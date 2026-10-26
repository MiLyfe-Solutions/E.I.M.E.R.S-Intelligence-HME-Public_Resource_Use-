import V185TrunkScan23Chunk0941

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5575620 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_5575620 : Nat := 118140960795 + 5575620 * 2 ^ 59
def prefixEnd_5575620 : Nat := 4983230072969 + 3 ^ 40 * 5575620 * 2
def baseEnd_5575620 : Nat := 2862973006821580594808197

theorem tailTrace_5575620 : CollatzResearch.WordTrace tailWord_5575620 prefixEnd_5575620 2862973006821580594808197 := by
  unfold tailWord_5575620
  simp only [CollatzResearch.WordTrace]
  refine ⟨101679784030244227464702157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135573045373658969952936209 101679784030244227464702157)
  ·
    refine ⟨38129919011341585299263309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101679784030244227464702157 38129919011341585299263309)
    ·
      refine ⟨14298719629253094487223741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38129919011341585299263309 14298719629253094487223741)
      ·
        refine ⟨5362019860969910432708903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14298719629253094487223741 5362019860969910432708903)
        ·
          refine ⟨8043029791454865649063355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5362019860969910432708903 8043029791454865649063355)
          ·
            refine ⟨12064544687182298473595033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8043029791454865649063355 12064544687182298473595033)
            ·
              refine ⟨9048408515386723855196275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12064544687182298473595033 9048408515386723855196275)
              ·
                refine ⟨13572612773080085782794413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9048408515386723855196275 13572612773080085782794413)
                ·
                  refine ⟨5089729789905032168547905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13572612773080085782794413 5089729789905032168547905)
                  ·
                    refine ⟨3817297342428774126410929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5089729789905032168547905 3817297342428774126410929)
                    ·
                      refine ⟨2862973006821580594808197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817297342428774126410929 2862973006821580594808197)
                      ·
                        rfl

theorem cell23_5575620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_5575620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575620 prefixEnd_5575620 := by exact prefixLift 5575620
  have htrace : WordTrace (prefixWord ++ tailWord_5575620) baseStart_5575620 baseEnd_5575620 := by
    simpa [prefixWord, tailWord_5575620, baseEnd_5575620] using wordTrace_append hprefix tailTrace_5575620
  have hstable : (prefixWord ++ tailWord_5575620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575620).length < 2 ^ (prefixWord ++ tailWord_5575620).sum := by decide
  have hdescent : baseEnd_5575620 < baseStart_5575620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575636 : List Nat := [2, 4, 1, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_5575636 : Nat := 118140960795 + 5575636 * 2 ^ 59
def prefixEnd_5575636 : Nat := 4983230072969 + 3 ^ 40 * 5575636 * 2
def baseEnd_5575636 : Nat := 2862981222512052532208123

theorem tailTrace_5575636 : CollatzResearch.WordTrace tailWord_5575636 prefixEnd_5575636 2862981222512052532208123 := by
  unfold tailWord_5575636
  simp only [CollatzResearch.WordTrace]
  refine ⟨101680075814215244830993381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135573434418953659774657841 101680075814215244830993381)
  ·
    refine ⟨19065014215165358405811259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101680075814215244830993381 19065014215165358405811259)
    ·
      refine ⟨28597521322748037608716889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19065014215165358405811259 28597521322748037608716889)
      ·
        refine ⟨21448140992061028206537667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28597521322748037608716889 21448140992061028206537667)
        ·
          refine ⟨32172211488091542309806501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21448140992061028206537667 32172211488091542309806501)
          ·
            refine ⟨6032289654017164183088719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32172211488091542309806501 6032289654017164183088719)
            ·
              refine ⟨9048434481025746274633079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032289654017164183088719 9048434481025746274633079)
              ·
                refine ⟨13572651721538619411949619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9048434481025746274633079 13572651721538619411949619)
                ·
                  refine ⟨20358977582307929117924429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13572651721538619411949619 20358977582307929117924429)
                  ·
                    refine ⟨7634616593365473419221661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20358977582307929117924429 7634616593365473419221661)
                    ·
                      refine ⟨2862981222512052532208123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7634616593365473419221661 2862981222512052532208123)
                      ·
                        rfl

theorem cell23_5575636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_5575636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575636 prefixEnd_5575636 := by exact prefixLift 5575636
  have htrace : WordTrace (prefixWord ++ tailWord_5575636) baseStart_5575636 baseEnd_5575636 := by
    simpa [prefixWord, tailWord_5575636, baseEnd_5575636] using wordTrace_append hprefix tailTrace_5575636
  have hstable : (prefixWord ++ tailWord_5575636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575636).length < 2 ^ (prefixWord ++ tailWord_5575636).sum := by decide
  have hdescent : baseEnd_5575636 < baseStart_5575636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575675 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 9]
def baseStart_5575675 : Nat := 118140960795 + 5575675 * 2 ^ 59
def prefixEnd_5575675 : Nat := 4983230072969 + 3 ^ 40 * 5575675 * 2
def baseEnd_5575675 : Nat := 2863001248257577879620443

theorem tailTrace_5575675 : CollatzResearch.WordTrace tailWord_5575675 prefixEnd_5575675 2863001248257577879620443 := by
  unfold tailWord_5575675
  simp only [CollatzResearch.WordTrace]
  refine ⟨203361574075289199322656479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135574382716859466215104319 203361574075289199322656479)
  ·
    refine ⟨305042361112933798983984719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203361574075289199322656479 305042361112933798983984719)
    ·
      refine ⟨457563541669400698475977079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305042361112933798983984719 457563541669400698475977079)
      ·
        refine ⟨686345312504101047713965619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457563541669400698475977079 686345312504101047713965619)
        ·
          refine ⟨1029517968756151571570948429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686345312504101047713965619 1029517968756151571570948429)
          ·
            refine ⟨386069238283556839339105661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1029517968756151571570948429 386069238283556839339105661)
            ·
              refine ⟨144775964356333814752164623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386069238283556839339105661 144775964356333814752164623)
              ·
                refine ⟨217163946534500722128246935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144775964356333814752164623 217163946534500722128246935)
                ·
                  refine ⟨325745919801751083192370403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217163946534500722128246935 325745919801751083192370403)
                  ·
                    refine ⟨488618879702626624788555605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 325745919801751083192370403 488618879702626624788555605)
                    ·
                      refine ⟨2863001248257577879620443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 488618879702626624788555605 2863001248257577879620443)
                      ·
                        rfl

theorem cell23_5575675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_5575675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575675 prefixEnd_5575675 := by exact prefixLift 5575675
  have htrace : WordTrace (prefixWord ++ tailWord_5575675) baseStart_5575675 baseEnd_5575675 := by
    simpa [prefixWord, tailWord_5575675, baseEnd_5575675] using wordTrace_append hprefix tailTrace_5575675
  have hstable : (prefixWord ++ tailWord_5575675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575675).length < 2 ^ (prefixWord ++ tailWord_5575675).sum := by decide
  have hdescent : baseEnd_5575675 < baseStart_5575675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575676 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 4, 2, 2]
def baseStart_5575676 : Nat := 118140960795 + 5575676 * 2 ^ 59
def prefixEnd_5575676 : Nat := 4983230072969 + 3 ^ 40 * 5575676 * 2
def baseEnd_5575676 : Nat := 2863001761738232375707939

theorem tailTrace_5575676 : CollatzResearch.WordTrace tailWord_5575676 prefixEnd_5575676 2863001761738232375707939 := by
  unfold tailWord_5575676
  simp only [CollatzResearch.WordTrace]
  refine ⟨101680805274142788246721441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135574407032190384328961921 101680805274142788246721441)
  ·
    refine ⟨76260603955607091185041081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101680805274142788246721441 76260603955607091185041081)
    ·
      refine ⟨57195452966705318388780811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76260603955607091185041081 57195452966705318388780811)
      ·
        refine ⟨85793179450057977583171217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57195452966705318388780811 85793179450057977583171217)
        ·
          refine ⟨64344884587543483187378413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85793179450057977583171217 64344884587543483187378413)
          ·
            refine ⟨24129331720328806195266905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64344884587543483187378413 24129331720328806195266905)
            ·
              refine ⟨18096998790246604646450179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24129331720328806195266905 18096998790246604646450179)
              ·
                refine ⟨27145498185369906969675269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18096998790246604646450179 27145498185369906969675269)
                ·
                  refine ⟨5089780909756857556814113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27145498185369906969675269 5089780909756857556814113)
                  ·
                    refine ⟨3817335682317643167610585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5089780909756857556814113 3817335682317643167610585)
                    ·
                      refine ⟨2863001761738232375707939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817335682317643167610585 2863001761738232375707939)
                      ·
                        rfl

theorem cell23_5575676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_5575676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575676 prefixEnd_5575676 := by exact prefixLift 5575676
  have htrace : WordTrace (prefixWord ++ tailWord_5575676) baseStart_5575676 baseEnd_5575676 := by
    simpa [prefixWord, tailWord_5575676, baseEnd_5575676] using wordTrace_append hprefix tailTrace_5575676
  have hstable : (prefixWord ++ tailWord_5575676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575676).length < 2 ^ (prefixWord ++ tailWord_5575676).sum := by decide
  have hdescent : baseEnd_5575676 < baseStart_5575676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575749 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 1, 6, 2]
def baseStart_5575749 : Nat := 118140960795 + 5575749 * 2 ^ 59
def prefixEnd_5575749 : Nat := 4983230072969 + 3 ^ 40 * 5575749 * 2
def baseEnd_5575749 : Nat := 2863039245826010590095103

theorem tailTrace_5575749 : CollatzResearch.WordTrace tailWord_5575749 prefixEnd_5575749 2863039245826010590095103 := by
  unfold tailWord_5575749
  simp only [CollatzResearch.WordTrace]
  refine ⟨203364273077021109960850301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135576182051347406640566867 203364273077021109960850301)
  ·
    refine ⟨76261602403882916235318863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203364273077021109960850301 76261602403882916235318863)
    ·
      refine ⟨114392403605824374352978295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76261602403882916235318863 114392403605824374352978295)
      ·
        refine ⟨171588605408736561529467443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114392403605824374352978295 171588605408736561529467443)
        ·
          refine ⟨257382908113104842294201165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171588605408736561529467443 257382908113104842294201165)
          ·
            refine ⟨96518590542414315860325437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257382908113104842294201165 96518590542414315860325437)
            ·
              refine ⟨36194471453405368447622039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96518590542414315860325437 36194471453405368447622039)
              ·
                refine ⟨54291707180108052671433059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36194471453405368447622039 54291707180108052671433059)
                ·
                  refine ⟨81437560770162079007149589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54291707180108052671433059 81437560770162079007149589)
                  ·
                    refine ⟨3817385661101347453460137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81437560770162079007149589 3817385661101347453460137)
                    ·
                      refine ⟨2863039245826010590095103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817385661101347453460137 2863039245826010590095103)
                      ·
                        rfl

theorem cell23_5575749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 1, 6, 2].length) (baseStart_5575749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575749 prefixEnd_5575749 := by exact prefixLift 5575749
  have htrace : WordTrace (prefixWord ++ tailWord_5575749) baseStart_5575749 baseEnd_5575749 := by
    simpa [prefixWord, tailWord_5575749, baseEnd_5575749] using wordTrace_append hprefix tailTrace_5575749
  have hstable : (prefixWord ++ tailWord_5575749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575749).length < 2 ^ (prefixWord ++ tailWord_5575749).sum := by decide
  have hdescent : baseEnd_5575749 < baseStart_5575749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575769 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 2, 2, 3]
def baseStart_5575769 : Nat := 118140960795 + 5575769 * 2 ^ 59
def prefixEnd_5575769 : Nat := 4983230072969 + 3 ^ 40 * 5575769 * 2
def baseEnd_5575769 : Nat := 2863049515439100511845011

theorem tailTrace_5575769 : CollatzResearch.WordTrace tailWord_5575769 prefixEnd_5575769 2863049515439100511845011 := by
  unfold tailWord_5575769
  simp only [CollatzResearch.WordTrace]
  refine ⟨203365002536948653376578361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135576668357965768917718907 203365002536948653376578361)
  ·
    refine ⟨152523751902711490032433771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203365002536948653376578361 152523751902711490032433771)
    ·
      refine ⟨228785627854067235048650657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152523751902711490032433771 228785627854067235048650657)
      ·
        refine ⟨171589220890550426286487993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228785627854067235048650657 171589220890550426286487993)
        ·
          refine ⟨128691915667912819714865995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171589220890550426286487993 128691915667912819714865995)
          ·
            refine ⟨193037873501869229572298993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128691915667912819714865995 193037873501869229572298993)
            ·
              refine ⟨144778405126401922179224245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193037873501869229572298993 144778405126401922179224245)
              ·
                refine ⟨13572975480600180204302273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144778405126401922179224245 13572975480600180204302273)
                ·
                  refine ⟨10179731610450135153226705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13572975480600180204302273 10179731610450135153226705)
                  ·
                    refine ⟨7634798707837601364920029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10179731610450135153226705 7634798707837601364920029)
                    ·
                      refine ⟨2863049515439100511845011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7634798707837601364920029 2863049515439100511845011)
                      ·
                        rfl

theorem cell23_5575769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_5575769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575769 prefixEnd_5575769 := by exact prefixLift 5575769
  have htrace : WordTrace (prefixWord ++ tailWord_5575769) baseStart_5575769 baseEnd_5575769 := by
    simpa [prefixWord, tailWord_5575769, baseEnd_5575769] using wordTrace_append hprefix tailTrace_5575769
  have hstable : (prefixWord ++ tailWord_5575769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575769).length < 2 ^ (prefixWord ++ tailWord_5575769).sum := by decide
  have hdescent : baseEnd_5575769 < baseStart_5575769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575789 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 8]
def baseStart_5575789 : Nat := 118140960795 + 5575789 * 2 ^ 59
def prefixEnd_5575789 : Nat := 4983230072969 + 3 ^ 40 * 5575789 * 2
def baseEnd_5575789 : Nat := 318117753894687825954991

theorem tailTrace_5575789 : CollatzResearch.WordTrace tailWord_5575789 prefixEnd_5575789 318117753894687825954991 := by
  unfold tailWord_5575789
  simp only [CollatzResearch.WordTrace]
  refine ⟨203365731996876196792306421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135577154664584131194870947 203365731996876196792306421)
  ·
    refine ⟨19065537374707143449278727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203365731996876196792306421 19065537374707143449278727)
    ·
      refine ⟨28598306062060715173918091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19065537374707143449278727 28598306062060715173918091)
      ·
        refine ⟨42897459093091072760877137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28598306062060715173918091 42897459093091072760877137)
        ·
          refine ⟨32173094319818304570657853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42897459093091072760877137 32173094319818304570657853)
          ·
            refine ⟨12064910369931864213996695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32173094319818304570657853 12064910369931864213996695)
            ·
              refine ⟨18097365554897796320995043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12064910369931864213996695 18097365554897796320995043)
              ·
                refine ⟨27146048332346694481492565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18097365554897796320995043 27146048332346694481492565)
                ·
                  refine ⟨318117753894687825954991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27146048332346694481492565 318117753894687825954991)
                  ·
                    rfl

theorem cell23_5575789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_5575789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575789 prefixEnd_5575789 := by exact prefixLift 5575789
  have htrace : WordTrace (prefixWord ++ tailWord_5575789) baseStart_5575789 baseEnd_5575789 := by
    simpa [prefixWord, tailWord_5575789, baseEnd_5575789] using wordTrace_append hprefix tailTrace_5575789
  have hstable : (prefixWord ++ tailWord_5575789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575789).length < 2 ^ (prefixWord ++ tailWord_5575789).sum := by decide
  have hdescent : baseEnd_5575789 < baseStart_5575789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575792 : List Nat := [2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_5575792 : Nat := 118140960795 + 5575792 * 2 ^ 59
def prefixEnd_5575792 : Nat := 4983230072969 + 3 ^ 40 * 5575792 * 2
def baseEnd_5575792 : Nat := 2863061325494153921857405

theorem tailTrace_5575792 : CollatzResearch.WordTrace tailWord_5575792 prefixEnd_5575792 2863061325494153921857405 := by
  unfold tailWord_5575792
  simp only [CollatzResearch.WordTrace]
  refine ⟨101682920707932664152332815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135577227610576885536443753 101682920707932664152332815)
  ·
    refine ⟨152524381061898996228499223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101682920707932664152332815 152524381061898996228499223)
    ·
      refine ⟨228786571592848494342748835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152524381061898996228499223 228786571592848494342748835)
      ·
        refine ⟨343179857389272741514123253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228786571592848494342748835 343179857389272741514123253)
        ·
          refine ⟨32173111630244319516949055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 343179857389272741514123253 32173111630244319516949055)
          ·
            refine ⟨48259667445366479275423583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32173111630244319516949055 48259667445366479275423583)
            ·
              refine ⟨72389501168049718913135375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48259667445366479275423583 72389501168049718913135375)
              ·
                refine ⟨108584251752074578369703063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72389501168049718913135375 108584251752074578369703063)
                ·
                  refine ⟨162876377628111867554554595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108584251752074578369703063 162876377628111867554554595)
                  ·
                    refine ⟨244314566442167801331831893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162876377628111867554554595 244314566442167801331831893)
                    ·
                      refine ⟨2863061325494153921857405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 244314566442167801331831893 2863061325494153921857405)
                      ·
                        rfl

theorem cell23_5575792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_5575792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575792 prefixEnd_5575792 := by exact prefixLift 5575792
  have htrace : WordTrace (prefixWord ++ tailWord_5575792) baseStart_5575792 baseEnd_5575792 := by
    simpa [prefixWord, tailWord_5575792, baseEnd_5575792] using wordTrace_append hprefix tailTrace_5575792
  have hstable : (prefixWord ++ tailWord_5575792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575792).length < 2 ^ (prefixWord ++ tailWord_5575792).sum := by decide
  have hdescent : baseEnd_5575792 < baseStart_5575792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575836 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 1, 5]
def baseStart_5575836 : Nat := 118140960795 + 5575836 * 2 ^ 59
def prefixEnd_5575836 : Nat := 4983230072969 + 3 ^ 40 * 5575836 * 2
def baseEnd_5575836 : Nat := 954361306214317249902401

theorem tailTrace_5575836 : CollatzResearch.WordTrace tailWord_5575836 prefixEnd_5575836 954361306214317249902401 := by
  unfold tailWord_5575836
  simp only [CollatzResearch.WordTrace]
  refine ⟨101683723113852961909633681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135578297485137282546178241 101683723113852961909633681)
  ·
    refine ⟨76262792335389721432225261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101683723113852961909633681 76262792335389721432225261)
    ·
      refine ⟨28598547125771145537084473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76262792335389721432225261 28598547125771145537084473)
      ·
        refine ⟨21448910344328359152813355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28598547125771145537084473 21448910344328359152813355)
        ·
          refine ⟨32173365516492538729220033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21448910344328359152813355 32173365516492538729220033)
          ·
            refine ⟨24130024137369404046915025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32173365516492538729220033 24130024137369404046915025)
            ·
              refine ⟨18097518103027053035186269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24130024137369404046915025 18097518103027053035186269)
              ·
                refine ⟨6786569288635144888194851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18097518103027053035186269 6786569288635144888194851)
                ·
                  refine ⟨10179853932952717332292277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6786569288635144888194851 10179853932952717332292277)
                  ·
                    refine ⟨954361306214317249902401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10179853932952717332292277 954361306214317249902401)
                    ·
                      rfl

theorem cell23_5575836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_5575836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575836 prefixEnd_5575836 := by exact prefixLift 5575836
  have htrace : WordTrace (prefixWord ++ tailWord_5575836) baseStart_5575836 baseEnd_5575836 := by
    simpa [prefixWord, tailWord_5575836, baseEnd_5575836] using wordTrace_append hprefix tailTrace_5575836
  have hstable : (prefixWord ++ tailWord_5575836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575836).length < 2 ^ (prefixWord ++ tailWord_5575836).sum := by decide
  have hdescent : baseEnd_5575836 < baseStart_5575836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575850 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5575850 : Nat := 118140960795 + 5575850 * 2 ^ 59
def prefixEnd_5575850 : Nat := 4983230072969 + 3 ^ 40 * 5575850 * 2
def baseEnd_5575850 : Nat := 2863091107372114694932139

theorem tailTrace_5575850 : CollatzResearch.WordTrace tailWord_5575850 prefixEnd_5575850 2863091107372114694932139 := by
  unfold tailWord_5575850
  simp only [CollatzResearch.WordTrace]
  refine ⟨50841989212413801052569251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135578637899770136140184669 50841989212413801052569251)
  ·
    refine ⟨76262983818620701578853877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50841989212413801052569251 76262983818620701578853877)
    ·
      refine ⟨7149654732995690773017551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76262983818620701578853877 7149654732995690773017551)
      ·
        refine ⟨10724482099493536159526327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7149654732995690773017551 10724482099493536159526327)
        ·
          refine ⟨16086723149240304239289491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10724482099493536159526327 16086723149240304239289491)
          ·
            refine ⟨24130084723860456358934237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16086723149240304239289491 24130084723860456358934237)
            ·
              refine ⟨9048781771447671134600339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24130084723860456358934237 9048781771447671134600339)
              ·
                refine ⟨13573172657171506701900509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9048781771447671134600339 13573172657171506701900509)
                ·
                  refine ⟨5089939746439315013212691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13573172657171506701900509 5089939746439315013212691)
                  ·
                    refine ⟨7634909619658972519819037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5089939746439315013212691 7634909619658972519819037)
                    ·
                      refine ⟨2863091107372114694932139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7634909619658972519819037 2863091107372114694932139)
                      ·
                        rfl

theorem cell23_5575850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5575850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575850 prefixEnd_5575850 := by exact prefixLift 5575850
  have htrace : WordTrace (prefixWord ++ tailWord_5575850) baseStart_5575850 baseEnd_5575850 := by
    simpa [prefixWord, tailWord_5575850, baseEnd_5575850] using wordTrace_append hprefix tailTrace_5575850
  have hstable : (prefixWord ++ tailWord_5575850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575850).length < 2 ^ (prefixWord ++ tailWord_5575850).sum := by decide
  have hdescent : baseEnd_5575850 < baseStart_5575850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575859 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 5]
def baseStart_5575859 : Nat := 118140960795 + 5575859 * 2 ^ 59
def prefixEnd_5575859 : Nat := 4983230072969 + 3 ^ 40 * 5575859 * 2
def baseEnd_5575859 : Nat := 2863095728698005159719597

theorem tailTrace_5575859 : CollatzResearch.WordTrace tailWord_5575859 prefixEnd_5575859 2863095728698005159719597 := by
  unfold tailWord_5575859
  simp only [CollatzResearch.WordTrace]
  refine ⟨203368285106622598747354631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135578856737748399164903087 203368285106622598747354631)
  ·
    refine ⟨305052427659933898121031947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203368285106622598747354631 305052427659933898121031947)
    ·
      refine ⟨457578641489900847181547921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305052427659933898121031947 457578641489900847181547921)
      ·
        refine ⟨343183981117425635386160941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457578641489900847181547921 343183981117425635386160941)
        ·
          refine ⟨128693992919034613269810353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343183981117425635386160941 128693992919034613269810353)
          ·
            refine ⟨96520494689275959952357765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128693992919034613269810353 96520494689275959952357765)
            ·
              refine ⟨18097592754239242491067081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96520494689275959952357765 18097592754239242491067081)
              ·
                refine ⟨13573194565679431868300311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18097592754239242491067081 13573194565679431868300311)
                ·
                  refine ⟨20359791848519147802450467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13573194565679431868300311 20359791848519147802450467)
                  ·
                    refine ⟨30539687772778721703675701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20359791848519147802450467 30539687772778721703675701)
                    ·
                      refine ⟨2863095728698005159719597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30539687772778721703675701 2863095728698005159719597)
                      ·
                        rfl

theorem cell23_5575859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_5575859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575859 prefixEnd_5575859 := by exact prefixLift 5575859
  have htrace : WordTrace (prefixWord ++ tailWord_5575859) baseStart_5575859 baseEnd_5575859 := by
    simpa [prefixWord, tailWord_5575859, baseEnd_5575859] using wordTrace_append hprefix tailTrace_5575859
  have hstable : (prefixWord ++ tailWord_5575859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575859).length < 2 ^ (prefixWord ++ tailWord_5575859).sum := by decide
  have hdescent : baseEnd_5575859 < baseStart_5575859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575869 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_5575869 : Nat := 118140960795 + 5575869 * 2 ^ 59
def prefixEnd_5575869 : Nat := 4983230072969 + 3 ^ 40 * 5575869 * 2
def baseEnd_5575869 : Nat := 2863100863504550120594551

theorem tailTrace_5575869 : CollatzResearch.WordTrace tailWord_5575869 prefixEnd_5575869 2863100863504550120594551 := by
  unfold tailWord_5575869
  simp only [CollatzResearch.WordTrace]
  refine ⟨203368649836586370455218661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135579099891057580303479107 203368649836586370455218661)
  ·
    refine ⟨38131621844359944460353499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203368649836586370455218661 38131621844359944460353499)
    ·
      refine ⟨57197432766539916690530249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38131621844359944460353499 57197432766539916690530249)
      ·
        refine ⟨42898074574904937517897687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57197432766539916690530249 42898074574904937517897687)
        ·
          refine ⟨64347111862357406276846531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42898074574904937517897687 64347111862357406276846531)
          ·
            refine ⟨96520667793536109415269797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64347111862357406276846531 96520667793536109415269797)
            ·
              refine ⟨18097625211288020515363087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96520667793536109415269797 18097625211288020515363087)
              ·
                refine ⟨27146437816932030773044631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18097625211288020515363087 27146437816932030773044631)
                ·
                  refine ⟨40719656725398046159566947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27146437816932030773044631 40719656725398046159566947)
                  ·
                    refine ⟨61079485088097069239350421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40719656725398046159566947 61079485088097069239350421)
                    ·
                      refine ⟨2863100863504550120594551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61079485088097069239350421 2863100863504550120594551)
                      ·
                        rfl

theorem cell23_5575869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_5575869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575869 prefixEnd_5575869 := by exact prefixLift 5575869
  have htrace : WordTrace (prefixWord ++ tailWord_5575869) baseStart_5575869 baseEnd_5575869 := by
    simpa [prefixWord, tailWord_5575869, baseEnd_5575869] using wordTrace_append hprefix tailTrace_5575869
  have hstable : (prefixWord ++ tailWord_5575869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575869).length < 2 ^ (prefixWord ++ tailWord_5575869).sum := by decide
  have hdescent : baseEnd_5575869 < baseStart_5575869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575873 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5575873 : Nat := 118140960795 + 5575873 * 2 ^ 59
def prefixEnd_5575873 : Nat := 4983230072969 + 3 ^ 40 * 5575873 * 2
def baseEnd_5575873 : Nat := 2863102917427168104944533

theorem tailTrace_5575873 : CollatzResearch.WordTrace tailWord_5575873 prefixEnd_5575873 2863102917427168104944533 := by
  unfold tailWord_5575873
  simp only [CollatzResearch.WordTrace]
  refine ⟨203368795728571879138364273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135579197152381252758909515 203368795728571879138364273)
  ·
    refine ⟨152526596796428909353773205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203368795728571879138364273 152526596796428909353773205)
    ·
      refine ⟨7149684224832605125958119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 152526596796428909353773205 7149684224832605125958119)
      ·
        refine ⟨10724526337248907688937179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7149684224832605125958119 10724526337248907688937179)
        ·
          refine ⟨16086789505873361533405769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10724526337248907688937179 16086789505873361533405769)
          ·
            refine ⟨12065092129405021150054327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16086789505873361533405769 12065092129405021150054327)
            ·
              refine ⟨18097638194107531725081491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12065092129405021150054327 18097638194107531725081491)
              ·
                refine ⟨27146457291161297587622237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18097638194107531725081491 27146457291161297587622237)
                ·
                  refine ⟨10179921484185486595358339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27146457291161297587622237 10179921484185486595358339)
                  ·
                    refine ⟨15269882226278229893037509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10179921484185486595358339 15269882226278229893037509)
                    ·
                      refine ⟨2863102917427168104944533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15269882226278229893037509 2863102917427168104944533)
                      ·
                        rfl

theorem cell23_5575873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5575873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575873 prefixEnd_5575873 := by exact prefixLift 5575873
  have htrace : WordTrace (prefixWord ++ tailWord_5575873) baseStart_5575873 baseEnd_5575873 := by
    simpa [prefixWord, tailWord_5575873, baseEnd_5575873] using wordTrace_append hprefix tailTrace_5575873
  have hstable : (prefixWord ++ tailWord_5575873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575873).length < 2 ^ (prefixWord ++ tailWord_5575873).sum := by decide
  have hdescent : baseEnd_5575873 < baseStart_5575873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575893 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_5575893 : Nat := 118140960795 + 5575893 * 2 ^ 59
def prefixEnd_5575893 : Nat := 4983230072969 + 3 ^ 40 * 5575893 * 2
def baseEnd_5575893 : Nat := 2863113187040258026694441

theorem tailTrace_5575893 : CollatzResearch.WordTrace tailWord_5575893 prefixEnd_5575893 2863113187040258026694441 := by
  unfold tailWord_5575893
  simp only [CollatzResearch.WordTrace]
  refine ⟨203369525188499422554092333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135579683458999615036061555 203369525188499422554092333)
  ·
    refine ⟨76263571945687283457784625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203369525188499422554092333 76263571945687283457784625)
    ·
      refine ⟨57197678959265462593338469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76263571945687283457784625 57197678959265462593338469)
      ·
        refine ⟨10724564804862274236250963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57197678959265462593338469 10724564804862274236250963)
        ·
          refine ⟨16086847207293411354376445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10724564804862274236250963 16086847207293411354376445)
          ·
            refine ⟨6032567702735029257891167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16086847207293411354376445 6032567702735029257891167)
            ·
              refine ⟨9048851554102543886836751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032567702735029257891167 9048851554102543886836751)
              ·
                refine ⟨13573277331153815830255127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9048851554102543886836751 13573277331153815830255127)
                ·
                  refine ⟨20359915996730723745382691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13573277331153815830255127 20359915996730723745382691)
                  ·
                    refine ⟨30539873995096085618074037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20359915996730723745382691 30539873995096085618074037)
                    ·
                      refine ⟨2863113187040258026694441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30539873995096085618074037 2863113187040258026694441)
                      ·
                        rfl

theorem cell23_5575893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_5575893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575893 prefixEnd_5575893 := by exact prefixLift 5575893
  have htrace : WordTrace (prefixWord ++ tailWord_5575893) baseStart_5575893 baseEnd_5575893 := by
    simpa [prefixWord, tailWord_5575893, baseEnd_5575893] using wordTrace_append hprefix tailTrace_5575893
  have hstable : (prefixWord ++ tailWord_5575893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575893).length < 2 ^ (prefixWord ++ tailWord_5575893).sum := by decide
  have hdescent : baseEnd_5575893 < baseStart_5575893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575901 : List Nat := [1, 4, 3, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_5575901 : Nat := 118140960795 + 5575901 * 2 ^ 59
def prefixEnd_5575901 : Nat := 4983230072969 + 3 ^ 40 * 5575901 * 2
def baseEnd_5575901 : Nat := 2863117294885493995394405

theorem tailTrace_5575901 : CollatzResearch.WordTrace tailWord_5575901 prefixEnd_5575901 2863117294885493995394405 := by
  unfold tailWord_5575901
  simp only [CollatzResearch.WordTrace]
  refine ⟨203369816972470439920383557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135579877981646959946922371 203369816972470439920383557)
  ·
    refine ⟨38131840682338207485071917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203369816972470439920383557 38131840682338207485071917)
    ·
      refine ⟨14299440255876827806901969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38131840682338207485071917 14299440255876827806901969)
      ·
        refine ⟨10724580191907620855176477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14299440255876827806901969 10724580191907620855176477)
        ·
          refine ⟨4021717571965357820691179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10724580191907620855176477 4021717571965357820691179)
          ·
            refine ⟨6032576357948036731036769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021717571965357820691179 6032576357948036731036769)
            ·
              refine ⟨4524432268461027548277577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6032576357948036731036769 4524432268461027548277577)
              ·
                refine ⟨3393324201345770661208183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4524432268461027548277577 3393324201345770661208183)
                ·
                  refine ⟨5089986302018655991812275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393324201345770661208183 5089986302018655991812275)
                  ·
                    refine ⟨7634979453027983987718413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5089986302018655991812275 7634979453027983987718413)
                    ·
                      refine ⟨2863117294885493995394405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7634979453027983987718413 2863117294885493995394405)
                      ·
                        rfl

theorem cell23_5575901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_5575901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575901 prefixEnd_5575901 := by exact prefixLift 5575901
  have htrace : WordTrace (prefixWord ++ tailWord_5575901) baseStart_5575901 baseEnd_5575901 := by
    simpa [prefixWord, tailWord_5575901, baseEnd_5575901] using wordTrace_append hprefix tailTrace_5575901
  have hstable : (prefixWord ++ tailWord_5575901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575901).length < 2 ^ (prefixWord ++ tailWord_5575901).sum := by decide
  have hdescent : baseEnd_5575901 < baseStart_5575901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575923 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 2, 1, 3]
def baseStart_5575923 : Nat := 118140960795 + 5575923 * 2 ^ 59
def prefixEnd_5575923 : Nat := 4983230072969 + 3 ^ 40 * 5575923 * 2
def baseEnd_5575923 : Nat := 2863128591459892909319303

theorem tailTrace_5575923 : CollatzResearch.WordTrace tailWord_5575923 prefixEnd_5575923 2863128591459892909319303 := by
  unfold tailWord_5575923
  simp only [CollatzResearch.WordTrace]
  refine ⟨203370619378390737677684423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135580412918927158451789615 203370619378390737677684423)
  ·
    refine ⟨305055929067586106516526635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203370619378390737677684423 305055929067586106516526635)
    ·
      refine ⟨457583893601379159774789953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305055929067586106516526635 457583893601379159774789953)
      ·
        refine ⟨343187920201034369831092465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457583893601379159774789953 343187920201034369831092465)
        ·
          refine ⟨257390940150775777373319349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343187920201034369831092465 257390940150775777373319349)
          ·
            refine ⟨24130400639135229128748689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 257390940150775777373319349 24130400639135229128748689)
            ·
              refine ⟨18097800479351421846561517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24130400639135229128748689 18097800479351421846561517)
              ·
                refine ⟨6786675179756783192460569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18097800479351421846561517 6786675179756783192460569)
                ·
                  refine ⟨5090006384817587394345427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6786675179756783192460569 5090006384817587394345427)
                  ·
                    refine ⟨7635009577226381091518141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5090006384817587394345427 7635009577226381091518141)
                    ·
                      refine ⟨2863128591459892909319303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7635009577226381091518141 2863128591459892909319303)
                      ·
                        rfl

theorem cell23_5575923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 2, 1, 3].length) (baseStart_5575923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575923 prefixEnd_5575923 := by exact prefixLift 5575923
  have htrace : WordTrace (prefixWord ++ tailWord_5575923) baseStart_5575923 baseEnd_5575923 := by
    simpa [prefixWord, tailWord_5575923, baseEnd_5575923] using wordTrace_append hprefix tailTrace_5575923
  have hstable : (prefixWord ++ tailWord_5575923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575923).length < 2 ^ (prefixWord ++ tailWord_5575923).sum := by decide
  have hdescent : baseEnd_5575923 < baseStart_5575923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575929 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 4]
def baseStart_5575929 : Nat := 118140960795 + 5575929 * 2 ^ 59
def prefixEnd_5575929 : Nat := 4983230072969 + 3 ^ 40 * 5575929 * 2
def baseEnd_5575929 : Nat := 2863131672343819885844275

theorem tailTrace_5575929 : CollatzResearch.WordTrace tailWord_5575929 prefixEnd_5575929 2863131672343819885844275 := by
  unfold tailWord_5575929
  simp only [CollatzResearch.WordTrace]
  refine ⟨203370838216369000702402841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135580558810912667134935227 203370838216369000702402841)
  ·
    refine ⟨152528128662276750526802131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203370838216369000702402841 152528128662276750526802131)
    ·
      refine ⟨228792192993415125790203197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152528128662276750526802131 228792192993415125790203197)
      ·
        refine ⟨85797072372530672171326199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228792192993415125790203197 85797072372530672171326199)
        ·
          refine ⟨128695608558796008256989299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85797072372530672171326199 128695608558796008256989299)
          ·
            refine ⟨193043412838194012385483949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128695608558796008256989299 193043412838194012385483949)
            ·
              refine ⟨72391279814322754644556481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193043412838194012385483949 72391279814322754644556481)
              ·
                refine ⟨54293459860742065983417361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72391279814322754644556481 54293459860742065983417361)
                ·
                  refine ⟨40720094895556549487563021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54293459860742065983417361 40720094895556549487563021)
                  ·
                    refine ⟨15270035585833706057836133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40720094895556549487563021 15270035585833706057836133)
                    ·
                      refine ⟨2863131672343819885844275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15270035585833706057836133 2863131672343819885844275)
                      ·
                        rfl

theorem cell23_5575929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_5575929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575929 prefixEnd_5575929 := by exact prefixLift 5575929
  have htrace : WordTrace (prefixWord ++ tailWord_5575929) baseStart_5575929 baseEnd_5575929 := by
    simpa [prefixWord, tailWord_5575929, baseEnd_5575929] using wordTrace_append hprefix tailTrace_5575929
  have hstable : (prefixWord ++ tailWord_5575929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575929).length < 2 ^ (prefixWord ++ tailWord_5575929).sum := by decide
  have hdescent : baseEnd_5575929 < baseStart_5575929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575950 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2]
def baseStart_5575950 : Nat := 118140960795 + 5575950 * 2 ^ 59
def prefixEnd_5575950 : Nat := 4983230072969 + 3 ^ 40 * 5575950 * 2
def baseEnd_5575950 : Nat := 2863142455437564303681679

theorem tailTrace_5575950 : CollatzResearch.WordTrace tailWord_5575950 prefixEnd_5575950 2863142455437564303681679 := by
  unfold tailWord_5575950
  simp only [CollatzResearch.WordTrace]
  refine ⟨25421450518661615161114663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135581069432861947525944869 25421450518661615161114663)
  ·
    refine ⟨38132175777992422741671995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25421450518661615161114663 38132175777992422741671995)
    ·
      refine ⟨57198263666988634112507993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38132175777992422741671995 57198263666988634112507993)
      ·
        refine ⟨42898697750241475584380995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57198263666988634112507993 42898697750241475584380995)
        ·
          refine ⟨64348046625362213376571493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42898697750241475584380995 64348046625362213376571493)
          ·
            refine ⟨12065258742255415008107155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64348046625362213376571493 12065258742255415008107155)
            ·
              refine ⟨18097888113383122512160733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12065258742255415008107155 18097888113383122512160733)
              ·
                refine ⟨6786708042518670942060275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18097888113383122512160733 6786708042518670942060275)
                ·
                  refine ⟨10180062063778006413090413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6786708042518670942060275 10180062063778006413090413)
                  ·
                    refine ⟨3817523273916752404908905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10180062063778006413090413 3817523273916752404908905)
                    ·
                      refine ⟨2863142455437564303681679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817523273916752404908905 2863142455437564303681679)
                      ·
                        rfl

theorem cell23_5575950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_5575950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575950 prefixEnd_5575950 := by exact prefixLift 5575950
  have htrace : WordTrace (prefixWord ++ tailWord_5575950) baseStart_5575950 baseEnd_5575950 := by
    simpa [prefixWord, tailWord_5575950, baseEnd_5575950] using wordTrace_append hprefix tailTrace_5575950
  have hstable : (prefixWord ++ tailWord_5575950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575950).length < 2 ^ (prefixWord ++ tailWord_5575950).sum := by decide
  have hdescent : baseEnd_5575950 < baseStart_5575950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5575986 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 7]
def baseStart_5575986 : Nat := 118140960795 + 5575986 * 2 ^ 59
def prefixEnd_5575986 : Nat := 4983230072969 + 3 ^ 40 * 5575986 * 2
def baseEnd_5575986 : Nat := 318128993415680684759057

theorem tailTrace_5575986 : CollatzResearch.WordTrace tailWord_5575986 prefixEnd_5575986 318128993415680684759057 := by
  unfold tailWord_5575986
  simp only [CollatzResearch.WordTrace]
  refine ⟨50843229294290624859306953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135581944784774999624818541 50843229294290624859306953)
  ·
    refine ⟨38132421970717968644480215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50843229294290624859306953 38132421970717968644480215)
    ·
      refine ⟨57198632956076952966720323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38132421970717968644480215 57198632956076952966720323)
      ·
        refine ⟨85797949434115429450080485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57198632956076952966720323 85797949434115429450080485)
        ·
          refine ⟨16087115518896643021890091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85797949434115429450080485 16087115518896643021890091)
          ·
            refine ⟨24130673278344964532835137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16087115518896643021890091 24130673278344964532835137)
            ·
              refine ⟨18098004958758723399626353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24130673278344964532835137 18098004958758723399626353)
              ·
                refine ⟨13573503719069042549719765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18098004958758723399626353 13573503719069042549719765)
                ·
                  refine ⟨318128993415680684759057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13573503719069042549719765 318128993415680684759057)
                  ·
                    rfl

theorem cell23_5575986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_5575986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5575986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5575986 prefixEnd_5575986 := by exact prefixLift 5575986
  have htrace : WordTrace (prefixWord ++ tailWord_5575986) baseStart_5575986 baseEnd_5575986 := by
    simpa [prefixWord, tailWord_5575986, baseEnd_5575986] using wordTrace_append hprefix tailTrace_5575986
  have hstable : (prefixWord ++ tailWord_5575986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5575986).length < 2 ^ (prefixWord ++ tailWord_5575986).sum := by decide
  have hdescent : baseEnd_5575986 < baseStart_5575986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5575986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576016 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 2, 5]
def baseStart_5576016 : Nat := 118140960795 + 5576016 * 2 ^ 59
def prefixEnd_5576016 : Nat := 4983230072969 + 3 ^ 40 * 5576016 * 2
def baseEnd_5576016 : Nat := 954392115053587015152125

theorem tailTrace_5576016 : CollatzResearch.WordTrace tailWord_5576016 prefixEnd_5576016 954392115053587015152125 := by
  unfold tailWord_5576016
  simp only [CollatzResearch.WordTrace]
  refine ⟨101687005683526907280409951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135582674244702543040546601 101687005683526907280409951)
  ·
    refine ⟨152530508525290360920614927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101687005683526907280409951 152530508525290360920614927)
    ·
      refine ⟨228795762787935541380922391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152530508525290360920614927 228795762787935541380922391)
      ·
        refine ⟨343193644181903312071383587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228795762787935541380922391 343193644181903312071383587)
        ·
          refine ⟨514790466272854968107075381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343193644181903312071383587 514790466272854968107075381)
          ·
            refine ⟨48261606213080153260038317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 514790466272854968107075381 48261606213080153260038317)
            ·
              refine ⟨18098102329905057472514369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48261606213080153260038317 18098102329905057472514369)
              ·
                refine ⟨13573576747428793104385777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18098102329905057472514369 13573576747428793104385777)
                ·
                  refine ⟨10180182560571594828289333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13573576747428793104385777 10180182560571594828289333)
                  ·
                    refine ⟨954392115053587015152125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10180182560571594828289333 954392115053587015152125)
                    ·
                      rfl

theorem cell23_5576016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_5576016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576016 prefixEnd_5576016 := by exact prefixLift 5576016
  have htrace : WordTrace (prefixWord ++ tailWord_5576016) baseStart_5576016 baseEnd_5576016 := by
    simpa [prefixWord, tailWord_5576016, baseEnd_5576016] using wordTrace_append hprefix tailTrace_5576016
  have hstable : (prefixWord ++ tailWord_5576016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576016).length < 2 ^ (prefixWord ++ tailWord_5576016).sum := by decide
  have hdescent : baseEnd_5576016 < baseStart_5576016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576020 : List Nat := [2, 4, 1, 1, 2, 1, 5, 2, 5]
def baseStart_5576020 : Nat := 118140960795 + 5576020 * 2 ^ 59
def prefixEnd_5576020 : Nat := 4983230072969 + 3 ^ 40 * 5576020 * 2
def baseEnd_5576020 : Nat := 318130933231486558867373

theorem tailTrace_5576020 : CollatzResearch.WordTrace tailWord_5576020 prefixEnd_5576020 318130933231486558867373 := by
  unfold tailWord_5576020
  simp only [CollatzResearch.WordTrace]
  refine ⟨101687078629519661621982757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135582771506026215495977009 101687078629519661621982757)
  ·
    refine ⟨19066327243034936554121767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101687078629519661621982757 19066327243034936554121767)
    ·
      refine ⟨28599490864552404831182651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19066327243034936554121767 28599490864552404831182651)
      ·
        refine ⟨42899236296828607246773977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28599490864552404831182651 42899236296828607246773977)
        ·
          refine ⟨32174427222621455435080483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42899236296828607246773977 32174427222621455435080483)
          ·
            refine ⟨48261640833932183152620725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32174427222621455435080483 48261640833932183152620725)
            ·
              refine ⟨4524528828181142170558193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48261640833932183152620725 4524528828181142170558193)
              ·
                refine ⟨3393396621135856627918645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4524528828181142170558193 3393396621135856627918645)
                ·
                  refine ⟨318130933231486558867373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3393396621135856627918645 318130933231486558867373)
                  ·
                    rfl

theorem cell23_5576020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_5576020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576020 prefixEnd_5576020 := by exact prefixLift 5576020
  have htrace : WordTrace (prefixWord ++ tailWord_5576020) baseStart_5576020 baseEnd_5576020 := by
    simpa [prefixWord, tailWord_5576020, baseEnd_5576020] using wordTrace_append hprefix tailTrace_5576020
  have hstable : (prefixWord ++ tailWord_5576020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576020).length < 2 ^ (prefixWord ++ tailWord_5576020).sum := by decide
  have hdescent : baseEnd_5576020 < baseStart_5576020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576093 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 6]
def baseStart_5576093 : Nat := 118140960795 + 5576093 * 2 ^ 59
def prefixEnd_5576093 : Nat := 4983230072969 + 3 ^ 40 * 5576093 * 2
def baseEnd_5576093 : Nat := 318135098130128582688169

theorem tailTrace_5576093 : CollatzResearch.WordTrace tailWord_5576093 prefixEnd_5576093 318135098130128582688169 := by
  unfold tailWord_5576093
  simp only [CollatzResearch.WordTrace]
  refine ⟨203376819787774856711372933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135584546525183237807581955 203376819787774856711372933)
  ·
    refine ⟨38133153710207785633382425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203376819787774856711372933 38133153710207785633382425)
    ·
      refine ⟨28599865282655839225036819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38133153710207785633382425 28599865282655839225036819)
      ·
        refine ⟨42899797923983758837555229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28599865282655839225036819 42899797923983758837555229)
        ·
          refine ⟨16087424221493909564083211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42899797923983758837555229 16087424221493909564083211)
          ·
            refine ⟨24131136332240864346124817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16087424221493909564083211 24131136332240864346124817)
            ·
              refine ⟨18098352249180648259593613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24131136332240864346124817 18098352249180648259593613)
              ·
                refine ⟨6786882093442743097347605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18098352249180648259593613 6786882093442743097347605)
                ·
                  refine ⟨318135098130128582688169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6786882093442743097347605 318135098130128582688169)
                  ·
                    rfl

theorem cell23_5576093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_5576093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576093 prefixEnd_5576093 := by exact prefixLift 5576093
  have htrace : WordTrace (prefixWord ++ tailWord_5576093) baseStart_5576093 baseEnd_5576093 := by
    simpa [prefixWord, tailWord_5576093, baseEnd_5576093] using wordTrace_append hprefix tailTrace_5576093
  have hstable : (prefixWord ++ tailWord_5576093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576093).length < 2 ^ (prefixWord ++ tailWord_5576093).sum := by decide
  have hdescent : baseEnd_5576093 < baseStart_5576093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576104 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_5576104 : Nat := 118140960795 + 5576104 * 2 ^ 59
def prefixEnd_5576104 : Nat := 4983230072969 + 3 ^ 40 * 5576104 * 2
def baseEnd_5576104 : Nat := 2863221531458356701155971

theorem tailTrace_5576104 : CollatzResearch.WordTrace tailWord_5576104 prefixEnd_5576104 2863221531458356701155971 := by
  unfold tailWord_5576104
  simp only [CollatzResearch.WordTrace]
  refine ⟨101688610495367502795011683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135584813993823337060015577 101688610495367502795011683)
  ·
    refine ⟨152532915743051254192517525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101688610495367502795011683 152532915743051254192517525)
    ·
      refine ⟨7149980425455527540274259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 152532915743051254192517525 7149980425455527540274259)
      ·
        refine ⟨10724970638183291310411389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7149980425455527540274259 10724970638183291310411389)
        ·
          refine ⟨4021863989318734241404271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10724970638183291310411389 4021863989318734241404271)
          ·
            refine ⟨6032795983978101362106407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021863989318734241404271 6032795983978101362106407)
            ·
              refine ⟨9049193975967152043159611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032795983978101362106407 9049193975967152043159611)
              ·
                refine ⟨13573790963950728064739417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9049193975967152043159611 13573790963950728064739417)
                ·
                  refine ⟨10180343222963046048554563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13573790963950728064739417 10180343222963046048554563)
                  ·
                    refine ⟨15270514834444569072831845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10180343222963046048554563 15270514834444569072831845)
                    ·
                      refine ⟨2863221531458356701155971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15270514834444569072831845 2863221531458356701155971)
                      ·
                        rfl

theorem cell23_5576104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_5576104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576104 prefixEnd_5576104 := by exact prefixLift 5576104
  have htrace : WordTrace (prefixWord ++ tailWord_5576104) baseStart_5576104 baseEnd_5576104 := by
    simpa [prefixWord, tailWord_5576104, baseEnd_5576104] using wordTrace_append hprefix tailTrace_5576104
  have hstable : (prefixWord ++ tailWord_5576104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576104).length < 2 ^ (prefixWord ++ tailWord_5576104).sum := by decide
  have hdescent : baseEnd_5576104 < baseStart_5576104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576153 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 1, 6]
def baseStart_5576153 : Nat := 118140960795 + 5576153 * 2 ^ 59
def prefixEnd_5576153 : Nat := 4983230072969 + 3 ^ 40 * 5576153 * 2
def baseEnd_5576153 : Nat := 954415564003475669814415

theorem tailTrace_5576153 : CollatzResearch.WordTrace tailWord_5576153 prefixEnd_5576153 954415564003475669814415 := by
  unfold tailWord_5576153
  simp only [CollatzResearch.WordTrace]
  refine ⟨203379008167557486958557113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135586005445038324639038075 203379008167557486958557113)
  ·
    refine ⟨152534256125668115218917835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203379008167557486958557113 152534256125668115218917835)
    ·
      refine ⟨228801384188502172828376753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152534256125668115218917835 228801384188502172828376753)
      ·
        refine ⟨171601038141376629621282565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228801384188502172828376753 171601038141376629621282565)
        ·
          refine ⟨32175194651508118053990481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171601038141376629621282565 32175194651508118053990481)
          ·
            refine ⟨24131395988631088540492861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32175194651508118053990481 24131395988631088540492861)
            ·
              refine ⟨9049273495736658202684823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24131395988631088540492861 9049273495736658202684823)
              ·
                refine ⟨13573910243604987304027235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9049273495736658202684823 13573910243604987304027235)
                ·
                  refine ⟨20360865365407480956040853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13573910243604987304027235 20360865365407480956040853)
                  ·
                    refine ⟨954415564003475669814415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20360865365407480956040853 954415564003475669814415)
                    ·
                      rfl

theorem cell23_5576153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 6].length) (baseStart_5576153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576153 prefixEnd_5576153 := by exact prefixLift 5576153
  have htrace : WordTrace (prefixWord ++ tailWord_5576153) baseStart_5576153 baseEnd_5576153 := by
    simpa [prefixWord, tailWord_5576153, baseEnd_5576153] using wordTrace_append hprefix tailTrace_5576153
  have hstable : (prefixWord ++ tailWord_5576153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576153).length < 2 ^ (prefixWord ++ tailWord_5576153).sum := by decide
  have hdescent : baseEnd_5576153 < baseStart_5576153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576160 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 5, 2, 2]
def baseStart_5576160 : Nat := 118140960795 + 5576160 * 2 ^ 59
def prefixEnd_5576160 : Nat := 4983230072969 + 3 ^ 40 * 5576160 * 2
def baseEnd_5576160 : Nat := 2863250286375008482055713

theorem tailTrace_5576160 : CollatzResearch.WordTrace tailWord_5576160 prefixEnd_5576160 2863250286375008482055713 := by
  unfold tailWord_5576160
  simp only [CollatzResearch.WordTrace]
  refine ⟨101689631739266063577030967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135586175652354751436041289 101689631739266063577030967)
  ·
    refine ⟨152534447608899095365546451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101689631739266063577030967 152534447608899095365546451)
    ·
      refine ⟨228801671413348643048319677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152534447608899095365546451 228801671413348643048319677)
      ·
        refine ⟨85800626780005741143119879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228801671413348643048319677 85800626780005741143119879)
        ·
          refine ⟨128700940170008611714679819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85800626780005741143119879 128700940170008611714679819)
          ·
            refine ⟨193051410255012917572019729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128700940170008611714679819 193051410255012917572019729)
            ·
              refine ⟨144788557691259688179014797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193051410255012917572019729 144788557691259688179014797)
              ·
                refine ⟨54295709134222383067130549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144788557691259688179014797 54295709134222383067130549)
                ·
                  refine ⟨5090222731333348412543489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54295709134222383067130549 5090222731333348412543489)
                  ·
                    refine ⟨3817667048500011309407617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5090222731333348412543489 3817667048500011309407617)
                    ·
                      refine ⟨2863250286375008482055713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817667048500011309407617 2863250286375008482055713)
                      ·
                        rfl

theorem cell23_5576160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_5576160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576160 prefixEnd_5576160 := by exact prefixLift 5576160
  have htrace : WordTrace (prefixWord ++ tailWord_5576160) baseStart_5576160 baseEnd_5576160 := by
    simpa [prefixWord, tailWord_5576160, baseEnd_5576160] using wordTrace_append hprefix tailTrace_5576160
  have hstable : (prefixWord ++ tailWord_5576160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576160).length < 2 ^ (prefixWord ++ tailWord_5576160).sum := by decide
  have hdescent : baseEnd_5576160 < baseStart_5576160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576204 : List Nat := [2, 2, 1, 2, 5, 2, 2, 1, 2, 4]
def baseStart_5576204 : Nat := 118140960795 + 5576204 * 2 ^ 59
def prefixEnd_5576204 : Nat := 4983230072969 + 3 ^ 40 * 5576204 * 2
def baseEnd_5576204 : Nat := 954424293174602103301837

theorem tailTrace_5576204 : CollatzResearch.WordTrace tailWord_5576204 prefixEnd_5576204 954424293174602103301837 := by
  unfold tailWord_5576204
  simp only [CollatzResearch.WordTrace]
  refine ⟨101690434145186361334331833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135587245526915148445775777 101690434145186361334331833)
  ·
    refine ⟨76267825608889771000748875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101690434145186361334331833 76267825608889771000748875)
    ·
      refine ⟨114401738413334656501123313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76267825608889771000748875 114401738413334656501123313)
      ·
        refine ⟨85801303810000992375842485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114401738413334656501123313 85801303810000992375842485)
        ·
          refine ⟨8043872232187593035235233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85801303810000992375842485 8043872232187593035235233)
          ·
            refine ⟨6032904174140694776426425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8043872232187593035235233 6032904174140694776426425)
            ·
              refine ⟨4524678130605521082319819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6032904174140694776426425 4524678130605521082319819)
              ·
                refine ⟨6787017195908281623479729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4524678130605521082319819 6787017195908281623479729)
                ·
                  refine ⟨5090262896931211217609797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6787017195908281623479729 5090262896931211217609797)
                  ·
                    refine ⟨954424293174602103301837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5090262896931211217609797 954424293174602103301837)
                    ·
                      rfl

theorem cell23_5576204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_5576204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576204 prefixEnd_5576204 := by exact prefixLift 5576204
  have htrace : WordTrace (prefixWord ++ tailWord_5576204) baseStart_5576204 baseEnd_5576204 := by
    simpa [prefixWord, tailWord_5576204, baseEnd_5576204] using wordTrace_append hprefix tailTrace_5576204
  have hstable : (prefixWord ++ tailWord_5576204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576204).length < 2 ^ (prefixWord ++ tailWord_5576204).sum := by decide
  have hdescent : baseEnd_5576204 < baseStart_5576204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576250 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2]
def baseStart_5576250 : Nat := 118140960795 + 5576250 * 2 ^ 59
def prefixEnd_5576250 : Nat := 4983230072969 + 3 ^ 40 * 5576250 * 2
def baseEnd_5576250 : Nat := 2863296499633913129930299

theorem tailTrace_5576250 : CollatzResearch.WordTrace tailWord_5576250 prefixEnd_5576250 2863296499633913129930299 := by
  unfold tailWord_5576250
  simp only [CollatzResearch.WordTrace]
  refine ⟨50845636512051518131209551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135588364032137381683225469 50845636512051518131209551)
  ·
    refine ⟨76268454768077277196814327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50845636512051518131209551 76268454768077277196814327)
    ·
      refine ⟨114402682152115915795221491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76268454768077277196814327 114402682152115915795221491)
      ·
        refine ⟨171604023228173873692832237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114402682152115915795221491 171604023228173873692832237)
        ·
          refine ⟨64351508710565202634812089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171604023228173873692832237 64351508710565202634812089)
          ·
            refine ⟨48263631532923901976109067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64351508710565202634812089 48263631532923901976109067)
            ·
              refine ⟨72395447299385852964163601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48263631532923901976109067 72395447299385852964163601)
              ·
                refine ⟨54296585474539389723122701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72395447299385852964163601 54296585474539389723122701)
                ·
                  refine ⟨20361219552952271146171013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54296585474539389723122701 20361219552952271146171013)
                  ·
                    refine ⟨3817728666178550839907065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20361219552952271146171013 3817728666178550839907065)
                    ·
                      refine ⟨2863296499633913129930299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817728666178550839907065 2863296499633913129930299)
                      ·
                        rfl

theorem cell23_5576250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3, 4, 2].length) (baseStart_5576250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576250 prefixEnd_5576250 := by exact prefixLift 5576250
  have htrace : WordTrace (prefixWord ++ tailWord_5576250) baseStart_5576250 baseEnd_5576250 := by
    simpa [prefixWord, tailWord_5576250, baseEnd_5576250] using wordTrace_append hprefix tailTrace_5576250
  have hstable : (prefixWord ++ tailWord_5576250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576250).length < 2 ^ (prefixWord ++ tailWord_5576250).sum := by decide
  have hdescent : baseEnd_5576250 < baseStart_5576250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576273 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 7]
def baseStart_5576273 : Nat := 118140960795 + 5576273 * 2 ^ 59
def prefixEnd_5576273 : Nat := 4983230072969 + 3 ^ 40 * 5576273 * 2
def baseEnd_5576273 : Nat := 318145367743218504438077

theorem tailTrace_5576273 : CollatzResearch.WordTrace tailWord_5576273 prefixEnd_5576273 318145367743218504438077 := by
  unfold tailWord_5576273
  simp only [CollatzResearch.WordTrace]
  refine ⟨203383384927122747452925473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135588923284748498301950315 203383384927122747452925473)
  ·
    refine ⟨152537538695342060589694105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203383384927122747452925473 152537538695342060589694105)
    ·
      refine ⟨114403154021506545442270579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152537538695342060589694105 114403154021506545442270579)
      ·
        refine ⟨171604731032259818163405869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114403154021506545442270579 171604731032259818163405869)
        ·
          refine ⟨64351774137097431811277201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171604731032259818163405869 64351774137097431811277201)
          ·
            refine ⟨48263830602823073858457901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64351774137097431811277201 48263830602823073858457901)
            ·
              refine ⟨18098936476058652696921713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48263830602823073858457901 18098936476058652696921713)
              ·
                refine ⟨13574202357043989522691285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18098936476058652696921713 13574202357043989522691285)
                ·
                  refine ⟨318145367743218504438077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13574202357043989522691285 318145367743218504438077)
                  ·
                    rfl

theorem cell23_5576273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 7].length) (baseStart_5576273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576273 prefixEnd_5576273 := by exact prefixLift 5576273
  have htrace : WordTrace (prefixWord ++ tailWord_5576273) baseStart_5576273 baseEnd_5576273 := by
    simpa [prefixWord, tailWord_5576273, baseEnd_5576273] using wordTrace_append hprefix tailTrace_5576273
  have hstable : (prefixWord ++ tailWord_5576273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576273).length < 2 ^ (prefixWord ++ tailWord_5576273).sum := by decide
  have hdescent : baseEnd_5576273 < baseStart_5576273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576303 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 4, 5]
def baseStart_5576303 : Nat := 118140960795 + 5576303 * 2 ^ 59
def prefixEnd_5576303 : Nat := 4983230072969 + 3 ^ 40 * 5576303 * 2
def baseEnd_5576303 : Nat := 954441238036200474189185

theorem tailTrace_5576303 : CollatzResearch.WordTrace tailWord_5576303 prefixEnd_5576303 954441238036200474189185 := by
  unfold tailWord_5576303
  simp only [CollatzResearch.WordTrace]
  refine ⟨203384479117014062576517563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135589652744676041717678375 203384479117014062576517563)
  ·
    refine ⟨305076718675521093864776345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203384479117014062576517563 305076718675521093864776345)
    ·
      refine ⟨228807539006640820398582259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305076718675521093864776345 228807539006640820398582259)
      ·
        refine ⟨343211308509961230597873389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228807539006640820398582259 343211308509961230597873389)
        ·
          refine ⟨128704240691235461474202521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343211308509961230597873389 128704240691235461474202521)
          ·
            refine ⟨96528180518426596105651891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128704240691235461474202521 96528180518426596105651891)
            ·
              refine ⟨144792270777639894158477837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96528180518426596105651891 144792270777639894158477837)
              ·
                refine ⟨54297101541614960309429189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144792270777639894158477837 54297101541614960309429189)
                ·
                  refine ⟨10180706539052805058017973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54297101541614960309429189 10180706539052805058017973)
                  ·
                    refine ⟨954441238036200474189185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10180706539052805058017973 954441238036200474189185)
                    ·
                      rfl

theorem cell23_5576303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_5576303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576303 prefixEnd_5576303 := by exact prefixLift 5576303
  have htrace : WordTrace (prefixWord ++ tailWord_5576303) baseStart_5576303 baseEnd_5576303 := by
    simpa [prefixWord, tailWord_5576303, baseEnd_5576303] using wordTrace_append hprefix tailTrace_5576303
  have hstable : (prefixWord ++ tailWord_5576303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576303).length < 2 ^ (prefixWord ++ tailWord_5576303).sum := by decide
  have hdescent : baseEnd_5576303 < baseStart_5576303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576313 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_5576313 : Nat := 118140960795 + 5576313 * 2 ^ 59
def prefixEnd_5576313 : Nat := 4983230072969 + 3 ^ 40 * 5576313 * 2
def baseEnd_5576313 : Nat := 2863328848915146383442509

theorem tailTrace_5576313 : CollatzResearch.WordTrace tailWord_5576313 prefixEnd_5576313 2863328848915146383442509 := by
  unfold tailWord_5576313
  simp only [CollatzResearch.WordTrace]
  refine ⟨203384843846977834284381593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135589895897985222856254395 203384843846977834284381593)
  ·
    refine ⟨152538632885233375713286195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203384843846977834284381593 152538632885233375713286195)
    ·
      refine ⟨228807949327850063569929293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152538632885233375713286195 228807949327850063569929293)
      ·
        refine ⟨85802980997943773838723485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228807949327850063569929293 85802980997943773838723485)
        ·
          refine ⟨32176117874228915189521307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85802980997943773838723485 32176117874228915189521307)
          ·
            refine ⟨48264176811343372784281961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32176117874228915189521307 48264176811343372784281961)
            ·
              refine ⟨36198132608507529588211471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48264176811343372784281961 36198132608507529588211471)
              ·
                refine ⟨54297198912761294382317207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36198132608507529588211471 54297198912761294382317207)
                ·
                  refine ⟨81445798369141941573475811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54297198912761294382317207 81445798369141941573475811)
                  ·
                    refine ⟨122168697553712912360213717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81445798369141941573475811 122168697553712912360213717)
                    ·
                      refine ⟨2863328848915146383442509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122168697553712912360213717 2863328848915146383442509)
                      ·
                        rfl

theorem cell23_5576313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_5576313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576313 prefixEnd_5576313 := by exact prefixLift 5576313
  have htrace : WordTrace (prefixWord ++ tailWord_5576313) baseStart_5576313 baseEnd_5576313 := by
    simpa [prefixWord, tailWord_5576313, baseEnd_5576313] using wordTrace_append hprefix tailTrace_5576313
  have hstable : (prefixWord ++ tailWord_5576313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576313).length < 2 ^ (prefixWord ++ tailWord_5576313).sum := by decide
  have hdescent : baseEnd_5576313 < baseStart_5576313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576354 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_5576354 : Nat := 118140960795 + 5576354 * 2 ^ 59
def prefixEnd_5576354 : Nat := 4983230072969 + 3 ^ 40 * 5576354 * 2
def baseEnd_5576354 : Nat := 954449967207326907676607

theorem tailTrace_5576354 : CollatzResearch.WordTrace tailWord_5576354 prefixEnd_5576354 954449967207326907676607 := by
  unfold tailWord_5576354
  simp only [CollatzResearch.WordTrace]
  refine ⟨50846584809957324571656029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135590892826552865524416077 50846584809957324571656029)
  ·
    refine ⟨19067469303733996714371011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50846584809957324571656029 19067469303733996714371011)
    ·
      refine ⟨28601203955600995071556517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19067469303733996714371011 28601203955600995071556517)
      ·
        refine ⟨5362725741675186575916847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28601203955600995071556517 5362725741675186575916847)
        ·
          refine ⟨8044088612512779863875271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5362725741675186575916847 8044088612512779863875271)
          ·
            refine ⟨12066132918769169795812907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044088612512779863875271 12066132918769169795812907)
            ·
              refine ⟨18099199378153754693719361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12066132918769169795812907 18099199378153754693719361)
              ·
                refine ⟨13574399533615316020289521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18099199378153754693719361 13574399533615316020289521)
                ·
                  refine ⟨10180799650211487015217141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13574399533615316020289521 10180799650211487015217141)
                  ·
                    refine ⟨954449967207326907676607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10180799650211487015217141 954449967207326907676607)
                    ·
                      rfl

theorem cell23_5576354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_5576354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576354 prefixEnd_5576354 := by exact prefixLift 5576354
  have htrace : WordTrace (prefixWord ++ tailWord_5576354) baseStart_5576354 baseEnd_5576354 := by
    simpa [prefixWord, tailWord_5576354, baseEnd_5576354] using wordTrace_append hprefix tailTrace_5576354
  have hstable : (prefixWord ++ tailWord_5576354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576354).length < 2 ^ (prefixWord ++ tailWord_5576354).sum := by decide
  have hdescent : baseEnd_5576354 < baseStart_5576354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576394 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_5576394 : Nat := 118140960795 + 5576394 * 2 ^ 59
def prefixEnd_5576394 : Nat := 4983230072969 + 3 ^ 40 * 5576394 * 2
def baseEnd_5576394 : Nat := 2863370440848160566529637

theorem tailTrace_5576394 : CollatzResearch.WordTrace tailWord_5576394 prefixEnd_5576394 2863370440848160566529637 := by
  unfold tailWord_5576394
  simp only [CollatzResearch.WordTrace]
  refine ⟨50846949539921096279520059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135591865439789590078720157 50846949539921096279520059)
  ·
    refine ⟨76270424309881644419280089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50846949539921096279520059 76270424309881644419280089)
    ·
      refine ⟨57202818232411233314460067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76270424309881644419280089 57202818232411233314460067)
      ·
        refine ⟨85804227348616849971690101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57202818232411233314460067 85804227348616849971690101)
        ·
          refine ⟨8044146313932829684845947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85804227348616849971690101 8044146313932829684845947)
          ·
            refine ⟨12066219470899244527268921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044146313932829684845947 12066219470899244527268921)
            ·
              refine ⟨9049664603174433395451691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12066219470899244527268921 9049664603174433395451691)
              ·
                refine ⟨13574496904761650093177537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9049664603174433395451691 13574496904761650093177537)
                ·
                  refine ⟨10180872678571237569883153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13574496904761650093177537 10180872678571237569883153)
                  ·
                    refine ⟨7635654508928428177412365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10180872678571237569883153 7635654508928428177412365)
                    ·
                      refine ⟨2863370440848160566529637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7635654508928428177412365 2863370440848160566529637)
                      ·
                        rfl

theorem cell23_5576394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_5576394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576394 prefixEnd_5576394 := by exact prefixLift 5576394
  have htrace : WordTrace (prefixWord ++ tailWord_5576394) baseStart_5576394 baseEnd_5576394 := by
    simpa [prefixWord, tailWord_5576394, baseEnd_5576394] using wordTrace_append hprefix tailTrace_5576394
  have hstable : (prefixWord ++ tailWord_5576394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576394).length < 2 ^ (prefixWord ++ tailWord_5576394).sum := by decide
  have hdescent : baseEnd_5576394 < baseStart_5576394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576474 : List Nat := [3, 1, 1, 3, 2, 2, 3, 2, 2, 4]
def baseStart_5576474 : Nat := 118140960795 + 5576474 * 2 ^ 59
def prefixEnd_5576474 : Nat := 4983230072969 + 3 ^ 40 * 5576474 * 2
def baseEnd_5576474 : Nat := 954470506433506751176423

theorem tailTrace_5576474 : CollatzResearch.WordTrace tailWord_5576474 prefixEnd_5576474 954470506433506751176423 := by
  unfold tailWord_5576474
  simp only [CollatzResearch.WordTrace]
  refine ⟨50847678999848639695248119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135593810666263039187328317 50847678999848639695248119)
  ·
    refine ⟨76271518499772959542872179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50847678999848639695248119 76271518499772959542872179)
    ·
      refine ⟨114407277749659439314308269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76271518499772959542872179 114407277749659439314308269)
      ·
        refine ⟨42902729156122289742865601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114407277749659439314308269 42902729156122289742865601)
        ·
          refine ⟨32177046867091717307149201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42902729156122289742865601 32177046867091717307149201)
          ·
            refine ⟨24132785150318787980361901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32177046867091717307149201 24132785150318787980361901)
            ·
              refine ⟨9049794431369545492635713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24132785150318787980361901 9049794431369545492635713)
              ·
                refine ⟨6787345823527159119476785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9049794431369545492635713 6787345823527159119476785)
                ·
                  refine ⟨5090509367645369339607589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6787345823527159119476785 5090509367645369339607589)
                  ·
                    refine ⟨954470506433506751176423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5090509367645369339607589 954470506433506751176423)
                    ·
                      rfl

theorem cell23_5576474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_5576474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576474 prefixEnd_5576474 := by exact prefixLift 5576474
  have htrace : WordTrace (prefixWord ++ tailWord_5576474) baseStart_5576474 baseEnd_5576474 := by
    simpa [prefixWord, tailWord_5576474, baseEnd_5576474] using wordTrace_append hprefix tailTrace_5576474
  have hstable : (prefixWord ++ tailWord_5576474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576474).length < 2 ^ (prefixWord ++ tailWord_5576474).sum := by decide
  have hdescent : baseEnd_5576474 < baseStart_5576474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576481 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 3, 2, 2]
def baseStart_5576481 : Nat := 118140960795 + 5576481 * 2 ^ 59
def prefixEnd_5576481 : Nat := 4983230072969 + 3 ^ 40 * 5576481 * 2
def baseEnd_5576481 : Nat := 2863415113665101726141737

theorem tailTrace_5576481 : CollatzResearch.WordTrace tailWord_5576481 prefixEnd_5576481 2863415113665101726141737 := by
  unfold tailWord_5576481
  simp only [CollatzResearch.WordTrace]
  refine ⟨203390971310369198976497297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135593980873579465984331531 203390971310369198976497297)
  ·
    refine ⟨152543228482776899232372973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203390971310369198976497297 152543228482776899232372973)
    ·
      refine ⟨57203710681041337212139865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152543228482776899232372973 57203710681041337212139865)
      ·
        refine ⟨42902783010781002909104899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57203710681041337212139865 42902783010781002909104899)
        ·
          refine ⟨64354174516171504363657349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42902783010781002909104899 64354174516171504363657349)
          ·
            refine ⟨12066407721782157068185753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64354174516171504363657349 12066407721782157068185753)
            ·
              refine ⟨9049805791336617801139315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12066407721782157068185753 9049805791336617801139315)
              ·
                refine ⟨13574708687004926701708973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9049805791336617801139315 13574708687004926701708973)
                ·
                  refine ⟨5090515757626847513140865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13574708687004926701708973 5090515757626847513140865)
                  ·
                    refine ⟨3817886818220135634855649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5090515757626847513140865 3817886818220135634855649)
                    ·
                      refine ⟨2863415113665101726141737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817886818220135634855649 2863415113665101726141737)
                      ·
                        rfl

theorem cell23_5576481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_5576481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576481 prefixEnd_5576481 := by exact prefixLift 5576481
  have htrace : WordTrace (prefixWord ++ tailWord_5576481) baseStart_5576481 baseEnd_5576481 := by
    simpa [prefixWord, tailWord_5576481, baseEnd_5576481] using wordTrace_append hprefix tailTrace_5576481
  have hstable : (prefixWord ++ tailWord_5576481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576481).length < 2 ^ (prefixWord ++ tailWord_5576481).sum := by decide
  have hdescent : baseEnd_5576481 < baseStart_5576481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576494 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_5576494 : Nat := 118140960795 + 5576494 * 2 ^ 59
def prefixEnd_5576494 : Nat := 4983230072969 + 3 ^ 40 * 5576494 * 2
def baseEnd_5576494 : Nat := 2863421788913610175279177

theorem tailTrace_5576494 : CollatzResearch.WordTrace tailWord_5576494 prefixEnd_5576494 2863421788913610175279177 := by
  unfold tailWord_5576494
  simp only [CollatzResearch.WordTrace]
  refine ⟨25423930682415262774590067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135594296972881401464480357 25423930682415262774590067)
  ·
    refine ⟨38135896023622894161885101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25423930682415262774590067 38135896023622894161885101)
    ·
      refine ⟨14300961008858585310706913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38135896023622894161885101 14300961008858585310706913)
      ·
        refine ⟨10725720756643938983030185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14300961008858585310706913 10725720756643938983030185)
        ·
          refine ⟨8044290567482954237272639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10725720756643938983030185 8044290567482954237272639)
          ·
            refine ⟨12066435851224431355908959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044290567482954237272639 12066435851224431355908959)
            ·
              refine ⟨18099653776836647033863439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12066435851224431355908959 18099653776836647033863439)
              ·
                refine ⟨27149480665254970550795159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18099653776836647033863439 27149480665254970550795159)
                ·
                  refine ⟨40724220997882455826192739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27149480665254970550795159 40724220997882455826192739)
                  ·
                    refine ⟨61086331496823683739289109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40724220997882455826192739 61086331496823683739289109)
                    ·
                      refine ⟨2863421788913610175279177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61086331496823683739289109 2863421788913610175279177)
                      ·
                        rfl

theorem cell23_5576494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_5576494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576494 prefixEnd_5576494 := by exact prefixLift 5576494
  have htrace : WordTrace (prefixWord ++ tailWord_5576494) baseStart_5576494 baseEnd_5576494 := by
    simpa [prefixWord, tailWord_5576494, baseEnd_5576494] using wordTrace_append hprefix tailTrace_5576494
  have hstable : (prefixWord ++ tailWord_5576494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576494).length < 2 ^ (prefixWord ++ tailWord_5576494).sum := by decide
  have hdescent : baseEnd_5576494 < baseStart_5576494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576501 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_5576501 : Nat := 118140960795 + 5576501 * 2 ^ 59
def prefixEnd_5576501 : Nat := 4983230072969 + 3 ^ 40 * 5576501 * 2
def baseEnd_5576501 : Nat := 2863425383278191647891645

theorem tailTrace_5576501 : CollatzResearch.WordTrace tailWord_5576501 prefixEnd_5576501 2863425383278191647891645 := by
  unfold tailWord_5576501
  simp only [CollatzResearch.WordTrace]
  refine ⟨203391700770296742392225357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135594467180197828261483571 203391700770296742392225357)
  ·
    refine ⟨76271887788861278397084509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203391700770296742392225357 76271887788861278397084509)
    ·
      refine ⟨28601957920822979398906691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76271887788861278397084509 28601957920822979398906691)
      ·
        refine ⟨42902936881234469098360037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28601957920822979398906691 42902936881234469098360037)
        ·
          refine ⟨8044300665231462955942507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42902936881234469098360037 8044300665231462955942507)
          ·
            refine ⟨12066450997847194433913761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044300665231462955942507 12066450997847194433913761)
            ·
              refine ⟨9049838248385395825435321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12066450997847194433913761 9049838248385395825435321)
              ·
                refine ⟨6787378686289046869076491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9049838248385395825435321 6787378686289046869076491)
                ·
                  refine ⟨10181068029433570303614737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6787378686289046869076491 10181068029433570303614737)
                  ·
                    refine ⟨7635801022075177727711053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10181068029433570303614737 7635801022075177727711053)
                    ·
                      refine ⟨2863425383278191647891645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7635801022075177727711053 2863425383278191647891645)
                      ·
                        rfl

theorem cell23_5576501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_5576501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576501 prefixEnd_5576501 := by exact prefixLift 5576501
  have htrace : WordTrace (prefixWord ++ tailWord_5576501) baseStart_5576501 baseEnd_5576501 := by
    simpa [prefixWord, tailWord_5576501, baseEnd_5576501] using wordTrace_append hprefix tailTrace_5576501
  have hstable : (prefixWord ++ tailWord_5576501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576501).length < 2 ^ (prefixWord ++ tailWord_5576501).sum := by decide
  have hdescent : baseEnd_5576501 < baseStart_5576501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576518 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_5576518 : Nat := 118140960795 + 5576518 * 2 ^ 59
def prefixEnd_5576518 : Nat := 4983230072969 + 3 ^ 40 * 5576518 * 2
def baseEnd_5576518 : Nat := 2863434112449318081379067

theorem tailTrace_5576518 : CollatzResearch.WordTrace tailWord_5576518 prefixEnd_5576518 2863434112449318081379067 := by
  unfold tailWord_5576518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6356010025351098571737319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135594880540823436197062805 6356010025351098571737319)
  ·
    refine ⟨9534015038026647857605979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6356010025351098571737319 9534015038026647857605979)
    ·
      refine ⟨14301022557039971786408969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9534015038026647857605979 14301022557039971786408969)
      ·
        refine ⟨10725766917779978839806727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14301022557039971786408969 10725766917779978839806727)
        ·
          refine ⟨16088650376669968259710091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10725766917779978839806727 16088650376669968259710091)
          ·
            refine ⟨24132975565004952389565137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16088650376669968259710091 24132975565004952389565137)
            ·
              refine ⟨18099731673753714292173853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24132975565004952389565137 18099731673753714292173853)
              ·
                refine ⟨6787399377657642859565195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18099731673753714292173853 6787399377657642859565195)
                ·
                  refine ⟨10181099066486464289347793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6787399377657642859565195 10181099066486464289347793)
                  ·
                    refine ⟨7635824299864848217010845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10181099066486464289347793 7635824299864848217010845)
                    ·
                      refine ⟨2863434112449318081379067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7635824299864848217010845 2863434112449318081379067)
                      ·
                        rfl

theorem cell23_5576518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_5576518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576518 prefixEnd_5576518 := by exact prefixLift 5576518
  have htrace : WordTrace (prefixWord ++ tailWord_5576518) baseStart_5576518 baseEnd_5576518 := by
    simpa [prefixWord, tailWord_5576518, baseEnd_5576518] using wordTrace_append hprefix tailTrace_5576518
  have hstable : (prefixWord ++ tailWord_5576518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576518).length < 2 ^ (prefixWord ++ tailWord_5576518).sum := by decide
  have hdescent : baseEnd_5576518 < baseStart_5576518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576557 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_5576557 : Nat := 118140960795 + 5576557 * 2 ^ 59
def prefixEnd_5576557 : Nat := 4983230072969 + 3 ^ 40 * 5576557 * 2
def baseEnd_5576557 : Nat := 2863454138194843428791387

theorem tailTrace_5576557 : CollatzResearch.WordTrace tailWord_5576557 prefixEnd_5576557 2863454138194843428791387 := by
  unfold tailWord_5576557
  simp only [CollatzResearch.WordTrace]
  refine ⟨203393743258093863956263925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135595828838729242637509283 203393743258093863956263925)
  ·
    refine ⟨19068163430446299745899743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203393743258093863956263925 19068163430446299745899743)
    ·
      refine ⟨28602245145669449618849615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19068163430446299745899743 28602245145669449618849615)
      ·
        refine ⟨42903367718504174428274423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28602245145669449618849615 42903367718504174428274423)
        ·
          refine ⟨64355051577756261642411635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42903367718504174428274423 64355051577756261642411635)
          ·
            refine ⟨96532577366634392463617453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64355051577756261642411635 96532577366634392463617453)
            ·
              refine ⟨36199716512487897173856545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96532577366634392463617453 36199716512487897173856545)
              ·
                refine ⟨27149787384365922880392409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36199716512487897173856545 27149787384365922880392409)
                ·
                  refine ⟨20362340538274442160294307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27149787384365922880392409 20362340538274442160294307)
                  ·
                    refine ⟨30543510807411663240441461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20362340538274442160294307 30543510807411663240441461)
                    ·
                      refine ⟨2863454138194843428791387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30543510807411663240441461 2863454138194843428791387)
                      ·
                        rfl

theorem cell23_5576557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_5576557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576557 prefixEnd_5576557 := by exact prefixLift 5576557
  have htrace : WordTrace (prefixWord ++ tailWord_5576557) baseStart_5576557 baseEnd_5576557 := by
    simpa [prefixWord, tailWord_5576557, baseEnd_5576557] using wordTrace_append hprefix tailTrace_5576557
  have hstable : (prefixWord ++ tailWord_5576557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576557).length < 2 ^ (prefixWord ++ tailWord_5576557).sum := by decide
  have hdescent : baseEnd_5576557 < baseStart_5576557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576558 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_5576558 : Nat := 118140960795 + 5576558 * 2 ^ 59
def prefixEnd_5576558 : Nat := 4983230072969 + 3 ^ 40 * 5576558 * 2
def baseEnd_5576558 : Nat := 2863454651675497924878883

theorem tailTrace_5576558 : CollatzResearch.WordTrace tailWord_5576558 prefixEnd_5576558 2863454651675497924878883 := by
  unfold tailWord_5576558
  simp only [CollatzResearch.WordTrace]
  refine ⟨25424222466386280140881291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135595853154060160751366885 25424222466386280140881291)
  ·
    refine ⟨38136333699579420211321937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25424222466386280140881291 38136333699579420211321937)
    ·
      refine ⟨28602250274684565158491453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38136333699579420211321937 28602250274684565158491453)
      ·
        refine ⟨10725843853006711934434295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28602250274684565158491453 10725843853006711934434295)
        ·
          refine ⟨16088765779510067901651443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10725843853006711934434295 16088765779510067901651443)
          ·
            refine ⟨24133148669265101852477165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16088765779510067901651443 24133148669265101852477165)
            ·
              refine ⟨9049930750974413194678937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24133148669265101852477165 9049930750974413194678937)
              ·
                refine ⟨6787448063230809896009203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9049930750974413194678937 6787448063230809896009203)
                ·
                  refine ⟨10181172094846214844013805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6787448063230809896009203 10181172094846214844013805)
                  ·
                    refine ⟨3817939535567330566505177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10181172094846214844013805 3817939535567330566505177)
                    ·
                      refine ⟨2863454651675497924878883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3817939535567330566505177 2863454651675497924878883)
                      ·
                        rfl

theorem cell23_5576558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_5576558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576558 prefixEnd_5576558 := by exact prefixLift 5576558
  have htrace : WordTrace (prefixWord ++ tailWord_5576558) baseStart_5576558 baseEnd_5576558 := by
    simpa [prefixWord, tailWord_5576558, baseEnd_5576558] using wordTrace_append hprefix tailTrace_5576558
  have hstable : (prefixWord ++ tailWord_5576558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576558).length < 2 ^ (prefixWord ++ tailWord_5576558).sum := by decide
  have hdescent : baseEnd_5576558 < baseStart_5576558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576560 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 9]
def baseStart_5576560 : Nat := 118140960795 + 5576560 * 2 ^ 59
def prefixEnd_5576560 : Nat := 4983230072969 + 3 ^ 40 * 5576560 * 2
def baseEnd_5576560 : Nat := 318161742070756324117097

theorem tailTrace_5576560 : CollatzResearch.WordTrace tailWord_5576560 prefixEnd_5576560 318161742070756324117097 := by
  unfold tailWord_5576560
  simp only [CollatzResearch.WordTrace]
  refine ⟨101696926338541497734311567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135595901784721996979082089 101696926338541497734311567)
  ·
    refine ⟨152545389507812246601467351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101696926338541497734311567 152545389507812246601467351)
    ·
      refine ⟨228818084261718369902201027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152545389507812246601467351 228818084261718369902201027)
      ·
        refine ⟨343227126392577554853301541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228818084261718369902201027 343227126392577554853301541)
        ·
          refine ⟨64355086198608291534994039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 343227126392577554853301541 64355086198608291534994039)
          ·
            refine ⟨96532629297912437302491059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64355086198608291534994039 96532629297912437302491059)
            ·
              refine ⟨144798943946868655953736589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96532629297912437302491059 144798943946868655953736589)
              ·
                refine ⟨54299603980075745982651221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144798943946868655953736589 54299603980075745982651221)
                ·
                  refine ⟨318161742070756324117097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54299603980075745982651221 318161742070756324117097)
                  ·
                    rfl

theorem cell23_5576560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 9].length) (baseStart_5576560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576560 prefixEnd_5576560 := by exact prefixLift 5576560
  have htrace : WordTrace (prefixWord ++ tailWord_5576560) baseStart_5576560 baseEnd_5576560 := by
    simpa [prefixWord, tailWord_5576560, baseEnd_5576560] using wordTrace_append hprefix tailTrace_5576560
  have hstable : (prefixWord ++ tailWord_5576560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576560).length < 2 ^ (prefixWord ++ tailWord_5576560).sum := by decide
  have hdescent : baseEnd_5576560 < baseStart_5576560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576587 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 3]
def baseStart_5576587 : Nat := 118140960795 + 5576587 * 2 ^ 59
def prefixEnd_5576587 : Nat := 4983230072969 + 3 ^ 40 * 5576587 * 2
def baseEnd_5576587 : Nat := 2863469542614478311416249

theorem tailTrace_5576587 : CollatzResearch.WordTrace tailWord_5576587 prefixEnd_5576587 2863469542614478311416249 := by
  unfold tailWord_5576587
  simp only [CollatzResearch.WordTrace]
  refine ⟨203394837447985179079856015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135596558298656786053237343 203394837447985179079856015)
  ·
    refine ⟨305092256171977768619784023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203394837447985179079856015 305092256171977768619784023)
    ·
      refine ⟨457638384257966652929676035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305092256171977768619784023 457638384257966652929676035)
      ·
        refine ⟨686457576386949979394514053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457638384257966652929676035 686457576386949979394514053)
        ·
          refine ⟨128710795572553121136471385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 686457576386949979394514053 128710795572553121136471385)
          ·
            refine ⟨96533096679414840852353539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128710795572553121136471385 96533096679414840852353539)
            ·
              refine ⟨144799645019122261278530309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96533096679414840852353539 144799645019122261278530309)
              ·
                refine ⟨27149933441085423989724433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144799645019122261278530309 27149933441085423989724433)
                ·
                  refine ⟨20362450080814067992293325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27149933441085423989724433 20362450080814067992293325)
                  ·
                    refine ⟨7635918780305275497109997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20362450080814067992293325 7635918780305275497109997)
                    ·
                      refine ⟨2863469542614478311416249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7635918780305275497109997 2863469542614478311416249)
                      ·
                        rfl

theorem cell23_5576587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 3].length) (baseStart_5576587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576587 prefixEnd_5576587 := by exact prefixLift 5576587
  have htrace : WordTrace (prefixWord ++ tailWord_5576587) baseStart_5576587 baseEnd_5576587 := by
    simpa [prefixWord, tailWord_5576587, baseEnd_5576587] using wordTrace_append hprefix tailTrace_5576587
  have hstable : (prefixWord ++ tailWord_5576587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576587).length < 2 ^ (prefixWord ++ tailWord_5576587).sum := by decide
  have hdescent : baseEnd_5576587 < baseStart_5576587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576598 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_5576598 : Nat := 118140960795 + 5576598 * 2 ^ 59
def prefixEnd_5576598 : Nat := 4983230072969 + 3 ^ 40 * 5576598 * 2
def baseEnd_5576598 : Nat := 954491730300559256126233

theorem tailTrace_5576598 : CollatzResearch.WordTrace tailWord_5576598 prefixEnd_5576598 954491730300559256126233 := by
  unfold tailWord_5576598
  simp only [CollatzResearch.WordTrace]
  refine ⟨12712202415684082997406653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135596825767296885305670965 12712202415684082997406653)
  ·
    refine ⟨4767075905881531124027495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12712202415684082997406653 4767075905881531124027495)
    ·
      refine ⟨7150613858822296686041243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4767075905881531124027495 7150613858822296686041243)
      ·
        refine ⟨10725920788233445029061865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7150613858822296686041243 10725920788233445029061865)
        ·
          refine ⟨8044440591175083771796399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10725920788233445029061865 8044440591175083771796399)
          ·
            refine ⟨12066660886762625657694599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044440591175083771796399 12066660886762625657694599)
            ·
              refine ⟨18099991330143938486541899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12066660886762625657694599 18099991330143938486541899)
              ·
                refine ⟨27149986995215907729812849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18099991330143938486541899 27149986995215907729812849)
                ·
                  refine ⟨20362490246411930797359637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27149986995215907729812849 20362490246411930797359637)
                  ·
                    refine ⟨954491730300559256126233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20362490246411930797359637 954491730300559256126233)
                    ·
                      rfl

theorem cell23_5576598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_5576598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576598 prefixEnd_5576598 := by exact prefixLift 5576598
  have htrace : WordTrace (prefixWord ++ tailWord_5576598) baseStart_5576598 baseEnd_5576598 := by
    simpa [prefixWord, tailWord_5576598, baseEnd_5576598] using wordTrace_append hprefix tailTrace_5576598
  have hstable : (prefixWord ++ tailWord_5576598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576598).length < 2 ^ (prefixWord ++ tailWord_5576598).sum := by decide
  have hdescent : baseEnd_5576598 < baseStart_5576598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576604 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_5576604 : Nat := 118140960795 + 5576604 * 2 ^ 59
def prefixEnd_5576604 : Nat := 4983230072969 + 3 ^ 40 * 5576604 * 2
def baseEnd_5576604 : Nat := 2863478271785604744903671

theorem tailTrace_5576604 : CollatzResearch.WordTrace tailWord_5576604 prefixEnd_5576604 2863478271785604744903671 := by
  unfold tailWord_5576604
  simp only [CollatzResearch.WordTrace]
  refine ⟨101697728744461795491612433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135596971659282393988816577 101697728744461795491612433)
  ·
    refine ⟨76273296558346346618709325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101697728744461795491612433 76273296558346346618709325)
    ·
      refine ⟨28602486209379879982015997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76273296558346346618709325 28602486209379879982015997)
      ·
        refine ⟨10725932328517454993255999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28602486209379879982015997 10725932328517454993255999)
        ·
          refine ⟨16088898492776182489883999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10725932328517454993255999 16088898492776182489883999)
          ·
            refine ⟨24133347739164273734825999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16088898492776182489883999 24133347739164273734825999)
            ·
              refine ⟨36200021608746410602238999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24133347739164273734825999 36200021608746410602238999)
              ·
                refine ⟨54300032413119615903358499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36200021608746410602238999 54300032413119615903358499)
                ·
                  refine ⟨81450048619679423855037749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54300032413119615903358499 81450048619679423855037749)
                  ·
                    refine ⟨7635942058094945986409789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81450048619679423855037749 7635942058094945986409789)
                    ·
                      refine ⟨2863478271785604744903671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7635942058094945986409789 2863478271785604744903671)
                      ·
                        rfl

theorem cell23_5576604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_5576604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576604 prefixEnd_5576604 := by exact prefixLift 5576604
  have htrace : WordTrace (prefixWord ++ tailWord_5576604) baseStart_5576604 baseEnd_5576604 := by
    simpa [prefixWord, tailWord_5576604, baseEnd_5576604] using wordTrace_append hprefix tailTrace_5576604
  have hstable : (prefixWord ++ tailWord_5576604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576604).length < 2 ^ (prefixWord ++ tailWord_5576604).sum := by decide
  have hdescent : baseEnd_5576604 < baseStart_5576604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576627 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 4]
def baseStart_5576627 : Nat := 118140960795 + 5576627 * 2 ^ 59
def prefixEnd_5576627 : Nat := 4983230072969 + 3 ^ 40 * 5576627 * 2
def baseEnd_5576627 : Nat := 2863490081840658154916065

theorem tailTrace_5576627 : CollatzResearch.WordTrace tailWord_5576627 prefixEnd_5576627 2863490081840658154916065 := by
  unfold tailWord_5576627
  simp only [CollatzResearch.WordTrace]
  refine ⟨203396296367840265911312135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135597530911893510607541423 203396296367840265911312135)
  ·
    refine ⟨305094444551760398866968203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203396296367840265911312135 305094444551760398866968203)
    ·
      refine ⟨457641666827640598300452305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305094444551760398866968203 457641666827640598300452305)
      ·
        refine ⟨343231250120730448725339229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457641666827640598300452305 343231250120730448725339229)
        ·
          refine ⟨128711718795273918272002211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343231250120730448725339229 128711718795273918272002211)
          ·
            refine ⟨193067578192910877408003317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128711718795273918272002211 193067578192910877408003317)
            ·
              refine ⟨18100085455585394757000311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193067578192910877408003317 18100085455585394757000311)
              ·
                refine ⟨27150128183378092135500467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18100085455585394757000311 27150128183378092135500467)
                ·
                  refine ⟨40725192275067138203250701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27150128183378092135500467 40725192275067138203250701)
                  ·
                    refine ⟨15271947103150176826219013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40725192275067138203250701 15271947103150176826219013)
                    ·
                      refine ⟨2863490081840658154916065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15271947103150176826219013 2863490081840658154916065)
                      ·
                        rfl

theorem cell23_5576627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 4].length) (baseStart_5576627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576627 prefixEnd_5576627 := by exact prefixLift 5576627
  have htrace : WordTrace (prefixWord ++ tailWord_5576627) baseStart_5576627 baseEnd_5576627 := by
    simpa [prefixWord, tailWord_5576627, baseEnd_5576627] using wordTrace_append hprefix tailTrace_5576627
  have hstable : (prefixWord ++ tailWord_5576627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576627).length < 2 ^ (prefixWord ++ tailWord_5576627).sum := by decide
  have hdescent : baseEnd_5576627 < baseStart_5576627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576661 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 2, 4, 2]
def baseStart_5576661 : Nat := 118140960795 + 5576661 * 2 ^ 59
def prefixEnd_5576661 : Nat := 4983230072969 + 3 ^ 40 * 5576661 * 2
def baseEnd_5576661 : Nat := 2863507540182911021890909

theorem tailTrace_5576661 : CollatzResearch.WordTrace tailWord_5576661 prefixEnd_5576661 2863507540182911021890909 := by
  unfold tailWord_5576661
  simp only [CollatzResearch.WordTrace]
  refine ⟨203397536449717089718049837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135598357633144726478699891 203397536449717089718049837)
  ·
    refine ⟨76274076168643908644268689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203397536449717089718049837 76274076168643908644268689)
    ·
      refine ⟨57205557126482931483201517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76274076168643908644268689 57205557126482931483201517)
      ·
        refine ⟨21452083922431099306200569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57205557126482931483201517 21452083922431099306200569)
        ·
          refine ⟨16089062941823324479650427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21452083922431099306200569 16089062941823324479650427)
          ·
            refine ⟨24133594412734986719475641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16089062941823324479650427 24133594412734986719475641)
            ·
              refine ⟨18100195809551240039606731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24133594412734986719475641 18100195809551240039606731)
              ·
                refine ⟨27150293714326860059410097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18100195809551240039606731 27150293714326860059410097)
                ·
                  refine ⟨20362720285745145044557573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27150293714326860059410097 20362720285745145044557573)
                  ·
                    refine ⟨3818010053577214695854545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20362720285745145044557573 3818010053577214695854545)
                    ·
                      refine ⟨2863507540182911021890909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818010053577214695854545 2863507540182911021890909)
                      ·
                        rfl

theorem cell23_5576661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_5576661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576661 prefixEnd_5576661 := by exact prefixLift 5576661
  have htrace : WordTrace (prefixWord ++ tailWord_5576661) baseStart_5576661 baseEnd_5576661 := by
    simpa [prefixWord, tailWord_5576661, baseEnd_5576661] using wordTrace_append hprefix tailTrace_5576661
  have hstable : (prefixWord ++ tailWord_5576661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576661).length < 2 ^ (prefixWord ++ tailWord_5576661).sum := by decide
  have hdescent : baseEnd_5576661 < baseStart_5576661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576704 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 3, 5, 2]
def baseStart_5576704 : Nat := 118140960795 + 5576704 * 2 ^ 59
def prefixEnd_5576704 : Nat := 4983230072969 + 3 ^ 40 * 5576704 * 2
def baseEnd_5576704 : Nat := 2863529619851054353653211

theorem tailTrace_5576704 : CollatzResearch.WordTrace tailWord_5576704 prefixEnd_5576704 2863529619851054353653211 := by
  unfold tailWord_5576704
  simp only [CollatzResearch.WordTrace]
  refine ⟨101699552394280654030932583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135599403192374205374576777 101699552394280654030932583)
  ·
    refine ⟨152549328591420981046398875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101699552394280654030932583 152549328591420981046398875)
    ·
      refine ⟨228823992887131471569598313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152549328591420981046398875 228823992887131471569598313)
      ·
        refine ⟨171617994665348603677198735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228823992887131471569598313 171617994665348603677198735)
        ·
          refine ⟨257426991998022905515798103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171617994665348603677198735 257426991998022905515798103)
          ·
            refine ⟨386140487997034358273697155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257426991998022905515798103 386140487997034358273697155)
            ·
              refine ⟨579210731995551537410545733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386140487997034358273697155 579210731995551537410545733)
              ·
                refine ⟨108602012249165913264477325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 579210731995551537410545733 108602012249165913264477325)
                ·
                  refine ⟨40725754593437217474178997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108602012249165913264477325 40725754593437217474178997)
                  ·
                    refine ⟨3818039493134739138204281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40725754593437217474178997 3818039493134739138204281)
                    ·
                      refine ⟨2863529619851054353653211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818039493134739138204281 2863529619851054353653211)
                      ·
                        rfl

theorem cell23_5576704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 3, 5, 2].length) (baseStart_5576704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576704 prefixEnd_5576704 := by exact prefixLift 5576704
  have htrace : WordTrace (prefixWord ++ tailWord_5576704) baseStart_5576704 baseEnd_5576704 := by
    simpa [prefixWord, tailWord_5576704, baseEnd_5576704] using wordTrace_append hprefix tailTrace_5576704
  have hstable : (prefixWord ++ tailWord_5576704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576704).length < 2 ^ (prefixWord ++ tailWord_5576704).sum := by decide
  have hdescent : baseEnd_5576704 < baseStart_5576704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576738 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_5576738 : Nat := 118140960795 + 5576738 * 2 ^ 59
def prefixEnd_5576738 : Nat := 4983230072969 + 3 ^ 40 * 5576738 * 2
def baseEnd_5576738 : Nat := 2863547078193307220628055

theorem tailTrace_5576738 : CollatzResearch.WordTrace tailWord_5576738 prefixEnd_5576738 2863547078193307220628055 := by
  unfold tailWord_5576738
  simp only [CollatzResearch.WordTrace]
  refine ⟨50850086217609532967150717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135600229913625421245735245 50850086217609532967150717)
  ·
    refine ⟨19068782331603574862681519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50850086217609532967150717 19068782331603574862681519)
    ·
      refine ⟨28603173497405362294022279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19068782331603574862681519 28603173497405362294022279)
      ·
        refine ⟨42904760246108043441033419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28603173497405362294022279 42904760246108043441033419)
        ·
          refine ⟨64357140369162065161550129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42904760246108043441033419 64357140369162065161550129)
          ·
            refine ⟨48267855276871548871162597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64357140369162065161550129 48267855276871548871162597)
            ·
              refine ⟨9050222864413415413342987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48267855276871548871162597 9050222864413415413342987)
              ·
                refine ⟨13575334296620123120014481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9050222864413415413342987 13575334296620123120014481)
                ·
                  refine ⟨10181500722465092340010861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13575334296620123120014481 10181500722465092340010861)
                  ·
                    refine ⟨3818062770924409627504073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10181500722465092340010861 3818062770924409627504073)
                    ·
                      refine ⟨2863547078193307220628055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818062770924409627504073 2863547078193307220628055)
                      ·
                        rfl

theorem cell23_5576738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_5576738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576738 prefixEnd_5576738 := by exact prefixLift 5576738
  have htrace : WordTrace (prefixWord ++ tailWord_5576738) baseStart_5576738 baseEnd_5576738 := by
    simpa [prefixWord, tailWord_5576738, baseEnd_5576738] using wordTrace_append hprefix tailTrace_5576738
  have hstable : (prefixWord ++ tailWord_5576738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576738).length < 2 ^ (prefixWord ++ tailWord_5576738).sum := by decide
  have hdescent : baseEnd_5576738 < baseStart_5576738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576747 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 6]
def baseStart_5576747 : Nat := 118140960795 + 5576747 * 2 ^ 59
def prefixEnd_5576747 : Nat := 4983230072969 + 3 ^ 40 * 5576747 * 2
def baseEnd_5576747 : Nat := 2863551699519197685415513

theorem tailTrace_5576747 : CollatzResearch.WordTrace tailWord_5576747 prefixEnd_5576747 2863551699519197685415513 := by
  unfold tailWord_5576747
  simp only [CollatzResearch.WordTrace]
  refine ⟨203400673127405526405680495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135600448751603684270453663 203400673127405526405680495)
  ·
    refine ⟨305101009691108289608520743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203400673127405526405680495 305101009691108289608520743)
    ·
      refine ⟨457651514536662434412781115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305101009691108289608520743 457651514536662434412781115)
      ·
        refine ⟨686477271804993651619171673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457651514536662434412781115 686477271804993651619171673)
        ·
          refine ⟨514857953853745238714378755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686477271804993651619171673 514857953853745238714378755)
          ·
            refine ⟨772286930780617858071568133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514857953853745238714378755 772286930780617858071568133)
            ·
              refine ⟨144803799521365848388419025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 772286930780617858071568133 144803799521365848388419025)
              ·
                refine ⟨108602849641024386291314269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144803799521365848388419025 108602849641024386291314269)
                ·
                  refine ⟨40726068615384144859242851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108602849641024386291314269 40726068615384144859242851)
                  ·
                    refine ⟨61089102923076217288864277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40726068615384144859242851 61089102923076217288864277)
                    ·
                      refine ⟨2863551699519197685415513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61089102923076217288864277 2863551699519197685415513)
                      ·
                        rfl

theorem cell23_5576747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_5576747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576747 prefixEnd_5576747 := by exact prefixLift 5576747
  have htrace : WordTrace (prefixWord ++ tailWord_5576747) baseStart_5576747 baseEnd_5576747 := by
    simpa [prefixWord, tailWord_5576747, baseEnd_5576747] using wordTrace_append hprefix tailTrace_5576747
  have hstable : (prefixWord ++ tailWord_5576747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576747).length < 2 ^ (prefixWord ++ tailWord_5576747).sum := by decide
  have hdescent : baseEnd_5576747 < baseStart_5576747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576751 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 7, 2, 2]
def baseStart_5576751 : Nat := 118140960795 + 5576751 * 2 ^ 59
def prefixEnd_5576751 : Nat := 4983230072969 + 3 ^ 40 * 5576751 * 2
def baseEnd_5576751 : Nat := 2863553753441815669765495

theorem tailTrace_5576751 : CollatzResearch.WordTrace tailWord_5576751 prefixEnd_5576751 2863553753441815669765495 := by
  unfold tailWord_5576751
  simp only [CollatzResearch.WordTrace]
  refine ⟨203400819019391035088826107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135600546012927356725884071 203400819019391035088826107)
  ·
    refine ⟨305101228529086552633239161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203400819019391035088826107 305101228529086552633239161)
    ·
      refine ⟨228825921396814914474929371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305101228529086552633239161 228825921396814914474929371)
      ·
        refine ⟨343238882095222371712394057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228825921396814914474929371 343238882095222371712394057)
        ·
          refine ⟨257429161571416778784295543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343238882095222371712394057 257429161571416778784295543)
          ·
            refine ⟨386143742357125168176443315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257429161571416778784295543 386143742357125168176443315)
            ·
              refine ⟨579215613535687752264664973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386143742357125168176443315 579215613535687752264664973)
              ·
                refine ⟨217205855075882907099249365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 579215613535687752264664973 217205855075882907099249365)
                ·
                  refine ⟨5090762228341005635138657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 217205855075882907099249365 5090762228341005635138657)
                  ·
                    refine ⟨3818071671255754226353993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5090762228341005635138657 3818071671255754226353993)
                    ·
                      refine ⟨2863553753441815669765495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818071671255754226353993 2863553753441815669765495)
                      ·
                        rfl

theorem cell23_5576751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7, 2, 2].length) (baseStart_5576751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576751 prefixEnd_5576751 := by exact prefixLift 5576751
  have htrace : WordTrace (prefixWord ++ tailWord_5576751) baseStart_5576751 baseEnd_5576751 := by
    simpa [prefixWord, tailWord_5576751, baseEnd_5576751] using wordTrace_append hprefix tailTrace_5576751
  have hstable : (prefixWord ++ tailWord_5576751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576751).length < 2 ^ (prefixWord ++ tailWord_5576751).sum := by decide
  have hdescent : baseEnd_5576751 < baseStart_5576751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576764 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_5576764 : Nat := 118140960795 + 5576764 * 2 ^ 59
def prefixEnd_5576764 : Nat := 4983230072969 + 3 ^ 40 * 5576764 * 2
def baseEnd_5576764 : Nat := 2863560428690324118902935

theorem tailTrace_5576764 : CollatzResearch.WordTrace tailWord_5576764 prefixEnd_5576764 2863560428690324118902935 := by
  unfold tailWord_5576764
  simp only [CollatzResearch.WordTrace]
  refine ⟨101700646584171969154524673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135600862112229292206032897 101700646584171969154524673)
  ·
    refine ⟨76275484938128976865893505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101700646584171969154524673 76275484938128976865893505)
    ·
      refine ⟨57206613703596732649420129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76275484938128976865893505 57206613703596732649420129)
      ·
        refine ⟨42904960277697549487065097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57206613703596732649420129 42904960277697549487065097)
        ·
          refine ⟨32178720208273162115298823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42904960277697549487065097 32178720208273162115298823)
          ·
            refine ⟨48268080312409743172948235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32178720208273162115298823 48268080312409743172948235)
            ·
              refine ⟨72402120468614614759422353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48268080312409743172948235 72402120468614614759422353)
              ·
                refine ⟨54301590351460961069566765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72402120468614614759422353 54301590351460961069566765)
                ·
                  refine ⟨20363096381797860401087537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54301590351460961069566765 20363096381797860401087537)
                  ·
                    refine ⟨15272322286348395300815653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20363096381797860401087537 15272322286348395300815653)
                    ·
                      refine ⟨2863560428690324118902935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15272322286348395300815653 2863560428690324118902935)
                      ·
                        rfl

theorem cell23_5576764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_5576764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576764 prefixEnd_5576764 := by exact prefixLift 5576764
  have htrace : WordTrace (prefixWord ++ tailWord_5576764) baseStart_5576764 baseEnd_5576764 := by
    simpa [prefixWord, tailWord_5576764, baseEnd_5576764] using wordTrace_append hprefix tailTrace_5576764
  have hstable : (prefixWord ++ tailWord_5576764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576764).length < 2 ^ (prefixWord ++ tailWord_5576764).sum := by decide
  have hdescent : baseEnd_5576764 < baseStart_5576764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576787 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 3, 9]
def baseStart_5576787 : Nat := 118140960795 + 5576787 * 2 ^ 59
def prefixEnd_5576787 : Nat := 4983230072969 + 3 ^ 40 * 5576787 * 2
def baseEnd_5576787 : Nat := 954524079581792509638443

theorem tailTrace_5576787 : CollatzResearch.WordTrace tailWord_5576787 prefixEnd_5576787 954524079581792509638443 := by
  unfold tailWord_5576787
  simp only [CollatzResearch.WordTrace]
  refine ⟨203402132047260613237136615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135601421364840408824757743 203402132047260613237136615)
  ·
    refine ⟨305103198070890919855704923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203402132047260613237136615 305103198070890919855704923)
    ·
      refine ⟨457654797106336379783557385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305103198070890919855704923 457654797106336379783557385)
      ·
        refine ⟨343241097829752284837668039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457654797106336379783557385 343241097829752284837668039)
        ·
          refine ⟨514861646744628427256502059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343241097829752284837668039 514861646744628427256502059)
          ·
            refine ⟨772292470116942640884753089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514861646744628427256502059 772292470116942640884753089)
            ·
              refine ⟨579219352587706980663564817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 772292470116942640884753089 579219352587706980663564817)
              ·
                refine ⟨434414514440780235497673613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579219352587706980663564817 434414514440780235497673613)
                ·
                  refine ⟨162905442915292588311627605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 434414514440780235497673613 162905442915292588311627605)
                  ·
                    refine ⟨954524079581792509638443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 162905442915292588311627605 954524079581792509638443)
                    ·
                      rfl

theorem cell23_5576787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 9].length) (baseStart_5576787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576787 prefixEnd_5576787 := by exact prefixLift 5576787
  have htrace : WordTrace (prefixWord ++ tailWord_5576787) baseStart_5576787 baseEnd_5576787 := by
    simpa [prefixWord, tailWord_5576787, baseEnd_5576787] using wordTrace_append hprefix tailTrace_5576787
  have hstable : (prefixWord ++ tailWord_5576787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576787).length < 2 ^ (prefixWord ++ tailWord_5576787).sum := by decide
  have hdescent : baseEnd_5576787 < baseStart_5576787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576801 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_5576801 : Nat := 118140960795 + 5576801 * 2 ^ 59
def prefixEnd_5576801 : Nat := 4983230072969 + 3 ^ 40 * 5576801 * 2
def baseEnd_5576801 : Nat := 2863579427474540474140265

theorem tailTrace_5576801 : CollatzResearch.WordTrace tailWord_5576801 prefixEnd_5576801 2863579427474540474140265 := by
  unfold tailWord_5576801
  simp only [CollatzResearch.WordTrace]
  refine ⟨203402642669209893628146257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135601761779473262418764171 203402642669209893628146257)
  ·
    refine ⟨152551982001907420221109693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203402642669209893628146257 152551982001907420221109693)
    ·
      refine ⟨57206993250715282582916135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152551982001907420221109693 57206993250715282582916135)
      ·
        refine ⟨85810489876072923874374203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57206993250715282582916135 85810489876072923874374203)
        ·
          refine ⟨128715734814109385811561305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85810489876072923874374203 128715734814109385811561305)
          ·
            refine ⟨96536801110582039358670979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128715734814109385811561305 96536801110582039358670979)
            ·
              refine ⟨144805201665873059038006469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96536801110582039358670979 144805201665873059038006469)
              ·
                refine ⟨27150975312351198569626213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144805201665873059038006469 27150975312351198569626213)
                ·
                  refine ⟨5090807871065849731804915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27150975312351198569626213 5090807871065849731804915)
                  ·
                    refine ⟨7636211806598774597707373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5090807871065849731804915 7636211806598774597707373)
                    ·
                      refine ⟨2863579427474540474140265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7636211806598774597707373 2863579427474540474140265)
                      ·
                        rfl

theorem cell23_5576801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_5576801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576801 prefixEnd_5576801 := by exact prefixLift 5576801
  have htrace : WordTrace (prefixWord ++ tailWord_5576801) baseStart_5576801 baseEnd_5576801 := by
    simpa [prefixWord, tailWord_5576801, baseEnd_5576801] using wordTrace_append hprefix tailTrace_5576801
  have hstable : (prefixWord ++ tailWord_5576801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576801).length < 2 ^ (prefixWord ++ tailWord_5576801).sum := by decide
  have hdescent : baseEnd_5576801 < baseStart_5576801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576802 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5576802 : Nat := 118140960795 + 5576802 * 2 ^ 59
def prefixEnd_5576802 : Nat := 4983230072969 + 3 ^ 40 * 5576802 * 2
def baseEnd_5576802 : Nat := 2863579940955194970227761

theorem tailTrace_5576802 : CollatzResearch.WordTrace tailWord_5576802 prefixEnd_5576802 2863579940955194970227761 := by
  unfold tailWord_5576802
  simp only [CollatzResearch.WordTrace]
  refine ⟨50850669785551567699733165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135601786094804180532621773 50850669785551567699733165)
  ·
    refine ⟨19069001169581837887399937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50850669785551567699733165 19069001169581837887399937)
    ·
      refine ⟨14301750877186378415549953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19069001169581837887399937 14301750877186378415549953)
      ·
        refine ⟨10726313157889783811662465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14301750877186378415549953 10726313157889783811662465)
        ·
          refine ⟨8044734868417337858746849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10726313157889783811662465 8044734868417337858746849)
          ·
            refine ⟨6033551151313003394060137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8044734868417337858746849 6033551151313003394060137)
            ·
              refine ⟨4525163363484752545545103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6033551151313003394060137 4525163363484752545545103)
              ·
                refine ⟨6787745045227128818317655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525163363484752545545103 6787745045227128818317655)
                ·
                  refine ⟨10181617567840693227476483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6787745045227128818317655 10181617567840693227476483)
                  ·
                    refine ⟨15272426351761039841214725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10181617567840693227476483 15272426351761039841214725)
                    ·
                      refine ⟨2863579940955194970227761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15272426351761039841214725 2863579940955194970227761)
                      ·
                        rfl

theorem cell23_5576802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5576802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576802 prefixEnd_5576802 := by exact prefixLift 5576802
  have htrace : WordTrace (prefixWord ++ tailWord_5576802) baseStart_5576802 baseEnd_5576802 := by
    simpa [prefixWord, tailWord_5576802, baseEnd_5576802] using wordTrace_append hprefix tailTrace_5576802
  have hstable : (prefixWord ++ tailWord_5576802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576802).length < 2 ^ (prefixWord ++ tailWord_5576802).sum := by decide
  have hdescent : baseEnd_5576802 < baseStart_5576802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576805 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 1, 2, 3]
def baseStart_5576805 : Nat := 118140960795 + 5576805 * 2 ^ 59
def prefixEnd_5576805 : Nat := 4983230072969 + 3 ^ 40 * 5576805 * 2
def baseEnd_5576805 : Nat := 2863581481397158458490247

theorem tailTrace_5576805 : CollatzResearch.WordTrace tailWord_5576805 prefixEnd_5576805 2863581481397158458490247 := by
  unfold tailWord_5576805
  simp only [CollatzResearch.WordTrace]
  refine ⟨203402788561195402311291869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135601859040796934874194579 203402788561195402311291869)
  ·
    refine ⟨76276045710448275866734451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203402788561195402311291869 76276045710448275866734451)
    ·
      refine ⟨114414068565672413800101677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76276045710448275866734451 114414068565672413800101677)
      ·
        refine ⟨42905275712127155175038129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114414068565672413800101677 42905275712127155175038129)
        ·
          refine ⟨32178956784095366381278597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42905275712127155175038129 32178956784095366381278597)
          ·
            refine ⟨6033554397017881196489737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32178956784095366381278597 6033554397017881196489737)
            ·
              refine ⟨4525165797763410897367303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6033554397017881196489737 4525165797763410897367303)
              ·
                refine ⟨6787748696645116346050955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525165797763410897367303 6787748696645116346050955)
                ·
                  refine ⟨10181623044967674519076433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6787748696645116346050955 10181623044967674519076433)
                  ·
                    refine ⟨7636217283725755889307325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10181623044967674519076433 7636217283725755889307325)
                    ·
                      refine ⟨2863581481397158458490247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7636217283725755889307325 2863581481397158458490247)
                      ·
                        rfl

theorem cell23_5576805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_5576805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576805 prefixEnd_5576805 := by exact prefixLift 5576805
  have htrace : WordTrace (prefixWord ++ tailWord_5576805) baseStart_5576805 baseEnd_5576805 := by
    simpa [prefixWord, tailWord_5576805, baseEnd_5576805] using wordTrace_append hprefix tailTrace_5576805
  have hstable : (prefixWord ++ tailWord_5576805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576805).length < 2 ^ (prefixWord ++ tailWord_5576805).sum := by decide
  have hdescent : baseEnd_5576805 < baseStart_5576805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576818 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_5576818 : Nat := 118140960795 + 5576818 * 2 ^ 59
def prefixEnd_5576818 : Nat := 4983230072969 + 3 ^ 40 * 5576818 * 2
def baseEnd_5576818 : Nat := 2863588156645666907627687

theorem tailTrace_5576818 : CollatzResearch.WordTrace tailWord_5576818 prefixEnd_5576818 2863588156645666907627687 := by
  unfold tailWord_5576818
  simp only [CollatzResearch.WordTrace]
  refine ⟨50850815677537076382878777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135602175140098870354343405 50850815677537076382878777)
  ·
    refine ⟨38138111758152807287159083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50850815677537076382878777 38138111758152807287159083)
    ·
      refine ⟨57207167637229210930738625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38138111758152807287159083 57207167637229210930738625)
      ·
        refine ⟨42905375727921908198053969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57207167637229210930738625 42905375727921908198053969)
        ·
          refine ⟨32179031795941431148540477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42905375727921908198053969 32179031795941431148540477)
          ·
            refine ⟨12067136923478036680702679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32179031795941431148540477 12067136923478036680702679)
            ·
              refine ⟨18100705385217055021054019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12067136923478036680702679 18100705385217055021054019)
              ·
                refine ⟨27151058077825582531581029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18100705385217055021054019 27151058077825582531581029)
                ·
                  refine ⟨5090823389592296724671443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27151058077825582531581029 5090823389592296724671443)
                  ·
                    refine ⟨7636235084388445087007165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5090823389592296724671443 7636235084388445087007165)
                    ·
                      refine ⟨2863588156645666907627687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7636235084388445087007165 2863588156645666907627687)
                      ·
                        rfl

theorem cell23_5576818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_5576818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576818 prefixEnd_5576818 := by exact prefixLift 5576818
  have htrace : WordTrace (prefixWord ++ tailWord_5576818) baseStart_5576818 baseEnd_5576818 := by
    simpa [prefixWord, tailWord_5576818, baseEnd_5576818] using wordTrace_append hprefix tailTrace_5576818
  have hstable : (prefixWord ++ tailWord_5576818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576818).length < 2 ^ (prefixWord ++ tailWord_5576818).sum := by decide
  have hdescent : baseEnd_5576818 < baseStart_5576818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576835 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 2, 1, 3]
def baseStart_5576835 : Nat := 118140960795 + 5576835 * 2 ^ 59
def prefixEnd_5576835 : Nat := 4983230072969 + 3 ^ 40 * 5576835 * 2
def baseEnd_5576835 : Nat := 2863596885816793341115109

theorem tailTrace_5576835 : CollatzResearch.WordTrace tailWord_5576835 prefixEnd_5576835 2863596885816793341115109 := by
  unfold tailWord_5576835
  simp only [CollatzResearch.WordTrace]
  refine ⟨203403882751086717434883959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135602588500724478289922639 203403882751086717434883959)
  ·
    refine ⟨305105824126630076152325939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203403882751086717434883959 305105824126630076152325939)
    ·
      refine ⟨457658736189945114228488909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305105824126630076152325939 457658736189945114228488909)
      ·
        refine ⟨171622026071229417835683341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 457658736189945114228488909 171622026071229417835683341)
        ·
          refine ⟨64358259776711031688381253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171622026071229417835683341 64358259776711031688381253)
          ·
            refine ⟨12067173708133318441571485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64358259776711031688381253 12067173708133318441571485)
            ·
              refine ⟨4525190140549994415589307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12067173708133318441571485 4525190140549994415589307)
              ·
                refine ⟨6787785210824991623383961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525190140549994415589307 6787785210824991623383961)
                ·
                  refine ⟨5090838908118743717537971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6787785210824991623383961 5090838908118743717537971)
                  ·
                    refine ⟨7636258362178115576306957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5090838908118743717537971 7636258362178115576306957)
                    ·
                      refine ⟨2863596885816793341115109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7636258362178115576306957 2863596885816793341115109)
                      ·
                        rfl

theorem cell23_5576835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 2, 1, 3].length) (baseStart_5576835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576835 prefixEnd_5576835 := by exact prefixLift 5576835
  have htrace : WordTrace (prefixWord ++ tailWord_5576835) baseStart_5576835 baseEnd_5576835 := by
    simpa [prefixWord, tailWord_5576835, baseEnd_5576835] using wordTrace_append hprefix tailTrace_5576835
  have hstable : (prefixWord ++ tailWord_5576835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576835).length < 2 ^ (prefixWord ++ tailWord_5576835).sum := by decide
  have hdescent : baseEnd_5576835 < baseStart_5576835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576861 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_5576861 : Nat := 118140960795 + 5576861 * 2 ^ 59
def prefixEnd_5576861 : Nat := 4983230072969 + 3 ^ 40 * 5576861 * 2
def baseEnd_5576861 : Nat := 2863610236313810239389989

theorem tailTrace_5576861 : CollatzResearch.WordTrace tailWord_5576861 prefixEnd_5576861 2863610236313810239389989 := by
  unfold tailWord_5576861
  simp only [CollatzResearch.WordTrace]
  refine ⟨203404831048992523875330437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135603220699328349250220291 203404831048992523875330437)
  ·
    refine ⟨38138405821686098226624457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203404831048992523875330437 38138405821686098226624457)
    ·
      refine ⟨28603804366264573669968343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38138405821686098226624457 28603804366264573669968343)
      ·
        refine ⟨42905706549396860504952515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28603804366264573669968343 42905706549396860504952515)
        ·
          refine ⟨64358559824095290757428773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42905706549396860504952515 64358559824095290757428773)
          ·
            refine ⟨12067229967017867017017895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64358559824095290757428773 12067229967017867017017895)
            ·
              refine ⟨18100844950526800525526843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12067229967017867017017895 18100844950526800525526843)
              ·
                refine ⟨27151267425790200788290265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18100844950526800525526843 27151267425790200788290265)
                ·
                  refine ⟨20363450569342650591217699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27151267425790200788290265 20363450569342650591217699)
                  ·
                    refine ⟨30545175854013975886826549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20363450569342650591217699 30545175854013975886826549)
                    ·
                      refine ⟨2863610236313810239389989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30545175854013975886826549 2863610236313810239389989)
                      ·
                        rfl

theorem cell23_5576861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_5576861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576861 prefixEnd_5576861 := by exact prefixLift 5576861
  have htrace : WordTrace (prefixWord ++ tailWord_5576861) baseStart_5576861 baseEnd_5576861 := by
    simpa [prefixWord, tailWord_5576861, baseEnd_5576861] using wordTrace_append hprefix tailTrace_5576861
  have hstable : (prefixWord ++ tailWord_5576861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576861).length < 2 ^ (prefixWord ++ tailWord_5576861).sum := by decide
  have hdescent : baseEnd_5576861 < baseStart_5576861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576892 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 2, 2, 2]
def baseStart_5576892 : Nat := 118140960795 + 5576892 * 2 ^ 59
def prefixEnd_5576892 : Nat := 4983230072969 + 3 ^ 40 * 5576892 * 2
def baseEnd_5576892 : Nat := 2863626154214099618102347

theorem tailTrace_5576892 : CollatzResearch.WordTrace tailWord_5576892 prefixEnd_5576892 2863626154214099618102347 := by
  unfold tailWord_5576892
  simp only [CollatzResearch.WordTrace]
  refine ⟨101702980855940108084854465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135603974474586810779805953 101702980855940108084854465)
  ·
    refine ⟨76277235641955081063640849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101702980855940108084854465 76277235641955081063640849)
    ·
      refine ⟨57207926731466310797730637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76277235641955081063640849 57207926731466310797730637)
      ·
        refine ⟨21452972524299866549148989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57207926731466310797730637 21452972524299866549148989)
        ·
          refine ⟨8044864696612449955930871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21452972524299866549148989 8044864696612449955930871)
          ·
            refine ⟨12067297044918674933896307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8044864696612449955930871 12067297044918674933896307)
            ·
              refine ⟨18100945567378012400844461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12067297044918674933896307 18100945567378012400844461)
              ·
                refine ⟨6787854587766754650316673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18100945567378012400844461 6787854587766754650316673)
                ·
                  refine ⟨5090890940825065987737505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6787854587766754650316673 5090890940825065987737505)
                  ·
                    refine ⟨3818168205618799490803129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5090890940825065987737505 3818168205618799490803129)
                    ·
                      refine ⟨2863626154214099618102347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818168205618799490803129 2863626154214099618102347)
                      ·
                        rfl

theorem cell23_5576892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_5576892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576892 prefixEnd_5576892 := by exact prefixLift 5576892
  have htrace : WordTrace (prefixWord ++ tailWord_5576892) baseStart_5576892 baseEnd_5576892 := by
    simpa [prefixWord, tailWord_5576892, baseEnd_5576892] using wordTrace_append hprefix tailTrace_5576892
  have hstable : (prefixWord ++ tailWord_5576892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576892).length < 2 ^ (prefixWord ++ tailWord_5576892).sum := by decide
  have hdescent : baseEnd_5576892 < baseStart_5576892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576904 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_5576904 : Nat := 118140960795 + 5576904 * 2 ^ 59
def prefixEnd_5576904 : Nat := 4983230072969 + 3 ^ 40 * 5576904 * 2
def baseEnd_5576904 : Nat := 2863632315981953571152291

theorem tailTrace_5576904 : CollatzResearch.WordTrace tailWord_5576904 prefixEnd_5576904 2863632315981953571152291 := by
  unfold tailWord_5576904
  simp only [CollatzResearch.WordTrace]
  refine ⟨101703199693918371109572883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135604266258557828146097177 101703199693918371109572883)
  ·
    refine ⟨152554799540877556664359325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101703199693918371109572883 152554799540877556664359325)
    ·
      refine ⟨57208049827829083749134747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152554799540877556664359325 57208049827829083749134747)
      ·
        refine ⟨85812074741743625623702121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57208049827829083749134747 85812074741743625623702121)
        ·
          refine ⟨64359056056307719217776591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85812074741743625623702121 64359056056307719217776591)
          ·
            refine ⟨96538584084461578826664887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64359056056307719217776591 96538584084461578826664887)
            ·
              refine ⟨144807876126692368239997331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96538584084461578826664887 144807876126692368239997331)
              ·
                refine ⟨217211814190038552359995997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144807876126692368239997331 217211814190038552359995997)
                ·
                  refine ⟨81454430321264457134998499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 217211814190038552359995997 81454430321264457134998499)
                  ·
                    refine ⟨122181645481896685702497749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81454430321264457134998499 122181645481896685702497749)
                    ·
                      refine ⟨2863632315981953571152291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122181645481896685702497749 2863632315981953571152291)
                      ·
                        rfl

theorem cell23_5576904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_5576904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576904 prefixEnd_5576904 := by exact prefixLift 5576904
  have htrace : WordTrace (prefixWord ++ tailWord_5576904) baseStart_5576904 baseEnd_5576904 := by
    simpa [prefixWord, tailWord_5576904, baseEnd_5576904] using wordTrace_append hprefix tailTrace_5576904
  have hstable : (prefixWord ++ tailWord_5576904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576904).length < 2 ^ (prefixWord ++ tailWord_5576904).sum := by decide
  have hdescent : baseEnd_5576904 < baseStart_5576904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576911 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 2, 5]
def baseStart_5576911 : Nat := 118140960795 + 5576911 * 2 ^ 59
def prefixEnd_5576911 : Nat := 4983230072969 + 3 ^ 40 * 5576911 * 2
def baseEnd_5576911 : Nat := 954545303448845014588253

theorem tailTrace_5576911 : CollatzResearch.WordTrace tailWord_5576911 prefixEnd_5576911 954545303448845014588253 := by
  unfold tailWord_5576911
  simp only [CollatzResearch.WordTrace]
  refine ⟨203406654698811382414650587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135604436465874254943100391 203406654698811382414650587)
  ·
    refine ⟨305109982048217073621975881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203406654698811382414650587 305109982048217073621975881)
    ·
      refine ⟨228832486536162805216481911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305109982048217073621975881 228832486536162805216481911)
      ·
        refine ⟨343248729804244207824722867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228832486536162805216481911 343248729804244207824722867)
        ·
          refine ⟨514873094706366311737084301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343248729804244207824722867 514873094706366311737084301)
          ·
            refine ⟨193077410514887366901406613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 514873094706366311737084301 193077410514887366901406613)
            ·
              refine ⟨9050503617885345323503435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 193077410514887366901406613 9050503617885345323503435)
              ·
                refine ⟨13575755426828017985255153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9050503617885345323503435 13575755426828017985255153)
                ·
                  refine ⟨10181816570121013488941365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13575755426828017985255153 10181816570121013488941365)
                  ·
                    refine ⟨954545303448845014588253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10181816570121013488941365 954545303448845014588253)
                    ·
                      rfl

theorem cell23_5576911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 5].length) (baseStart_5576911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576911 prefixEnd_5576911 := by exact prefixLift 5576911
  have htrace : WordTrace (prefixWord ++ tailWord_5576911) baseStart_5576911 baseEnd_5576911 := by
    simpa [prefixWord, tailWord_5576911, baseEnd_5576911] using wordTrace_append hprefix tailTrace_5576911
  have hstable : (prefixWord ++ tailWord_5576911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576911).length < 2 ^ (prefixWord ++ tailWord_5576911).sum := by decide
  have hdescent : baseEnd_5576911 < baseStart_5576911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576968 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_5576968 : Nat := 118140960795 + 5576968 * 2 ^ 59
def prefixEnd_5576968 : Nat := 4983230072969 + 3 ^ 40 * 5576968 * 2
def baseEnd_5576968 : Nat := 2863665178743841320751997

theorem tailTrace_5576968 : CollatzResearch.WordTrace tailWord_5576968 prefixEnd_5576968 2863665178743841320751997 := by
  unfold tailWord_5576968
  simp only [CollatzResearch.WordTrace]
  refine ⟨101704366829802440574737779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135605822439736587432983705 101704366829802440574737779)
  ·
    refine ⟨152556550244703660862106669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101704366829802440574737779 152556550244703660862106669)
    ·
      refine ⟨57208706341763872823290001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152556550244703660862106669 57208706341763872823290001)
      ·
        refine ⟨42906529756322904617467501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57208706341763872823290001 42906529756322904617467501)
        ·
          refine ⟨16089948658621089231550313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42906529756322904617467501 16089948658621089231550313)
          ·
            refine ⟨12067461493965816923662735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16089948658621089231550313 12067461493965816923662735)
            ·
              refine ⟨18101192240948725385494103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12067461493965816923662735 18101192240948725385494103)
              ·
                refine ⟨27151788361423088078241155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18101192240948725385494103 27151788361423088078241155)
                ·
                  refine ⟨40727682542134632117361733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27151788361423088078241155 40727682542134632117361733)
                  ·
                    refine ⟨7636440476650243522005325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40727682542134632117361733 7636440476650243522005325)
                    ·
                      refine ⟨2863665178743841320751997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7636440476650243522005325 2863665178743841320751997)
                      ·
                        rfl

theorem cell23_5576968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_5576968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576968 prefixEnd_5576968 := by exact prefixLift 5576968
  have htrace : WordTrace (prefixWord ++ tailWord_5576968) baseStart_5576968 baseEnd_5576968 := by
    simpa [prefixWord, tailWord_5576968, baseEnd_5576968] using wordTrace_append hprefix tailTrace_5576968
  have hstable : (prefixWord ++ tailWord_5576968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576968).length < 2 ^ (prefixWord ++ tailWord_5576968).sum := by decide
  have hdescent : baseEnd_5576968 < baseStart_5576968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5576991 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 6]
def baseStart_5576991 : Nat := 118140960795 + 5576991 * 2 ^ 59
def prefixEnd_5576991 : Nat := 4983230072969 + 3 ^ 40 * 5576991 * 2
def baseEnd_5576991 : Nat := 2863676988798894730764391

theorem tailTrace_5576991 : CollatzResearch.WordTrace tailWord_5576991 prefixEnd_5576991 2863676988798894730764391 := by
  unfold tailWord_5576991
  simp only [CollatzResearch.WordTrace]
  refine ⟨203409572538521556077562827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135606381692347704051708551 203409572538521556077562827)
  ·
    refine ⟨305114358807782334116344241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203409572538521556077562827 305114358807782334116344241)
    ·
      refine ⟨228835769105836750587258181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305114358807782334116344241 228835769105836750587258181)
      ·
        refine ⟨42906706707344390735110909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228835769105836750587258181 42906706707344390735110909)
        ·
          refine ⟨16090015015254146525666591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42906706707344390735110909 16090015015254146525666591)
          ·
            refine ⟨24135022522881219788499887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16090015015254146525666591 24135022522881219788499887)
            ·
              refine ⟨36202533784321829682749831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24135022522881219788499887 36202533784321829682749831)
              ·
                refine ⟨54303800676482744524124747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36202533784321829682749831 54303800676482744524124747)
                ·
                  refine ⟨81455701014724116786187121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54303800676482744524124747 81455701014724116786187121)
                  ·
                    refine ⟨61091775761043087589640341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81455701014724116786187121 61091775761043087589640341)
                    ·
                      refine ⟨2863676988798894730764391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61091775761043087589640341 2863676988798894730764391)
                      ·
                        rfl

theorem cell23_5576991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_5576991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5576991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5576991 prefixEnd_5576991 := by exact prefixLift 5576991
  have htrace : WordTrace (prefixWord ++ tailWord_5576991) baseStart_5576991 baseEnd_5576991 := by
    simpa [prefixWord, tailWord_5576991, baseEnd_5576991] using wordTrace_append hprefix tailTrace_5576991
  have hstable : (prefixWord ++ tailWord_5576991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5576991).length < 2 ^ (prefixWord ++ tailWord_5576991).sum := by decide
  have hdescent : baseEnd_5576991 < baseStart_5576991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5576991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577008 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 6, 3, 2]
def baseStart_5577008 : Nat := 118140960795 + 5577008 * 2 ^ 59
def prefixEnd_5577008 : Nat := 4983230072969 + 3 ^ 40 * 5577008 * 2
def baseEnd_5577008 : Nat := 2863685717970021164251813

theorem tailTrace_5577008 : CollatzResearch.WordTrace tailWord_5577008 prefixEnd_5577008 2863685717970021164251813 := by
  unfold tailWord_5577008
  simp only [CollatzResearch.WordTrace]
  refine ⟨101705096289729983990465839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135606795052973311987287785 101705096289729983990465839)
  ·
    refine ⟨152557644434594975985698759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101705096289729983990465839 152557644434594975985698759)
    ·
      refine ⟨228836466651892463978548139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152557644434594975985698759 228836466651892463978548139)
      ·
        refine ⟨343254699977838695967822209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228836466651892463978548139 343254699977838695967822209)
        ·
          refine ⟨257441024983379021975866657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343254699977838695967822209 257441024983379021975866657)
          ·
            refine ⟨193080768737534266481899993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257441024983379021975866657 193080768737534266481899993)
            ·
              refine ⟨144810576553150699861424995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193080768737534266481899993 144810576553150699861424995)
              ·
                refine ⟨217215864829726049792137493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144810576553150699861424995 217215864829726049792137493)
                ·
                  refine ⟨10181993663893408584006445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 217215864829726049792137493 10181993663893408584006445)
                  ·
                    refine ⟨3818247623960028219002417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10181993663893408584006445 3818247623960028219002417)
                    ·
                      refine ⟨2863685717970021164251813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818247623960028219002417 2863685717970021164251813)
                      ·
                        rfl

theorem cell23_5577008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 6, 3, 2].length) (baseStart_5577008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577008 prefixEnd_5577008 := by exact prefixLift 5577008
  have htrace : WordTrace (prefixWord ++ tailWord_5577008) baseStart_5577008 baseEnd_5577008 := by
    simpa [prefixWord, tailWord_5577008, baseEnd_5577008] using wordTrace_append hprefix tailTrace_5577008
  have hstable : (prefixWord ++ tailWord_5577008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577008).length < 2 ^ (prefixWord ++ tailWord_5577008).sum := by decide
  have hdescent : baseEnd_5577008 < baseStart_5577008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577018 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 1, 5]
def baseStart_5577018 : Nat := 118140960795 + 5577018 * 2 ^ 59
def prefixEnd_5577018 : Nat := 4983230072969 + 3 ^ 40 * 5577018 * 2
def baseEnd_5577018 : Nat := 954563617592188708375589

theorem tailTrace_5577018 : CollatzResearch.WordTrace tailWord_5577018 prefixEnd_5577018 954563617592188708375589 := by
  unfold tailWord_5577018
  simp only [CollatzResearch.WordTrace]
  refine ⟨50852639327355934922198927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135607038206282493125863805 50852639327355934922198927)
  ·
    refine ⟨76278958991033902383298391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50852639327355934922198927 76278958991033902383298391)
    ·
      refine ⟨114418438486550853574947587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76278958991033902383298391 114418438486550853574947587)
      ·
        refine ⟨171627657729826280362421381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114418438486550853574947587 171627657729826280362421381)
        ·
          refine ⟨32180185824342427567954009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171627657729826280362421381 32180185824342427567954009)
          ·
            refine ⟨24135139368256820675965507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32180185824342427567954009 24135139368256820675965507)
            ·
              refine ⟨36202709052385231013948261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24135139368256820675965507 36202709052385231013948261)
              ·
                refine ⟨6788007947322230815115299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36202709052385231013948261 6788007947322230815115299)
                ·
                  refine ⟨10182011920983346222672949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6788007947322230815115299 10182011920983346222672949)
                  ·
                    refine ⟨954563617592188708375589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10182011920983346222672949 954563617592188708375589)
                    ·
                      rfl

theorem cell23_5577018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_5577018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577018 prefixEnd_5577018 := by exact prefixLift 5577018
  have htrace : WordTrace (prefixWord ++ tailWord_5577018) baseStart_5577018 baseEnd_5577018 := by
    simpa [prefixWord, tailWord_5577018, baseEnd_5577018] using wordTrace_append hprefix tailTrace_5577018
  have hstable : (prefixWord ++ tailWord_5577018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577018).length < 2 ^ (prefixWord ++ tailWord_5577018).sum := by decide
  have hdescent : baseEnd_5577018 < baseStart_5577018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577031 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 3, 6]
def baseStart_5577031 : Nat := 118140960795 + 5577031 * 2 ^ 59
def prefixEnd_5577031 : Nat := 4983230072969 + 3 ^ 40 * 5577031 * 2
def baseEnd_5577031 : Nat := 954565842675024858088069

theorem tailTrace_5577031 : CollatzResearch.WordTrace tailWord_5577031 prefixEnd_5577031 954565842675024858088069 := by
  unfold tailWord_5577031
  simp only [CollatzResearch.WordTrace]
  refine ⟨203411031458376642909018947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135607354305584428606012631 203411031458376642909018947)
  ·
    refine ⟨305116547187564964363528421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203411031458376642909018947 305116547187564964363528421)
    ·
      refine ⟨57209352597668430818161579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305116547187564964363528421 57209352597668430818161579)
      ·
        refine ⟨85814028896502646227242369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57209352597668430818161579 85814028896502646227242369)
        ·
          refine ⟨64360521672376984670431777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85814028896502646227242369 64360521672376984670431777)
          ·
            refine ⟨48270391254282738502823833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64360521672376984670431777 48270391254282738502823833)
            ·
              refine ⟨36202793440712053877117875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48270391254282738502823833 36202793440712053877117875)
              ·
                refine ⟨54304190161068080815676813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36202793440712053877117875 54304190161068080815676813)
                ·
                  refine ⟨20364071310400530305878805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54304190161068080815676813 20364071310400530305878805)
                  ·
                    refine ⟨954565842675024858088069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20364071310400530305878805 954565842675024858088069)
                    ·
                      rfl

theorem cell23_5577031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_5577031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577031 prefixEnd_5577031 := by exact prefixLift 5577031
  have htrace : WordTrace (prefixWord ++ tailWord_5577031) baseStart_5577031 baseEnd_5577031 := by
    simpa [prefixWord, tailWord_5577031, baseEnd_5577031] using wordTrace_append hprefix tailTrace_5577031
  have hstable : (prefixWord ++ tailWord_5577031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577031).length < 2 ^ (prefixWord ++ tailWord_5577031).sum := by decide
  have hdescent : baseEnd_5577031 < baseStart_5577031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577032 : List Nat := [2, 1, 3, 1, 1, 2, 5, 3, 1, 1, 3]
def baseStart_5577032 : Nat := 118140960795 + 5577032 * 2 ^ 59
def prefixEnd_5577032 : Nat := 4983230072969 + 3 ^ 40 * 5577032 * 2
def baseEnd_5577032 : Nat := 2863698041505729070351703

theorem tailTrace_5577032 : CollatzResearch.WordTrace tailWord_5577032 prefixEnd_5577032 2863698041505729070351703 := by
  unfold tailWord_5577032
  simp only [CollatzResearch.WordTrace]
  refine ⟨101705533965686510039902675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135607378620915346719870233 101705533965686510039902675)
  ·
    refine ⟨152558300948529765059854013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101705533965686510039902675 152558300948529765059854013)
    ·
      refine ⟨57209362855698661897445255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152558300948529765059854013 57209362855698661897445255)
      ·
        refine ⟨85814044283547992846167883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57209362855698661897445255 85814044283547992846167883)
        ·
          refine ⟨128721066425321989269251825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85814044283547992846167883 128721066425321989269251825)
          ·
            refine ⟨96540799818991491951938869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128721066425321989269251825 96540799818991491951938869)
            ·
              refine ⟨9050699983030452370494269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96540799818991491951938869 9050699983030452370494269)
              ·
                refine ⟨3394012493636419638935351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9050699983030452370494269 3394012493636419638935351)
                ·
                  refine ⟨5091018740454629458403027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3394012493636419638935351 5091018740454629458403027)
                  ·
                    refine ⟨7636528110681944187604541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5091018740454629458403027 7636528110681944187604541)
                    ·
                      refine ⟨2863698041505729070351703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7636528110681944187604541 2863698041505729070351703)
                      ·
                        rfl

theorem cell23_5577032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_5577032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577032 prefixEnd_5577032 := by exact prefixLift 5577032
  have htrace : WordTrace (prefixWord ++ tailWord_5577032) baseStart_5577032 baseEnd_5577032 := by
    simpa [prefixWord, tailWord_5577032, baseEnd_5577032] using wordTrace_append hprefix tailTrace_5577032
  have hstable : (prefixWord ++ tailWord_5577032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577032).length < 2 ^ (prefixWord ++ tailWord_5577032).sum := by decide
  have hdescent : baseEnd_5577032 < baseStart_5577032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577061 : List Nat := [1, 3, 1, 3, 1, 3, 1, 10]
def baseStart_5577061 : Nat := 118140960795 + 5577061 * 2 ^ 59
def prefixEnd_5577061 : Nat := 4983230072969 + 3 ^ 40 * 5577061 * 2
def baseEnd_5577061 : Nat := 106063441942396646551447

theorem tailTrace_5577061 : CollatzResearch.WordTrace tailWord_5577061 prefixEnd_5577061 106063441942396646551447 := by
  unfold tailWord_5577061
  simp only [CollatzResearch.WordTrace]
  refine ⟨203412125648267958032611037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135608083765511972021740691 203412125648267958032611037)
  ·
    refine ⟨76279547118100484262229139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203412125648267958032611037 76279547118100484262229139)
    ·
      refine ⟨114419320677150726393343709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76279547118100484262229139 114419320677150726393343709)
      ·
        refine ⟨42907245253931522397503891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114419320677150726393343709 42907245253931522397503891)
        ·
          refine ⟨64360867880897283596255837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42907245253931522397503891 64360867880897283596255837)
          ·
            refine ⟨24135325455336481348595939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64360867880897283596255837 24135325455336481348595939)
            ·
              refine ⟨36202988183004722022893909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24135325455336481348595939 36202988183004722022893909)
              ·
                refine ⟨106063441942396646551447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36202988183004722022893909 106063441942396646551447)
                ·
                  rfl

theorem cell23_5577061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 10].length) (baseStart_5577061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577061 prefixEnd_5577061 := by exact prefixLift 5577061
  have htrace : WordTrace (prefixWord ++ tailWord_5577061) baseStart_5577061 baseEnd_5577061 := by
    simpa [prefixWord, tailWord_5577061, baseEnd_5577061] using wordTrace_append hprefix tailTrace_5577061
  have hstable : (prefixWord ++ tailWord_5577061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577061).length < 2 ^ (prefixWord ++ tailWord_5577061).sum := by decide
  have hdescent : baseEnd_5577061 < baseStart_5577061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577092 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_5577092 : Nat := 118140960795 + 5577092 * 2 ^ 59
def prefixEnd_5577092 : Nat := 4983230072969 + 3 ^ 40 * 5577092 * 2
def baseEnd_5577092 : Nat := 2863728850344998835601427

theorem tailTrace_5577092 : CollatzResearch.WordTrace tailWord_5577092 prefixEnd_5577092 2863728850344998835601427 := by
  unfold tailWord_5577092
  simp only [CollatzResearch.WordTrace]
  refine ⟨101706628155577825163494765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135608837540770433551326353 101706628155577825163494765)
  ·
    refine ⟨38139985558341684436310537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101706628155577825163494765 38139985558341684436310537)
    ·
      refine ⟨28604989168756263327232903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38139985558341684436310537 28604989168756263327232903)
      ·
        refine ⟨42907483753134394990849355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28604989168756263327232903 42907483753134394990849355)
        ·
          refine ⟨64361225629701592486274033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42907483753134394990849355 64361225629701592486274033)
          ·
            refine ⟨48270919222276194364705525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64361225629701592486274033 48270919222276194364705525)
            ·
              refine ⟨4525398677088393221691143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48270919222276194364705525 4525398677088393221691143)
              ·
                refine ⟨6788098015632589832536715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525398677088393221691143 6788098015632589832536715)
                ·
                  refine ⟨10182147023448884748805073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6788098015632589832536715 10182147023448884748805073)
                  ·
                    refine ⟨7636610267586663561603805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10182147023448884748805073 7636610267586663561603805)
                    ·
                      refine ⟨2863728850344998835601427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7636610267586663561603805 2863728850344998835601427)
                      ·
                        rfl

theorem cell23_5577092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_5577092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577092 prefixEnd_5577092 := by exact prefixLift 5577092
  have htrace : WordTrace (prefixWord ++ tailWord_5577092) baseStart_5577092 baseEnd_5577092 := by
    simpa [prefixWord, tailWord_5577092, baseEnd_5577092] using wordTrace_append hprefix tailTrace_5577092
  have hstable : (prefixWord ++ tailWord_5577092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577092).length < 2 ^ (prefixWord ++ tailWord_5577092).sum := by decide
  have hdescent : baseEnd_5577092 < baseStart_5577092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577122 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_5577122 : Nat := 118140960795 + 5577122 * 2 ^ 59
def prefixEnd_5577122 : Nat := 4983230072969 + 3 ^ 40 * 5577122 * 2
def baseEnd_5577122 : Nat := 2863744254764633718226289

theorem tailTrace_5577122 : CollatzResearch.WordTrace tailWord_5577122 prefixEnd_5577122 2863744254764633718226289 := by
  unfold tailWord_5577122
  simp only [CollatzResearch.WordTrace]
  refine ⟨50853587625261741362645405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135609567000697976967054413 50853587625261741362645405)
  ·
    refine ⟨19070095359473153010992027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50853587625261741362645405 19070095359473153010992027)
    ·
      refine ⟨28605143039209729516488041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19070095359473153010992027 28605143039209729516488041)
      ·
        refine ⟨21453857279407297137366031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28605143039209729516488041 21453857279407297137366031)
        ·
          refine ⟨32180785919110945706049047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21453857279407297137366031 32180785919110945706049047)
          ·
            refine ⟨48271178878666418559073571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32180785919110945706049047 48271178878666418559073571)
            ·
              refine ⟨72406768317999627838610357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48271178878666418559073571 72406768317999627838610357)
              ·
                refine ⟨6788134529812465109869721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72406768317999627838610357 6788134529812465109869721)
                ·
                  refine ⟨5091100897359348832402291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6788134529812465109869721 5091100897359348832402291)
                  ·
                    refine ⟨7636651346039023248603437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5091100897359348832402291 7636651346039023248603437)
                    ·
                      refine ⟨2863744254764633718226289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7636651346039023248603437 2863744254764633718226289)
                      ·
                        rfl

theorem cell23_5577122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_5577122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577122 prefixEnd_5577122 := by exact prefixLift 5577122
  have htrace : WordTrace (prefixWord ++ tailWord_5577122) baseStart_5577122 baseEnd_5577122 := by
    simpa [prefixWord, tailWord_5577122, baseEnd_5577122] using wordTrace_append hprefix tailTrace_5577122
  have hstable : (prefixWord ++ tailWord_5577122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577122).length < 2 ^ (prefixWord ++ tailWord_5577122).sum := by decide
  have hdescent : baseEnd_5577122 < baseStart_5577122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577140 : List Nat := [2, 5, 2, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_5577140 : Nat := 118140960795 + 5577140 * 2 ^ 59
def prefixEnd_5577140 : Nat := 4983230072969 + 3 ^ 40 * 5577140 * 2
def baseEnd_5577140 : Nat := 2863753497416414647801207

theorem tailTrace_5577140 : CollatzResearch.WordTrace tailWord_5577140 prefixEnd_5577140 2863753497416414647801207 := by
  unfold tailWord_5577140
  simp only [CollatzResearch.WordTrace]
  refine ⟨101707503507490877262368437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135610004676654503016491249 101707503507490877262368437)
  ·
    refine ⟨9535078453827269743347041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101707503507490877262368437 9535078453827269743347041)
    ·
      refine ⟨7151308840370452307510281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9535078453827269743347041 7151308840370452307510281)
      ·
        refine ⟨5363481630277839230632711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7151308840370452307510281 5363481630277839230632711)
        ·
          refine ⟨8045222445416758845949067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363481630277839230632711 8045222445416758845949067)
          ·
            refine ⟨12067833668125138268923601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8045222445416758845949067 12067833668125138268923601)
            ·
              refine ⟨9050875251093853701692701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12067833668125138268923601 9050875251093853701692701)
              ·
                refine ⟨3394078219160195138134763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9050875251093853701692701 3394078219160195138134763)
                ·
                  refine ⟨5091117328740292707202145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3394078219160195138134763 5091117328740292707202145)
                  ·
                    refine ⟨3818337996555219530401609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5091117328740292707202145 3818337996555219530401609)
                    ·
                      refine ⟨2863753497416414647801207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818337996555219530401609 2863753497416414647801207)
                      ·
                        rfl

theorem cell23_5577140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_5577140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577140 prefixEnd_5577140 := by exact prefixLift 5577140
  have htrace : WordTrace (prefixWord ++ tailWord_5577140) baseStart_5577140 baseEnd_5577140 := by
    simpa [prefixWord, tailWord_5577140, baseEnd_5577140] using wordTrace_append hprefix tailTrace_5577140
  have hstable : (prefixWord ++ tailWord_5577140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577140).length < 2 ^ (prefixWord ++ tailWord_5577140).sum := by decide
  have hdescent : baseEnd_5577140 < baseStart_5577140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577149 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 1, 3, 2]
def baseStart_5577149 : Nat := 118140960795 + 5577149 * 2 ^ 59
def prefixEnd_5577149 : Nat := 4983230072969 + 3 ^ 40 * 5577149 * 2
def baseEnd_5577149 : Nat := 2863758118742305112588665

theorem tailTrace_5577149 : CollatzResearch.WordTrace tailWord_5577149 prefixEnd_5577149 2863758118742305112588665 := by
  unfold tailWord_5577149
  simp only [CollatzResearch.WordTrace]
  refine ⟨203415335271949149061814501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135610223514632766041209667 203415335271949149061814501)
  ·
    refine ⟨38140375363490465449090219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203415335271949149061814501 38140375363490465449090219)
    ·
      refine ⟨57210563045235698173635329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38140375363490465449090219 57210563045235698173635329)
      ·
        refine ⟨42907922283926773630226497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57210563045235698173635329 42907922283926773630226497)
        ·
          refine ⟨32180941712945080222669873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42907922283926773630226497 32180941712945080222669873)
          ·
            refine ⟨24135706284708810167002405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32180941712945080222669873 24135706284708810167002405)
            ·
              refine ⟨4525444928382901906312951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24135706284708810167002405 4525444928382901906312951)
              ·
                refine ⟨6788167392574352859469427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525444928382901906312951 6788167392574352859469427)
                ·
                  refine ⟨10182251088861529289204141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6788167392574352859469427 10182251088861529289204141)
                  ·
                    refine ⟨3818344158323073483451553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10182251088861529289204141 3818344158323073483451553)
                    ·
                      refine ⟨2863758118742305112588665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818344158323073483451553 2863758118742305112588665)
                      ·
                        rfl

theorem cell23_5577149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_5577149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577149 prefixEnd_5577149 := by exact prefixLift 5577149
  have htrace : WordTrace (prefixWord ++ tailWord_5577149) baseStart_5577149 baseEnd_5577149 := by
    simpa [prefixWord, tailWord_5577149, baseEnd_5577149] using wordTrace_append hprefix tailTrace_5577149
  have hstable : (prefixWord ++ tailWord_5577149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577149).length < 2 ^ (prefixWord ++ tailWord_5577149).sum := by decide
  have hdescent : baseEnd_5577149 < baseStart_5577149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577156 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_5577156 : Nat := 118140960795 + 5577156 * 2 ^ 59
def prefixEnd_5577156 : Nat := 4983230072969 + 3 ^ 40 * 5577156 * 2
def baseEnd_5577156 : Nat := 2863761713106886585201133

theorem tailTrace_5577156 : CollatzResearch.WordTrace tailWord_5577156 prefixEnd_5577156 2863761713106886585201133 := by
  unfold tailWord_5577156
  simp only [CollatzResearch.WordTrace]
  refine ⟨101707795291461894628659661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135610393721949192838212881 101707795291461894628659661)
  ·
    refine ⟨38140423234298210485747373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101707795291461894628659661 38140423234298210485747373)
    ·
      refine ⟨14302658712861828932155265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38140423234298210485747373 14302658712861828932155265)
      ·
        refine ⟨10726994034646371699116449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14302658712861828932155265 10726994034646371699116449)
        ·
          refine ⟨8045245525984778774337337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10726994034646371699116449 8045245525984778774337337)
          ·
            refine ⟨6033934144488584080753003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8045245525984778774337337 6033934144488584080753003)
            ·
              refine ⟨9050901216732876121129505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6033934144488584080753003 9050901216732876121129505)
              ·
                refine ⟨6788175912549657090847129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9050901216732876121129505 6788175912549657090847129)
                ·
                  refine ⟨5091131934412242818135347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6788175912549657090847129 5091131934412242818135347)
                  ·
                    refine ⟨7636697901618364227203021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5091131934412242818135347 7636697901618364227203021)
                    ·
                      refine ⟨2863761713106886585201133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7636697901618364227203021 2863761713106886585201133)
                      ·
                        rfl

theorem cell23_5577156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_5577156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577156 prefixEnd_5577156 := by exact prefixLift 5577156
  have htrace : WordTrace (prefixWord ++ tailWord_5577156) baseStart_5577156 baseEnd_5577156 := by
    simpa [prefixWord, tailWord_5577156, baseEnd_5577156] using wordTrace_append hprefix tailTrace_5577156
  have hstable : (prefixWord ++ tailWord_5577156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577156).length < 2 ^ (prefixWord ++ tailWord_5577156).sum := by decide
  have hdescent : baseEnd_5577156 < baseStart_5577156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577162 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2]
def baseStart_5577162 : Nat := 118140960795 + 5577162 * 2 ^ 59
def prefixEnd_5577162 : Nat := 4983230072969 + 3 ^ 40 * 5577162 * 2
def baseEnd_5577162 : Nat := 2863764793990813561726105

theorem tailTrace_5577162 : CollatzResearch.WordTrace tailWord_5577162 prefixEnd_5577162 2863764793990813561726105 := by
  unfold tailWord_5577162
  simp only [CollatzResearch.WordTrace]
  refine ⟨50853952355225513070509435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135610539613934701521358493 50853952355225513070509435)
  ·
    refine ⟨76280928532838269605764153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50853952355225513070509435 76280928532838269605764153)
    ·
      refine ⟨57210696399628702204323115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76280928532838269605764153 57210696399628702204323115)
      ·
        refine ⟨85816044599443053306484673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57210696399628702204323115 85816044599443053306484673)
        ·
          refine ⟨64362033449582289979863505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85816044599443053306484673 64362033449582289979863505)
          ·
            refine ⟨48271525087186717484897629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64362033449582289979863505 48271525087186717484897629)
            ·
              refine ⟨18101821907695019056836611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48271525087186717484897629 18101821907695019056836611)
              ·
                refine ⟨27152732861542528585254917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18101821907695019056836611 27152732861542528585254917)
                ·
                  refine ⟨5091137411539224109735297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27152732861542528585254917 5091137411539224109735297)
                  ·
                    refine ⟨3818353058654418082301473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5091137411539224109735297 3818353058654418082301473)
                    ·
                      refine ⟨2863764793990813561726105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818353058654418082301473 2863764793990813561726105)
                      ·
                        rfl

theorem cell23_5577162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_5577162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577162 prefixEnd_5577162 := by exact prefixLift 5577162
  have htrace : WordTrace (prefixWord ++ tailWord_5577162) baseStart_5577162 baseEnd_5577162 := by
    simpa [prefixWord, tailWord_5577162, baseEnd_5577162] using wordTrace_append hprefix tailTrace_5577162
  have hstable : (prefixWord ++ tailWord_5577162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577162).length < 2 ^ (prefixWord ++ tailWord_5577162).sum := by decide
  have hdescent : baseEnd_5577162 < baseStart_5577162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577208 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_5577208 : Nat := 118140960795 + 5577208 * 2 ^ 59
def prefixEnd_5577208 : Nat := 4983230072969 + 3 ^ 40 * 5577208 * 2
def baseEnd_5577208 : Nat := 2863788414100920381750893

theorem tailTrace_5577208 : CollatzResearch.WordTrace tailWord_5577208 prefixEnd_5577208 2863788414100920381750893 := by
  unfold tailWord_5577208
  simp only [CollatzResearch.WordTrace]
  refine ⟨101708743589367701069106139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135611658119156934758808185 101708743589367701069106139)
  ·
    refine ⟨152563115384051551603659209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101708743589367701069106139 152563115384051551603659209)
    ·
      refine ⟨114422336538038663702744407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152563115384051551603659209 114422336538038663702744407)
      ·
        refine ⟨171633504807057995554116611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114422336538038663702744407 171633504807057995554116611)
        ·
          refine ⟨257450257210586993331174917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171633504807057995554116611 257450257210586993331174917)
          ·
            refine ⟨48271923226985061249595297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257450257210586993331174917 48271923226985061249595297)
            ·
              refine ⟨36203942420238795937196473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48271923226985061249595297 36203942420238795937196473)
              ·
                refine ⟨27152956815179096952897355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36203942420238795937196473 27152956815179096952897355)
                ·
                  refine ⟨40729435222768645429346033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27152956815179096952897355 40729435222768645429346033)
                  ·
                    refine ⟨30547076417076484072009525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40729435222768645429346033 30547076417076484072009525)
                    ·
                      refine ⟨2863788414100920381750893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30547076417076484072009525 2863788414100920381750893)
                      ·
                        rfl

theorem cell23_5577208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_5577208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577208 prefixEnd_5577208 := by exact prefixLift 5577208
  have htrace : WordTrace (prefixWord ++ tailWord_5577208) baseStart_5577208 baseEnd_5577208 := by
    simpa [prefixWord, tailWord_5577208, baseEnd_5577208] using wordTrace_append hprefix tailTrace_5577208
  have hstable : (prefixWord ++ tailWord_5577208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577208).length < 2 ^ (prefixWord ++ tailWord_5577208).sum := by decide
  have hdescent : baseEnd_5577208 < baseStart_5577208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577235 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 1, 6, 2]
def baseStart_5577235 : Nat := 118140960795 + 5577235 * 2 ^ 59
def prefixEnd_5577235 : Nat := 4983230072969 + 3 ^ 40 * 5577235 * 2
def baseEnd_5577235 : Nat := 2863802278078591776113269

theorem tailTrace_5577235 : CollatzResearch.WordTrace tailWord_5577235 prefixEnd_5577235 2863802278078591776113269 := by
  unfold tailWord_5577235
  simp only [CollatzResearch.WordTrace]
  refine ⟨203418471949637585749445159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135612314633091723832963439 203418471949637585749445159)
  ·
    refine ⟨305127707924456378624167739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203418471949637585749445159 305127707924456378624167739)
    ·
      refine ⟨457691561886684567936251609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305127707924456378624167739 457691561886684567936251609)
      ·
        refine ⟨343268671415013425952188707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457691561886684567936251609 343268671415013425952188707)
        ·
          refine ⟨514903007122520138928283061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343268671415013425952188707 514903007122520138928283061)
          ·
            refine ⟨48272156917736263024526537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 514903007122520138928283061 48272156917736263024526537)
            ·
              refine ⟨36204117688302197268394903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48272156917736263024526537 36204117688302197268394903)
              ·
                refine ⟨54306176532453295902592355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36204117688302197268394903 54306176532453295902592355)
                ·
                  refine ⟨81459264798679943853888533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54306176532453295902592355 81459264798679943853888533)
                  ·
                    refine ⟨3818403037438122368151025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81459264798679943853888533 3818403037438122368151025)
                    ·
                      refine ⟨2863802278078591776113269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818403037438122368151025 2863802278078591776113269)
                      ·
                        rfl

theorem cell23_5577235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 6, 2].length) (baseStart_5577235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577235 prefixEnd_5577235 := by exact prefixLift 5577235
  have htrace : WordTrace (prefixWord ++ tailWord_5577235) baseStart_5577235 baseEnd_5577235 := by
    simpa [prefixWord, tailWord_5577235, baseEnd_5577235] using wordTrace_append hprefix tailTrace_5577235
  have hstable : (prefixWord ++ tailWord_5577235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577235).length < 2 ^ (prefixWord ++ tailWord_5577235).sum := by decide
  have hdescent : baseEnd_5577235 < baseStart_5577235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577286 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_5577286 : Nat := 118140960795 + 5577286 * 2 ^ 59
def prefixEnd_5577286 : Nat := 4983230072969 + 3 ^ 40 * 5577286 * 2
def baseEnd_5577286 : Nat := 2863828465591971076575535

theorem tailTrace_5577286 : CollatzResearch.WordTrace tailWord_5577286 prefixEnd_5577286 2863828465591971076575535 := by
  unfold tailWord_5577286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6356885377264150670610991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135613554714968547639701141 6356885377264150670610991)
  ·
    refine ⟨9535328065896226005916487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6356885377264150670610991 9535328065896226005916487)
    ·
      refine ⟨14302992098844339008874731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9535328065896226005916487 14302992098844339008874731)
      ·
        refine ⟨21454488148266508513312097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14302992098844339008874731 21454488148266508513312097)
        ·
          refine ⟨16090866111199881384984073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21454488148266508513312097 16090866111199881384984073)
          ·
            refine ⟨12068149583399911038738055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16090866111199881384984073 12068149583399911038738055)
            ·
              refine ⟨18102224375099866558107083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12068149583399911038738055 18102224375099866558107083)
              ·
                refine ⟨27153336562649799837160625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18102224375099866558107083 27153336562649799837160625)
                ·
                  refine ⟨20365002421987349877870469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27153336562649799837160625 20365002421987349877870469)
                  ·
                    refine ⟨3818437954122628102100713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20365002421987349877870469 3818437954122628102100713)
                    ·
                      refine ⟨2863828465591971076575535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818437954122628102100713 2863828465591971076575535)
                      ·
                        rfl

theorem cell23_5577286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_5577286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577286 prefixEnd_5577286 := by exact prefixLift 5577286
  have htrace : WordTrace (prefixWord ++ tailWord_5577286) baseStart_5577286 baseEnd_5577286 := by
    simpa [prefixWord, tailWord_5577286, baseEnd_5577286] using wordTrace_append hprefix tailTrace_5577286
  have hstable : (prefixWord ++ tailWord_5577286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577286).length < 2 ^ (prefixWord ++ tailWord_5577286).sum := by decide
  have hdescent : baseEnd_5577286 < baseStart_5577286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577322 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 1, 5]
def baseStart_5577322 : Nat := 118140960795 + 5577322 * 2 ^ 59
def prefixEnd_5577322 : Nat := 4983230072969 + 3 ^ 40 * 5577322 * 2
def baseEnd_5577322 : Nat := 954615650298510978575123

theorem tailTrace_5577322 : CollatzResearch.WordTrace tailWord_5577322 prefixEnd_5577322 954615650298510978575123 := by
  unfold tailWord_5577322
  simp only [CollatzResearch.WordTrace]
  refine ⟨50855411275080599901965555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135614430066881599738574813 50855411275080599901965555)
  ·
    refine ⟨76283116912620899852948333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50855411275080599901965555 76283116912620899852948333)
    ·
      refine ⟨28606168842232837444855625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76283116912620899852948333 28606168842232837444855625)
      ·
        refine ⟨21454626631674628083641719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28606168842232837444855625 21454626631674628083641719)
        ·
          refine ⟨32181939947511942125462579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21454626631674628083641719 32181939947511942125462579)
          ·
            refine ⟨48272909921267913188193869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32181939947511942125462579 48272909921267913188193869)
            ·
              refine ⟨18102341220475467445572701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48272909921267913188193869 18102341220475467445572701)
              ·
                refine ⟨6788377957678300292089763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18102341220475467445572701 6788377957678300292089763)
                ·
                  refine ⟨10182566936517450438134645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6788377957678300292089763 10182566936517450438134645)
                  ·
                    refine ⟨954615650298510978575123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10182566936517450438134645 954615650298510978575123)
                    ·
                      rfl

theorem cell23_5577322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_5577322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577322 prefixEnd_5577322 := by exact prefixLift 5577322
  have htrace : WordTrace (prefixWord ++ tailWord_5577322) baseStart_5577322 baseEnd_5577322 := by
    simpa [prefixWord, tailWord_5577322, baseEnd_5577322] using wordTrace_append hprefix tailTrace_5577322
  have hstable : (prefixWord ++ tailWord_5577322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577322).length < 2 ^ (prefixWord ++ tailWord_5577322).sum := by decide
  have hdescent : baseEnd_5577322 < baseStart_5577322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577355 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 4]
def baseStart_5577355 : Nat := 118140960795 + 5577355 * 2 ^ 59
def prefixEnd_5577355 : Nat := 4983230072969 + 3 ^ 40 * 5577355 * 2
def baseEnd_5577355 : Nat := 2863863895757131306612717

theorem tailTrace_5577355 : CollatzResearch.WordTrace tailWord_5577355 prefixEnd_5577355 2863863895757131306612717 := by
  unfold tailWord_5577355
  simp only [CollatzResearch.WordTrace]
  refine ⟨203422848709202846243813519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135615232472801897495875679 203422848709202846243813519)
  ·
    refine ⟨305134273063804269365720279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203422848709202846243813519 305134273063804269365720279)
    ·
      refine ⟨457701409595706404048580419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305134273063804269365720279 457701409595706404048580419)
      ·
        refine ⟨686552114393559606072870629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457701409595706404048580419 686552114393559606072870629)
        ·
          refine ⟨128728521448792426138663243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 686552114393559606072870629 128728521448792426138663243)
          ·
            refine ⟨193092782173188639207994865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128728521448792426138663243 193092782173188639207994865)
            ·
              refine ⟨144819586629891479405996149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193092782173188639207994865 144819586629891479405996149)
              ·
                refine ⟨13576836246552326194312139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144819586629891479405996149 13576836246552326194312139)
                ·
                  refine ⟨20365254369828489291468209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13576836246552326194312139 20365254369828489291468209)
                  ·
                    refine ⟨15273940777371366968601157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20365254369828489291468209 15273940777371366968601157)
                    ·
                      refine ⟨2863863895757131306612717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15273940777371366968601157 2863863895757131306612717)
                      ·
                        rfl

theorem cell23_5577355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 4].length) (baseStart_5577355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577355 prefixEnd_5577355 := by exact prefixLift 5577355
  have htrace : WordTrace (prefixWord ++ tailWord_5577355) baseStart_5577355 baseEnd_5577355 := by
    simpa [prefixWord, tailWord_5577355, baseEnd_5577355] using wordTrace_append hprefix tailTrace_5577355
  have hstable : (prefixWord ++ tailWord_5577355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577355).length < 2 ^ (prefixWord ++ tailWord_5577355).sum := by decide
  have hdescent : baseEnd_5577355 < baseStart_5577355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577370 : List Nat := [3, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3]
def baseStart_5577370 : Nat := 118140960795 + 5577370 * 2 ^ 59
def prefixEnd_5577370 : Nat := 4983230072969 + 3 ^ 40 * 5577370 * 2
def baseEnd_5577370 : Nat := 2863871597966948747925149

theorem tailTrace_5577370 : CollatzResearch.WordTrace tailWord_5577370 prefixEnd_5577370 2863871597966948747925149 := by
  unfold tailWord_5577370
  simp only [CollatzResearch.WordTrace]
  refine ⟨50855848951037125951402391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135615597202765669203739709 50855848951037125951402391)
  ·
    refine ⟨76283773426555688927103587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50855848951037125951402391 76283773426555688927103587)
    ·
      refine ⟨114425660139833533390655381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76283773426555688927103587 114425660139833533390655381)
      ·
        refine ⟨5363702819054696877686971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114425660139833533390655381 5363702819054696877686971)
        ·
          refine ⟨8045554228582045316530457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363702819054696877686971 8045554228582045316530457)
          ·
            refine ⟨6034165671436533987397843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8045554228582045316530457 6034165671436533987397843)
            ·
              refine ⟨9051248507154800981096765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034165671436533987397843 9051248507154800981096765)
              ·
                refine ⟨3394218190183050367911287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9051248507154800981096765 3394218190183050367911287)
                ·
                  refine ⟨5091327285274575551866931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3394218190183050367911287 5091327285274575551866931)
                  ·
                    refine ⟨7636990927911863327800397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5091327285274575551866931 7636990927911863327800397)
                    ·
                      refine ⟨2863871597966948747925149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7636990927911863327800397 2863871597966948747925149)
                      ·
                        rfl

theorem cell23_5577370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_5577370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577370 prefixEnd_5577370 := by exact prefixLift 5577370
  have htrace : WordTrace (prefixWord ++ tailWord_5577370) baseStart_5577370 baseEnd_5577370 := by
    simpa [prefixWord, tailWord_5577370, baseEnd_5577370] using wordTrace_append hprefix tailTrace_5577370
  have hstable : (prefixWord ++ tailWord_5577370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577370).length < 2 ^ (prefixWord ++ tailWord_5577370).sum := by decide
  have hdescent : baseEnd_5577370 < baseStart_5577370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577415 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_5577415 : Nat := 118140960795 + 5577415 * 2 ^ 59
def prefixEnd_5577415 : Nat := 4983230072969 + 3 ^ 40 * 5577415 * 2
def baseEnd_5577415 : Nat := 2863894704596401071862441

theorem tailTrace_5577415 : CollatzResearch.WordTrace tailWord_5577415 prefixEnd_5577415 2863894704596401071862441 := by
  unfold tailWord_5577415
  simp only [CollatzResearch.WordTrace]
  refine ⟨203425037088985476490997699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135616691392656984327331799 203425037088985476490997699)
  ·
    refine ⟨305137555633478214736496549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203425037088985476490997699 305137555633478214736496549)
    ·
      refine ⟨57213291681277165263093103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305137555633478214736496549 57213291681277165263093103)
      ·
        refine ⟨85819937521915747894639655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57213291681277165263093103 85819937521915747894639655)
        ·
          refine ⟨128729906282873621841959483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85819937521915747894639655 128729906282873621841959483)
          ·
            refine ⟨193094859424310432762939225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128729906282873621841959483 193094859424310432762939225)
            ·
              refine ⟨144821144568232824572204419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193094859424310432762939225 144821144568232824572204419)
              ·
                refine ⟨217231716852349236858306629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144821144568232824572204419 217231716852349236858306629)
                ·
                  refine ⟨40730946909815481910932493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 217231716852349236858306629 40730946909815481910932493)
                  ·
                    refine ⟨15274105091180805716599685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40730946909815481910932493 15274105091180805716599685)
                    ·
                      refine ⟨2863894704596401071862441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15274105091180805716599685 2863894704596401071862441)
                      ·
                        rfl

theorem cell23_5577415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_5577415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577415 prefixEnd_5577415 := by exact prefixLift 5577415
  have htrace : WordTrace (prefixWord ++ tailWord_5577415) baseStart_5577415 baseEnd_5577415 := by
    simpa [prefixWord, tailWord_5577415, baseEnd_5577415] using wordTrace_append hprefix tailTrace_5577415
  have hstable : (prefixWord ++ tailWord_5577415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577415).length < 2 ^ (prefixWord ++ tailWord_5577415).sum := by decide
  have hdescent : baseEnd_5577415 < baseStart_5577415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577449 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 4, 2, 2]
def baseStart_5577449 : Nat := 118140960795 + 5577449 * 2 ^ 59
def prefixEnd_5577449 : Nat := 4983230072969 + 3 ^ 40 * 5577449 * 2
def baseEnd_5577449 : Nat := 2863912162938653938837285

theorem tailTrace_5577449 : CollatzResearch.WordTrace tailWord_5577449 prefixEnd_5577449 2863912162938653938837285 := by
  unfold tailWord_5577449
  simp only [CollatzResearch.WordTrace]
  refine ⟨203426277170862300297735401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135617518113908200198490267 203426277170862300297735401)
  ·
    refine ⟨152569707878146725223301551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203426277170862300297735401 152569707878146725223301551)
    ·
      refine ⟨228854561817220087834952327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152569707878146725223301551 228854561817220087834952327)
      ·
        refine ⟨343281842725830131752428491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228854561817220087834952327 343281842725830131752428491)
        ·
          refine ⟨514922764088745197628642737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343281842725830131752428491 514922764088745197628642737)
          ·
            refine ⟨386192073066558898221482053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514922764088745197628642737 386192073066558898221482053)
            ·
              refine ⟨72411013699979793416527885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 386192073066558898221482053 72411013699979793416527885)
              ·
                refine ⟨27154130137492422531197957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72411013699979793416527885 27154130137492422531197957)
                ·
                  refine ⟨5091399400779829224599617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27154130137492422531197957 5091399400779829224599617)
                  ·
                    refine ⟨3818549550584871918449713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5091399400779829224599617 3818549550584871918449713)
                    ·
                      refine ⟨2863912162938653938837285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818549550584871918449713 2863912162938653938837285)
                      ·
                        rfl

theorem cell23_5577449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 4, 2, 2].length) (baseStart_5577449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577449 prefixEnd_5577449 := by exact prefixLift 5577449
  have htrace : WordTrace (prefixWord ++ tailWord_5577449) baseStart_5577449 baseEnd_5577449 := by
    simpa [prefixWord, tailWord_5577449, baseEnd_5577449] using wordTrace_append hprefix tailTrace_5577449
  have hstable : (prefixWord ++ tailWord_5577449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577449).length < 2 ^ (prefixWord ++ tailWord_5577449).sum := by decide
  have hdescent : baseEnd_5577449 < baseStart_5577449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577466 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2]
def baseStart_5577466 : Nat := 118140960795 + 5577466 * 2 ^ 59
def prefixEnd_5577466 : Nat := 4983230072969 + 3 ^ 40 * 5577466 * 2
def baseEnd_5577466 : Nat := 2863920892109780372324707

theorem tailTrace_5577466 : CollatzResearch.WordTrace tailWord_5577466 prefixEnd_5577466 2863920892109780372324707 := by
  unfold tailWord_5577466
  simp only [CollatzResearch.WordTrace]
  refine ⟨50856724302950178050276063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135617931474533808134069501 50856724302950178050276063)
  ·
    refine ⟨76285086454425267075414095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50856724302950178050276063 76285086454425267075414095)
    ·
      refine ⟨114427629681637900613121143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76285086454425267075414095 114427629681637900613121143)
      ·
        refine ⟨171641444522456850919681715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114427629681637900613121143 171641444522456850919681715)
        ·
          refine ⟨257462166783685276379522573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171641444522456850919681715 257462166783685276379522573)
          ·
            refine ⟨96548312543881978642320965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257462166783685276379522573 96548312543881978642320965)
            ·
              refine ⟨18102808601977870995435181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96548312543881978642320965 18102808601977870995435181)
              ·
                refine ⟨6788553225741701623288193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18102808601977870995435181 6788553225741701623288193)
                ·
                  refine ⟨5091414919306276217466145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6788553225741701623288193 5091414919306276217466145)
                  ·
                    refine ⟨3818561189479707163099609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5091414919306276217466145 3818561189479707163099609)
                    ·
                      refine ⟨2863920892109780372324707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818561189479707163099609 2863920892109780372324707)
                      ·
                        rfl

theorem cell23_5577466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2].length) (baseStart_5577466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577466 prefixEnd_5577466 := by exact prefixLift 5577466
  have htrace : WordTrace (prefixWord ++ tailWord_5577466) baseStart_5577466 baseEnd_5577466 := by
    simpa [prefixWord, tailWord_5577466, baseEnd_5577466] using wordTrace_append hprefix tailTrace_5577466
  have hstable : (prefixWord ++ tailWord_5577466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577466).length < 2 ^ (prefixWord ++ tailWord_5577466).sum := by decide
  have hdescent : baseEnd_5577466 < baseStart_5577466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577482 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_5577482 : Nat := 118140960795 + 5577482 * 2 ^ 59
def prefixEnd_5577482 : Nat := 4983230072969 + 3 ^ 40 * 5577482 * 2
def baseEnd_5577482 : Nat := 2863929107800252309724633

theorem tailTrace_5577482 : CollatzResearch.WordTrace tailWord_5577482 prefixEnd_5577482 2863929107800252309724633 := by
  unfold tailWord_5577482
  simp only [CollatzResearch.WordTrace]
  refine ⟨50856870194935686733421675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135618320519828497955791133 50856870194935686733421675)
  ·
    refine ⟨76285305292403530100132513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50856870194935686733421675 76285305292403530100132513)
    ·
      refine ⟨57213978969302647575099385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76285305292403530100132513 57213978969302647575099385)
      ·
        refine ⟨42910484226976985681324539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57213978969302647575099385 42910484226976985681324539)
        ·
          refine ⟨64365726340465478521986809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42910484226976985681324539 64365726340465478521986809)
          ·
            refine ⟨48274294755349108891490107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64365726340465478521986809 48274294755349108891490107)
            ·
              refine ⟨72411442133023663337235161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48274294755349108891490107 72411442133023663337235161)
              ·
                refine ⟨54308581599767747502926371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72411442133023663337235161 54308581599767747502926371)
                ·
                  refine ⟨81462872399651621254389557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54308581599767747502926371 81462872399651621254389557)
                  ·
                    refine ⟨7637144287467339492599021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81462872399651621254389557 7637144287467339492599021)
                    ·
                      refine ⟨2863929107800252309724633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7637144287467339492599021 2863929107800252309724633)
                      ·
                        rfl

theorem cell23_5577482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_5577482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577482 prefixEnd_5577482 := by exact prefixLift 5577482
  have htrace : WordTrace (prefixWord ++ tailWord_5577482) baseStart_5577482 baseEnd_5577482 := by
    simpa [prefixWord, tailWord_5577482, baseEnd_5577482] using wordTrace_append hprefix tailTrace_5577482
  have hstable : (prefixWord ++ tailWord_5577482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577482).length < 2 ^ (prefixWord ++ tailWord_5577482).sum := by decide
  have hdescent : baseEnd_5577482 < baseStart_5577482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577512 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_5577512 : Nat := 118140960795 + 5577512 * 2 ^ 59
def prefixEnd_5577512 : Nat := 4983230072969 + 3 ^ 40 * 5577512 * 2
def baseEnd_5577512 : Nat := 2863944512219887192349495

theorem tailTrace_5577512 : CollatzResearch.WordTrace tailWord_5577512 prefixEnd_5577512 2863944512219887192349495 := by
  unfold tailWord_5577512
  simp only [CollatzResearch.WordTrace]
  refine ⟨101714287484817031028639395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135619049979756041371519193 101714287484817031028639395)
  ·
    refine ⟨152571431227225546542959093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101714287484817031028639395 152571431227225546542959093)
    ·
      refine ⟨14303571677552394988402415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152571431227225546542959093 14303571677552394988402415)
      ·
        refine ⟨21455357516328592482603623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14303571677552394988402415 21455357516328592482603623)
        ·
          refine ⟨32183036274492888723905435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21455357516328592482603623 32183036274492888723905435)
          ·
            refine ⟨48274554411739333085858153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32183036274492888723905435 48274554411739333085858153)
            ·
              refine ⟨36205915808804499814393615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48274554411739333085858153 36205915808804499814393615)
              ·
                refine ⟨54308873713206749721590423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36205915808804499814393615 54308873713206749721590423)
                ·
                  refine ⟨81463310569810124582385635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54308873713206749721590423 81463310569810124582385635)
                  ·
                    refine ⟨122194965854715186873578453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81463310569810124582385635 122194965854715186873578453)
                    ·
                      refine ⟨2863944512219887192349495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122194965854715186873578453 2863944512219887192349495)
                      ·
                        rfl

theorem cell23_5577512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_5577512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577512 prefixEnd_5577512 := by exact prefixLift 5577512
  have htrace : WordTrace (prefixWord ++ tailWord_5577512) baseStart_5577512 baseEnd_5577512 := by
    simpa [prefixWord, tailWord_5577512, baseEnd_5577512] using wordTrace_append hprefix tailTrace_5577512
  have hstable : (prefixWord ++ tailWord_5577512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577512).length < 2 ^ (prefixWord ++ tailWord_5577512).sum := by decide
  have hdescent : baseEnd_5577512 < baseStart_5577512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577515 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 2, 8]
def baseStart_5577515 : Nat := 118140960795 + 5577515 * 2 ^ 59
def prefixEnd_5577515 : Nat := 4983230072969 + 3 ^ 40 * 5577515 * 2
def baseEnd_5577515 : Nat := 954648684220616893537327

theorem tailTrace_5577515 : CollatzResearch.WordTrace tailWord_5577515 prefixEnd_5577515 954648684220616893537327 := by
  unfold tailWord_5577515
  simp only [CollatzResearch.WordTrace]
  refine ⟨203428684388623193569637999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135619122925748795713091999 203428684388623193569637999)
  ·
    refine ⟨305143026582934790354456999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203428684388623193569637999 305143026582934790354456999)
    ·
      refine ⟨457714539874402185531685499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305143026582934790354456999 457714539874402185531685499)
      ·
        refine ⟨686571809811603278297528249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457714539874402185531685499 686571809811603278297528249)
        ·
          refine ⟨514928857358702458723146187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686571809811603278297528249 514928857358702458723146187)
          ·
            refine ⟨772393286038053688084719281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514928857358702458723146187 772393286038053688084719281)
            ·
              refine ⟨579294964528540266063539461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 772393286038053688084719281 579294964528540266063539461)
              ·
                refine ⟨108617805849101299886913649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 579294964528540266063539461 108617805849101299886913649)
                ·
                  refine ⟨81463354386825974915185237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108617805849101299886913649 81463354386825974915185237)
                  ·
                    refine ⟨954648684220616893537327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81463354386825974915185237 954648684220616893537327)
                    ·
                      rfl

theorem cell23_5577515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 8].length) (baseStart_5577515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577515 prefixEnd_5577515 := by exact prefixLift 5577515
  have htrace : WordTrace (prefixWord ++ tailWord_5577515) baseStart_5577515 baseEnd_5577515 := by
    simpa [prefixWord, tailWord_5577515, baseEnd_5577515] using wordTrace_append hprefix tailTrace_5577515
  have hstable : (prefixWord ++ tailWord_5577515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577515).length < 2 ^ (prefixWord ++ tailWord_5577515).sum := by decide
  have hdescent : baseEnd_5577515 < baseStart_5577515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577517 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_5577517 : Nat := 118140960795 + 5577517 * 2 ^ 59
def prefixEnd_5577517 : Nat := 4983230072969 + 3 ^ 40 * 5577517 * 2
def baseEnd_5577517 : Nat := 2863947079623159672786973

theorem tailTrace_5577517 : CollatzResearch.WordTrace tailWord_5577517 prefixEnd_5577517 2863947079623159672786973 := by
  unfold tailWord_5577517
  simp only [CollatzResearch.WordTrace]
  refine ⟨203428757334615947911210805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135619171556410631940807203 203428757334615947911210805)
  ·
    refine ⟨19071446000120245116676013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203428757334615947911210805 19071446000120245116676013)
    ·
      refine ⟨7151792250045091918753505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19071446000120245116676013 7151792250045091918753505)
      ·
        refine ⟨5363844187533818939065129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7151792250045091918753505 5363844187533818939065129)
        ·
          refine ⟨4022883140650364204298847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5363844187533818939065129 4022883140650364204298847)
          ·
            refine ⟨6034324710975546306448271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4022883140650364204298847 6034324710975546306448271)
            ·
              refine ⟨9051487066463319459672407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034324710975546306448271 9051487066463319459672407)
              ·
                refine ⟨13577230599694979189508611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9051487066463319459672407 13577230599694979189508611)
                ·
                  refine ⟨20365845899542468784262917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13577230599694979189508611 20365845899542468784262917)
                  ·
                    refine ⟨3818596106164212897049297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20365845899542468784262917 3818596106164212897049297)
                    ·
                      refine ⟨2863947079623159672786973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818596106164212897049297 2863947079623159672786973)
                      ·
                        rfl

theorem cell23_5577517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_5577517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577517 prefixEnd_5577517 := by exact prefixLift 5577517
  have htrace : WordTrace (prefixWord ++ tailWord_5577517) baseStart_5577517 baseEnd_5577517 := by
    simpa [prefixWord, tailWord_5577517, baseEnd_5577517] using wordTrace_append hprefix tailTrace_5577517
  have hstable : (prefixWord ++ tailWord_5577517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577517).length < 2 ^ (prefixWord ++ tailWord_5577517).sum := by decide
  have hdescent : baseEnd_5577517 < baseStart_5577517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577522 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_5577522 : Nat := 118140960795 + 5577522 * 2 ^ 59
def prefixEnd_5577522 : Nat := 4983230072969 + 3 ^ 40 * 5577522 * 2
def baseEnd_5577522 : Nat := 2863949647026432153224449

theorem tailTrace_5577522 : CollatzResearch.WordTrace tailWord_5577522 prefixEnd_5577522 2863949647026432153224449 := by
  unfold tailWord_5577522
  simp only [CollatzResearch.WordTrace]
  refine ⟨50857234924899458441285705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135619293133065222510095213 50857234924899458441285705)
  ·
    refine ⟨38142926193674593830964279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50857234924899458441285705 38142926193674593830964279)
    ·
      refine ⟨57214389290511890746446419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38142926193674593830964279 57214389290511890746446419)
      ·
        refine ⟨85821583935767836119669629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57214389290511890746446419 85821583935767836119669629)
        ·
          refine ⟨32183093975912938544876111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85821583935767836119669629 32183093975912938544876111)
          ·
            refine ⟨48274640963869407817314167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32183093975912938544876111 48274640963869407817314167)
            ·
              refine ⟨72411961445804111725971251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48274640963869407817314167 72411961445804111725971251)
              ·
                refine ⟨108617942168706167588956877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72411961445804111725971251 108617942168706167588956877)
                ·
                  refine ⟨40731728313264812845858829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108617942168706167588956877 40731728313264812845858829)
                  ·
                    refine ⟨15274398117474304817197061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40731728313264812845858829 15274398117474304817197061)
                    ·
                      refine ⟨2863949647026432153224449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15274398117474304817197061 2863949647026432153224449)
                      ·
                        rfl

theorem cell23_5577522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_5577522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577522 prefixEnd_5577522 := by exact prefixLift 5577522
  have htrace : WordTrace (prefixWord ++ tailWord_5577522) baseStart_5577522 baseEnd_5577522 := by
    simpa [prefixWord, tailWord_5577522, baseEnd_5577522] using wordTrace_append hprefix tailTrace_5577522
  have hstable : (prefixWord ++ tailWord_5577522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577522).length < 2 ^ (prefixWord ++ tailWord_5577522).sum := by decide
  have hdescent : baseEnd_5577522 < baseStart_5577522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577540 : List Nat := [2, 3, 4, 2, 1, 2, 1, 3, 5]
def baseStart_5577540 : Nat := 118140960795 + 5577540 * 2 ^ 59
def prefixEnd_5577540 : Nat := 4983230072969 + 3 ^ 40 * 5577540 * 2
def baseEnd_5577540 : Nat := 318217654408690342533263

theorem tailTrace_5577540 : CollatzResearch.WordTrace tailWord_5577540 prefixEnd_5577540 318217654408690342533263 := by
  unfold tailWord_5577540
  simp only [CollatzResearch.WordTrace]
  refine ⟨101714798106766311419649037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135619730809021748559532049 101714798106766311419649037)
  ·
    refine ⟨38143049290037366782368389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101714798106766311419649037 38143049290037366782368389)
    ·
      refine ⟨7151821741882006271694073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38143049290037366782368389 7151821741882006271694073)
      ·
        refine ⟨5363866306411504703770555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7151821741882006271694073 5363866306411504703770555)
        ·
          refine ⟨8045799459617257055655833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5363866306411504703770555 8045799459617257055655833)
          ·
            refine ⟨6034349594712942791741875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8045799459617257055655833 6034349594712942791741875)
            ·
              refine ⟨9051524392069414187612813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034349594712942791741875 9051524392069414187612813)
              ·
                refine ⟨3394321647026030320354805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9051524392069414187612813 3394321647026030320354805)
                ·
                  refine ⟨318217654408690342533263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3394321647026030320354805 318217654408690342533263)
                  ·
                    rfl

theorem cell23_5577540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_5577540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577540 prefixEnd_5577540 := by exact prefixLift 5577540
  have htrace : WordTrace (prefixWord ++ tailWord_5577540) baseStart_5577540 baseEnd_5577540 := by
    simpa [prefixWord, tailWord_5577540, baseEnd_5577540] using wordTrace_append hprefix tailTrace_5577540
  have hstable : (prefixWord ++ tailWord_5577540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577540).length < 2 ^ (prefixWord ++ tailWord_5577540).sum := by decide
  have hdescent : baseEnd_5577540 < baseStart_5577540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577556 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_5577556 : Nat := 118140960795 + 5577556 * 2 ^ 59
def prefixEnd_5577556 : Nat := 4983230072969 + 3 ^ 40 * 5577556 * 2
def baseEnd_5577556 : Nat := 2863967105368685020199293

theorem tailTrace_5577556 : CollatzResearch.WordTrace tailWord_5577556 prefixEnd_5577556 2863967105368685020199293 := by
  unfold tailWord_5577556
  simp only [CollatzResearch.WordTrace]
  refine ⟨101715089890737328785940261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135620119854316438381253681 101715089890737328785940261)
  ·
    refine ⟨19071579354513249147363799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101715089890737328785940261 19071579354513249147363799)
    ·
      refine ⟨28607369031769873721045699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19071579354513249147363799 28607369031769873721045699)
      ·
        refine ⟨42911053547654810581568549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28607369031769873721045699 42911053547654810581568549)
        ·
          refine ⟨8045822540185276984044103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42911053547654810581568549 8045822540185276984044103)
          ·
            refine ⟨12068733810277915476066155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8045822540185276984044103 12068733810277915476066155)
            ·
              refine ⟨18103100715416873214099233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12068733810277915476066155 18103100715416873214099233)
              ·
                refine ⟨13577325536562654910574425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18103100715416873214099233 13577325536562654910574425)
                ·
                  refine ⟨10182994152421991182930819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13577325536562654910574425 10182994152421991182930819)
                  ·
                    refine ⟨15274491228632986774396229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10182994152421991182930819 15274491228632986774396229)
                    ·
                      refine ⟨2863967105368685020199293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15274491228632986774396229 2863967105368685020199293)
                      ·
                        rfl

theorem cell23_5577556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_5577556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577556 prefixEnd_5577556 := by exact prefixLift 5577556
  have htrace : WordTrace (prefixWord ++ tailWord_5577556) baseStart_5577556 baseEnd_5577556 := by
    simpa [prefixWord, tailWord_5577556, baseEnd_5577556] using wordTrace_append hprefix tailTrace_5577556
  have hstable : (prefixWord ++ tailWord_5577556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577556).length < 2 ^ (prefixWord ++ tailWord_5577556).sum := by decide
  have hdescent : baseEnd_5577556 < baseStart_5577556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577559 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 3]
def baseStart_5577559 : Nat := 118140960795 + 5577559 * 2 ^ 59
def prefixEnd_5577559 : Nat := 4983230072969 + 3 ^ 40 * 5577559 * 2
def baseEnd_5577559 : Nat := 2863968645810648508461779

theorem tailTrace_5577559 : CollatzResearch.WordTrace tailWord_5577559 prefixEnd_5577559 2863968645810648508461779 := by
  unfold tailWord_5577559
  simp only [CollatzResearch.WordTrace]
  refine ⟨203430289200463789084239731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135620192800309192722826487 203430289200463789084239731)
  ·
    refine ⟨305145433800695683626359597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203430289200463789084239731 305145433800695683626359597)
    ·
      refine ⟨114429537675260881359884849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305145433800695683626359597 114429537675260881359884849)
      ·
        refine ⟨85822153256445661019913637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114429537675260881359884849 85822153256445661019913637)
        ·
          refine ⟨16091653735583561441233807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85822153256445661019913637 16091653735583561441233807)
          ·
            refine ⟨24137480603375342161850711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16091653735583561441233807 24137480603375342161850711)
            ·
              refine ⟨36206220905063013242776067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24137480603375342161850711 36206220905063013242776067)
              ·
                refine ⟨54309331357594519864164101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36206220905063013242776067 54309331357594519864164101)
                ·
                  refine ⟨10182999629548972474530769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54309331357594519864164101 10182999629548972474530769)
                  ·
                    refine ⟨7637249722161729355898077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10182999629548972474530769 7637249722161729355898077)
                    ·
                      refine ⟨2863968645810648508461779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7637249722161729355898077 2863968645810648508461779)
                      ·
                        rfl

theorem cell23_5577559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_5577559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577559 prefixEnd_5577559 := by exact prefixLift 5577559
  have htrace : WordTrace (prefixWord ++ tailWord_5577559) baseStart_5577559 baseEnd_5577559 := by
    simpa [prefixWord, tailWord_5577559, baseEnd_5577559] using wordTrace_append hprefix tailTrace_5577559
  have hstable : (prefixWord ++ tailWord_5577559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577559).length < 2 ^ (prefixWord ++ tailWord_5577559).sum := by decide
  have hdescent : baseEnd_5577559 < baseStart_5577559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577562 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 8]
def baseStart_5577562 : Nat := 118140960795 + 5577562 * 2 ^ 59
def prefixEnd_5577562 : Nat := 4983230072969 + 3 ^ 40 * 5577562 * 2
def baseEnd_5577562 : Nat := 318218909583623555191585

theorem tailTrace_5577562 : CollatzResearch.WordTrace tailWord_5577562 prefixEnd_5577562 318218909583623555191585 := by
  unfold tailWord_5577562
  simp only [CollatzResearch.WordTrace]
  refine ⟨50857599654863230149149735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135620265746301947064399293 50857599654863230149149735)
  ·
    refine ⟨76286399482294845223724603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50857599654863230149149735 76286399482294845223724603)
    ·
      refine ⟨114429599223442267835586905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76286399482294845223724603 114429599223442267835586905)
      ·
        refine ⟨85822199417581700876690179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114429599223442267835586905 85822199417581700876690179)
        ·
          refine ⟨128733299126372551315035269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85822199417581700876690179 128733299126372551315035269)
          ·
            refine ⟨24137493586194853371569113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128733299126372551315035269 24137493586194853371569113)
            ·
              refine ⟨18103120189646140028676835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24137493586194853371569113 18103120189646140028676835)
              ·
                refine ⟨27154680284469210043015253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18103120189646140028676835 27154680284469210043015253)
                ·
                  refine ⟨318218909583623555191585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27154680284469210043015253 318218909583623555191585)
                  ·
                    rfl

theorem cell23_5577562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_5577562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577562 prefixEnd_5577562 := by exact prefixLift 5577562
  have htrace : WordTrace (prefixWord ++ tailWord_5577562) baseStart_5577562 baseEnd_5577562 := by
    simpa [prefixWord, tailWord_5577562, baseEnd_5577562] using wordTrace_append hprefix tailTrace_5577562
  have hstable : (prefixWord ++ tailWord_5577562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577562).length < 2 ^ (prefixWord ++ tailWord_5577562).sum := by decide
  have hdescent : baseEnd_5577562 < baseStart_5577562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577579 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 6]
def baseStart_5577579 : Nat := 118140960795 + 5577579 * 2 ^ 59
def prefixEnd_5577579 : Nat := 4983230072969 + 3 ^ 40 * 5577579 * 2
def baseEnd_5577579 : Nat := 318219879491526492245743

theorem tailTrace_5577579 : CollatzResearch.WordTrace tailWord_5577579 prefixEnd_5577579 318219879491526492245743 := by
  unfold tailWord_5577579
  simp only [CollatzResearch.WordTrace]
  refine ⟨203431018660391332499967791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135620679106927554999978527 203431018660391332499967791)
  ·
    refine ⟨305146527990586998749951687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203431018660391332499967791 305146527990586998749951687)
    ·
      refine ⟨457719791985880498124927531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305146527990586998749951687 457719791985880498124927531)
      ·
        refine ⟨686579687978820747187391297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457719791985880498124927531 686579687978820747187391297)
        ·
          refine ⟨514934765984115560390543473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686579687978820747187391297 514934765984115560390543473)
          ·
            refine ⟨386201074488086670292907605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 514934765984115560390543473 386201074488086670292907605)
            ·
              refine ⟨4525793841657265667495011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 386201074488086670292907605 4525793841657265667495011)
              ·
                refine ⟨6788690762485898501242517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525793841657265667495011 6788690762485898501242517)
                ·
                  refine ⟨318219879491526492245743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6788690762485898501242517 318219879491526492245743)
                  ·
                    rfl

theorem cell23_5577579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 6].length) (baseStart_5577579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577579 prefixEnd_5577579 := by exact prefixLift 5577579
  have htrace : WordTrace (prefixWord ++ tailWord_5577579) baseStart_5577579 baseEnd_5577579 := by
    simpa [prefixWord, tailWord_5577579, baseEnd_5577579] using wordTrace_append hprefix tailTrace_5577579
  have hstable : (prefixWord ++ tailWord_5577579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577579).length < 2 ^ (prefixWord ++ tailWord_5577579).sum := by decide
  have hdescent : baseEnd_5577579 < baseStart_5577579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577599 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 1, 5, 2]
def baseStart_5577599 : Nat := 118140960795 + 5577599 * 2 ^ 59
def prefixEnd_5577599 : Nat := 4983230072969 + 3 ^ 40 * 5577599 * 2
def baseEnd_5577599 : Nat := 2863989185036828351961595

theorem tailTrace_5577599 : CollatzResearch.WordTrace tailWord_5577599 prefixEnd_5577599 2863989185036828351961595 := by
  unfold tailWord_5577599
  simp only [CollatzResearch.WordTrace]
  refine ⟨203431748120318875915695851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135621165413545917277130567 203431748120318875915695851)
  ·
    refine ⟨305147622180478313873543777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203431748120318875915695851 305147622180478313873543777)
    ·
      refine ⟨228860716635358735405157833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305147622180478313873543777 228860716635358735405157833)
      ·
        refine ⟨171645537476519051553868375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228860716635358735405157833 171645537476519051553868375)
        ·
          refine ⟨257468306214778577330802563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171645537476519051553868375 257468306214778577330802563)
          ·
            refine ⟨386202459322167865996203845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257468306214778577330802563 386202459322167865996203845)
            ·
              refine ⟨72412961122906474874288221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 386202459322167865996203845 72412961122906474874288221)
              ·
                refine ⟨27154860421089928077858083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72412961122906474874288221 27154860421089928077858083)
                ·
                  refine ⟨40732290631634892116787125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27154860421089928077858083 40732290631634892116787125)
                  ·
                    refine ⟨3818652246715771135948793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40732290631634892116787125 3818652246715771135948793)
                    ·
                      refine ⟨2863989185036828351961595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818652246715771135948793 2863989185036828351961595)
                      ·
                        rfl

theorem cell23_5577599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 5, 2].length) (baseStart_5577599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577599 prefixEnd_5577599 := by exact prefixLift 5577599
  have htrace : WordTrace (prefixWord ++ tailWord_5577599) baseStart_5577599 baseEnd_5577599 := by
    simpa [prefixWord, tailWord_5577599, baseEnd_5577599] using wordTrace_append hprefix tailTrace_5577599
  have hstable : (prefixWord ++ tailWord_5577599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577599).length < 2 ^ (prefixWord ++ tailWord_5577599).sum := by decide
  have hdescent : baseEnd_5577599 < baseStart_5577599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577623 : List Nat := [1, 1, 3, 3, 1, 2, 3, 4, 1, 1, 3]
def baseStart_5577623 : Nat := 118140960795 + 5577623 * 2 ^ 59
def prefixEnd_5577623 : Nat := 4983230072969 + 3 ^ 40 * 5577623 * 2
def baseEnd_5577623 : Nat := 2864001508572536258061485

theorem tailTrace_5577623 : CollatzResearch.WordTrace tailWord_5577623 prefixEnd_5577623 2864001508572536258061485 := by
  unfold tailWord_5577623
  simp only [CollatzResearch.WordTrace]
  refine ⟨203432623472231928014569523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135621748981487952009713015 203432623472231928014569523)
  ·
    refine ⟨305148935208347892021854285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203432623472231928014569523 305148935208347892021854285)
    ·
      refine ⟨114430850703130459508195357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305148935208347892021854285 114430850703130459508195357)
      ·
        refine ⟨42911569013673922315573259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114430850703130459508195357 42911569013673922315573259)
        ·
          refine ⟨64367353520510883473359889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42911569013673922315573259 64367353520510883473359889)
          ·
            refine ⟨48275515140383162605019917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64367353520510883473359889 48275515140383162605019917)
            ·
              refine ⟨18103318177643685976882469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48275515140383162605019917 18103318177643685976882469)
              ·
                refine ⟨3394372158308191120665463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18103318177643685976882469 3394372158308191120665463)
                ·
                  refine ⟨5091558237462286680998195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3394372158308191120665463 5091558237462286680998195)
                  ·
                    refine ⟨7637337356193430021497293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5091558237462286680998195 7637337356193430021497293)
                    ·
                      refine ⟨2864001508572536258061485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7637337356193430021497293 2864001508572536258061485)
                      ·
                        rfl

theorem cell23_5577623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_5577623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577623 prefixEnd_5577623 := by exact prefixLift 5577623
  have htrace : WordTrace (prefixWord ++ tailWord_5577623) baseStart_5577623 baseEnd_5577623 := by
    simpa [prefixWord, tailWord_5577623, baseEnd_5577623] using wordTrace_append hprefix tailTrace_5577623
  have hstable : (prefixWord ++ tailWord_5577623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577623).length < 2 ^ (prefixWord ++ tailWord_5577623).sum := by decide
  have hdescent : baseEnd_5577623 < baseStart_5577623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577629 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_5577629 : Nat := 118140960795 + 5577629 * 2 ^ 59
def prefixEnd_5577629 : Nat := 4983230072969 + 3 ^ 40 * 5577629 * 2
def baseEnd_5577629 : Nat := 2864004589456463234586457

theorem tailTrace_5577629 : CollatzResearch.WordTrace tailWord_5577629 prefixEnd_5577629 2864004589456463234586457 := by
  unfold tailWord_5577629
  simp only [CollatzResearch.WordTrace]
  refine ⟨203432842310210191039287941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135621894873473460692858627 203432842310210191039287941)
  ·
    refine ⟨38143657933164410819866489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203432842310210191039287941 38143657933164410819866489)
    ·
      refine ⟨28607743449873308114899867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38143657933164410819866489 28607743449873308114899867)
      ·
        refine ⟨42911615174809962172349801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28607743449873308114899867 42911615174809962172349801)
        ·
          refine ⟨32183711381107471629262351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42911615174809962172349801 32183711381107471629262351)
          ·
            refine ⟨48275567071661207443893527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32183711381107471629262351 48275567071661207443893527)
            ·
              refine ⟨72413350607491811165840291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48275567071661207443893527 72413350607491811165840291)
              ·
                refine ⟨108620025911237716748760437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72413350607491811165840291 108620025911237716748760437)
                ·
                  refine ⟨10183127429178535945196291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108620025911237716748760437 10183127429178535945196291)
                  ·
                    refine ⟨15274691143767803917794437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10183127429178535945196291 15274691143767803917794437)
                    ·
                      refine ⟨2864004589456463234586457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15274691143767803917794437 2864004589456463234586457)
                      ·
                        rfl

theorem cell23_5577629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_5577629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577629 prefixEnd_5577629 := by exact prefixLift 5577629
  have htrace : WordTrace (prefixWord ++ tailWord_5577629) baseStart_5577629 baseEnd_5577629 := by
    simpa [prefixWord, tailWord_5577629, baseEnd_5577629] using wordTrace_append hprefix tailTrace_5577629
  have hstable : (prefixWord ++ tailWord_5577629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577629).length < 2 ^ (prefixWord ++ tailWord_5577629).sum := by decide
  have hdescent : baseEnd_5577629 < baseStart_5577629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577693 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_5577693 : Nat := 118140960795 + 5577693 * 2 ^ 59
def prefixEnd_5577693 : Nat := 4983230072969 + 3 ^ 40 * 5577693 * 2
def baseEnd_5577693 : Nat := 2864037452218350984186163

theorem tailTrace_5577693 : CollatzResearch.WordTrace tailWord_5577693 prefixEnd_5577693 2864037452218350984186163 := by
  unfold tailWord_5577693
  simp only [CollatzResearch.WordTrace]
  refine ⟨203435176581978329969617733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135623451054652219979745155 203435176581978329969617733)
  ·
    refine ⟨38144095609120936869303325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203435176581978329969617733 38144095609120936869303325)
    ·
      refine ⟨14304035853420351325988747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38144095609120936869303325 14304035853420351325988747)
      ·
        refine ⟨21456053780130526988983121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14304035853420351325988747 21456053780130526988983121)
        ·
          refine ⟨16092040335097895241737341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21456053780130526988983121 16092040335097895241737341)
          ·
            refine ⟨6034515125661710715651503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16092040335097895241737341 6034515125661710715651503)
            ·
              refine ⟨9051772688492566073477255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034515125661710715651503 9051772688492566073477255)
              ·
                refine ⟨13577659032738849110215883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9051772688492566073477255 13577659032738849110215883)
                ·
                  refine ⟨20366488549108273665323825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13577659032738849110215883 20366488549108273665323825)
                  ·
                    refine ⟨15274866411831205248992869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20366488549108273665323825 15274866411831205248992869)
                    ·
                      refine ⟨2864037452218350984186163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15274866411831205248992869 2864037452218350984186163)
                      ·
                        rfl

theorem cell23_5577693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_5577693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577693 prefixEnd_5577693 := by exact prefixLift 5577693
  have htrace : WordTrace (prefixWord ++ tailWord_5577693) baseStart_5577693 baseEnd_5577693 := by
    simpa [prefixWord, tailWord_5577693, baseEnd_5577693] using wordTrace_append hprefix tailTrace_5577693
  have hstable : (prefixWord ++ tailWord_5577693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577693).length < 2 ^ (prefixWord ++ tailWord_5577693).sum := by decide
  have hdescent : baseEnd_5577693 < baseStart_5577693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577757 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_5577757 : Nat := 118140960795 + 5577757 * 2 ^ 59
def prefixEnd_5577757 : Nat := 4983230072969 + 3 ^ 40 * 5577757 * 2
def baseEnd_5577757 : Nat := 2864070314980238733785869

theorem tailTrace_5577757 : CollatzResearch.WordTrace tailWord_5577757 prefixEnd_5577757 2864070314980238733785869 := by
  unfold tailWord_5577757
  simp only [CollatzResearch.WordTrace]
  refine ⟨203437510853746468899947525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135625007235830979266631683 203437510853746468899947525)
  ·
    refine ⟨38144533285077462918740161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203437510853746468899947525 38144533285077462918740161)
    ·
      refine ⟨28608399963808097189055121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38144533285077462918740161 28608399963808097189055121)
      ·
        refine ⟨21456299972856072891791341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28608399963808097189055121 21456299972856072891791341)
        ·
          refine ⟨8046112489821027334421753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21456299972856072891791341 8046112489821027334421753)
          ·
            refine ⟨6034584367365770500816315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8046112489821027334421753 6034584367365770500816315)
            ·
              refine ⟨9051876551048655751224473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034584367365770500816315 9051876551048655751224473)
              ·
                refine ⟨6788907413286491813418355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9051876551048655751224473 6788907413286491813418355)
                ·
                  refine ⟨10183361119929737720127533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6788907413286491813418355 10183361119929737720127533)
                  ·
                    refine ⟨3818760419973651645047825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10183361119929737720127533 3818760419973651645047825)
                    ·
                      refine ⟨2864070314980238733785869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818760419973651645047825 2864070314980238733785869)
                      ·
                        rfl

theorem cell23_5577757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_5577757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577757 prefixEnd_5577757 := by exact prefixLift 5577757
  have htrace : WordTrace (prefixWord ++ tailWord_5577757) baseStart_5577757 baseEnd_5577757 := by
    simpa [prefixWord, tailWord_5577757, baseEnd_5577757] using wordTrace_append hprefix tailTrace_5577757
  have hstable : (prefixWord ++ tailWord_5577757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577757).length < 2 ^ (prefixWord ++ tailWord_5577757).sum := by decide
  have hdescent : baseEnd_5577757 < baseStart_5577757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577770 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_5577770 : Nat := 118140960795 + 5577770 * 2 ^ 59
def prefixEnd_5577770 : Nat := 4983230072969 + 3 ^ 40 * 5577770 * 2
def baseEnd_5577770 : Nat := 2864076990228747182923309

theorem tailTrace_5577770 : CollatzResearch.WordTrace tailWord_5577770 prefixEnd_5577770 2864076990228747182923309 := by
  unfold tailWord_5577770
  simp only [CollatzResearch.WordTrace]
  refine ⟨50859496250674843030042691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135625323335132914746780509 50859496250674843030042691)
  ·
    refine ⟨76289244376012264545064037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50859496250674843030042691 76289244376012264545064037)
    ·
      refine ⟨14304233320502299602199507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76289244376012264545064037 14304233320502299602199507)
      ·
        refine ⟨21456349980753449403299261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14304233320502299602199507 21456349980753449403299261)
        ·
          refine ⟨8046131242782543526237223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21456349980753449403299261 8046131242782543526237223)
          ·
            refine ⟨12069196864173815289355835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8046131242782543526237223 12069196864173815289355835)
            ·
              refine ⟨18103795296260722934033753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12069196864173815289355835 18103795296260722934033753)
              ·
                refine ⟨13577846472195542200525315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18103795296260722934033753 13577846472195542200525315)
                ·
                  refine ⟨20366769708293313300787973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13577846472195542200525315 20366769708293313300787973)
                  ·
                    refine ⟨3818769320304996243897745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20366769708293313300787973 3818769320304996243897745)
                    ·
                      refine ⟨2864076990228747182923309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818769320304996243897745 2864076990228747182923309)
                      ·
                        rfl

theorem cell23_5577770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_5577770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577770 prefixEnd_5577770 := by exact prefixLift 5577770
  have htrace : WordTrace (prefixWord ++ tailWord_5577770) baseStart_5577770 baseEnd_5577770 := by
    simpa [prefixWord, tailWord_5577770, baseEnd_5577770] using wordTrace_append hprefix tailTrace_5577770
  have hstable : (prefixWord ++ tailWord_5577770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577770).length < 2 ^ (prefixWord ++ tailWord_5577770).sum := by decide
  have hdescent : baseEnd_5577770 < baseStart_5577770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577776 : List Nat := [2, 1, 1, 1, 2, 4, 2, 5, 5]
def baseStart_5577776 : Nat := 118140960795 + 5577776 * 2 ^ 59
def prefixEnd_5577776 : Nat := 4983230072969 + 3 ^ 40 * 5577776 * 2
def baseEnd_5577776 : Nat := 318231119012519351049809

theorem tailTrace_5577776 : CollatzResearch.WordTrace tailWord_5577776 prefixEnd_5577776 318231119012519351049809 := by
  unfold tailWord_5577776
  simp only [CollatzResearch.WordTrace]
  refine ⟨101719101920338817572444591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135625469227118423429926121 101719101920338817572444591)
  ·
    refine ⟨152578652880508226358666887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101719101920338817572444591 152578652880508226358666887)
    ·
      refine ⟨228867979320762339538000331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152578652880508226358666887 228867979320762339538000331)
      ·
        refine ⟨343301968981143509307000497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228867979320762339538000331 343301968981143509307000497)
        ·
          refine ⟨257476476735857631980250373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343301968981143509307000497 257476476735857631980250373)
          ·
            refine ⟨48276839387973305996296945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 257476476735857631980250373 48276839387973305996296945)
            ·
              refine ⟨36207629540979979497222709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48276839387973305996296945 36207629540979979497222709)
              ·
                refine ⟨3394465269466873077864629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36207629540979979497222709 3394465269466873077864629)
                ·
                  refine ⟨318231119012519351049809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3394465269466873077864629 318231119012519351049809)
                  ·
                    rfl

theorem cell23_5577776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 5].length) (baseStart_5577776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577776 prefixEnd_5577776 := by exact prefixLift 5577776
  have htrace : WordTrace (prefixWord ++ tailWord_5577776) baseStart_5577776 baseEnd_5577776 := by
    simpa [prefixWord, tailWord_5577776, baseEnd_5577776] using wordTrace_append hprefix tailTrace_5577776
  have hstable : (prefixWord ++ tailWord_5577776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577776).length < 2 ^ (prefixWord ++ tailWord_5577776).sum := by decide
  have hdescent : baseEnd_5577776 < baseStart_5577776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577836 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 5, 4]
def baseStart_5577836 : Nat := 118140960795 + 5577836 * 2 ^ 59
def prefixEnd_5577836 : Nat := 4983230072969 + 3 ^ 40 * 5577836 * 2
def baseEnd_5577836 : Nat := 954703626650647974899335

theorem tailTrace_5577836 : CollatzResearch.WordTrace tailWord_5577836 prefixEnd_5577836 954703626650647974899335 := by
  unfold tailWord_5577836
  simp only [CollatzResearch.WordTrace]
  refine ⟨101720196110230132696036681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135626928146973510261382241 101720196110230132696036681)
  ·
    refine ⟨76290147082672599522027511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101720196110230132696036681 76290147082672599522027511)
    ·
      refine ⟨114435220624008899283041267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76290147082672599522027511 114435220624008899283041267)
      ·
        refine ⟨171652830936013348924561901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114435220624008899283041267 171652830936013348924561901)
        ·
          refine ⟨64369811601005005846710713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171652830936013348924561901 64369811601005005846710713)
          ·
            refine ⟨48277358700753754385033035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64369811601005005846710713 48277358700753754385033035)
            ·
              refine ⟨72416038051130631577549553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48277358700753754385033035 72416038051130631577549553)
              ·
                refine ⟨54312028538347973683162165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72416038051130631577549553 54312028538347973683162165)
                ·
                  refine ⟨5091752675470122532796453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54312028538347973683162165 5091752675470122532796453)
                  ·
                    refine ⟨954703626650647974899335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5091752675470122532796453 954703626650647974899335)
                    ·
                      rfl

theorem cell23_5577836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_5577836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577836 prefixEnd_5577836 := by exact prefixLift 5577836
  have htrace : WordTrace (prefixWord ++ tailWord_5577836) baseStart_5577836 baseEnd_5577836 := by
    simpa [prefixWord, tailWord_5577836, baseEnd_5577836] using wordTrace_append hprefix tailTrace_5577836
  have hstable : (prefixWord ++ tailWord_5577836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577836).length < 2 ^ (prefixWord ++ tailWord_5577836).sum := by decide
  have hdescent : baseEnd_5577836 < baseStart_5577836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577839 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_5577839 : Nat := 118140960795 + 5577839 * 2 ^ 59
def prefixEnd_5577839 : Nat := 4983230072969 + 3 ^ 40 * 5577839 * 2
def baseEnd_5577839 : Nat := 2864112420393907412960491

theorem tailTrace_5577839 : CollatzResearch.WordTrace tailWord_5577839 prefixEnd_5577839 2864112420393907412960491 := by
  unfold tailWord_5577839
  simp only [CollatzResearch.WordTrace]
  refine ⟨203440501639449396904432571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135627001092966264602955047 203440501639449396904432571)
  ·
    refine ⟨305160752459174095356648857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203440501639449396904432571 305160752459174095356648857)
    ·
      refine ⟨228870564344380571517486643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305160752459174095356648857 228870564344380571517486643)
      ·
        refine ⟨343305846516570857276229965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228870564344380571517486643 343305846516570857276229965)
        ·
          refine ⟨128739692443714071478586237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 343305846516570857276229965 128739692443714071478586237)
          ·
            refine ⟨48277384666392776804469839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128739692443714071478586237 48277384666392776804469839)
            ·
              refine ⟨72416076999589165206704759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48277384666392776804469839 72416076999589165206704759)
              ·
                refine ⟨108624115499383747810057139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72416076999589165206704759 108624115499383747810057139)
                ·
                  refine ⟨162936173249075621715085709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108624115499383747810057139 162936173249075621715085709)
                  ·
                    refine ⟨61101064968403358143157141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162936173249075621715085709 61101064968403358143157141)
                    ·
                      refine ⟨2864112420393907412960491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61101064968403358143157141 2864112420393907412960491)
                      ·
                        rfl

theorem cell23_5577839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_5577839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577839 prefixEnd_5577839 := by exact prefixLift 5577839
  have htrace : WordTrace (prefixWord ++ tailWord_5577839) baseStart_5577839 baseEnd_5577839 := by
    simpa [prefixWord, tailWord_5577839, baseEnd_5577839] using wordTrace_append hprefix tailTrace_5577839
  have hstable : (prefixWord ++ tailWord_5577839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577839).length < 2 ^ (prefixWord ++ tailWord_5577839).sum := by decide
  have hdescent : baseEnd_5577839 < baseStart_5577839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577853 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_5577853 : Nat := 118140960795 + 5577853 * 2 ^ 59
def prefixEnd_5577853 : Nat := 4983230072969 + 3 ^ 40 * 5577853 * 2
def baseEnd_5577853 : Nat := 954706536374356786061809

theorem tailTrace_5577853 : CollatzResearch.WordTrace tailWord_5577853 prefixEnd_5577853 954706536374356786061809 := by
  unfold tailWord_5577853
  simp only [CollatzResearch.WordTrace]
  refine ⟨203441012261398677295442213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135627341507599118196961475 203441012261398677295442213)
  ·
    refine ⟨38145189799012251992895415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203441012261398677295442213 38145189799012251992895415)
    ·
      refine ⟨57217784698518377989343123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38145189799012251992895415 57217784698518377989343123)
      ·
        refine ⟨85826677047777566984014685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57217784698518377989343123 85826677047777566984014685)
        ·
          refine ⟨32185003892916587619005507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85826677047777566984014685 32185003892916587619005507)
          ·
            refine ⟨48277505839374881428508261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32185003892916587619005507 48277505839374881428508261)
            ·
              refine ⟨9052032344882790267845299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48277505839374881428508261 9052032344882790267845299)
              ·
                refine ⟨13578048517324185401767949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9052032344882790267845299 13578048517324185401767949)
                ·
                  refine ⟨5091768193996569525662981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13578048517324185401767949 5091768193996569525662981)
                  ·
                    refine ⟨954706536374356786061809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5091768193996569525662981 954706536374356786061809)
                    ·
                      rfl

theorem cell23_5577853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_5577853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577853 prefixEnd_5577853 := by exact prefixLift 5577853
  have htrace : WordTrace (prefixWord ++ tailWord_5577853) baseStart_5577853 baseEnd_5577853 := by
    simpa [prefixWord, tailWord_5577853, baseEnd_5577853] using wordTrace_append hprefix tailTrace_5577853
  have hstable : (prefixWord ++ tailWord_5577853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577853).length < 2 ^ (prefixWord ++ tailWord_5577853).sum := by decide
  have hdescent : baseEnd_5577853 < baseStart_5577853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577899 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 8]
def baseStart_5577899 : Nat := 118140960795 + 5577899 * 2 ^ 59
def prefixEnd_5577899 : Nat := 4983230072969 + 3 ^ 40 * 5577899 * 2
def baseEnd_5577899 : Nat := 2864143229233177178210215

theorem tailTrace_5577899 : CollatzResearch.WordTrace tailWord_5577899 prefixEnd_5577899 2864143229233177178210215 := by
  unfold tailWord_5577899
  simp only [CollatzResearch.WordTrace]
  refine ⟨203442690019232027151616751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135628460012821351434411167 203442690019232027151616751)
  ·
    refine ⟨305164035028848040727425127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203442690019232027151616751 305164035028848040727425127)
    ·
      refine ⟨457746052543272061091137691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305164035028848040727425127 457746052543272061091137691)
      ·
        refine ⟨686619078814908091636706537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457746052543272061091137691 686619078814908091636706537)
        ·
          refine ⟨514964309111181068727529903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686619078814908091636706537 514964309111181068727529903)
          ·
            refine ⟨772446463666771603091294855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514964309111181068727529903 772446463666771603091294855)
            ·
              refine ⟨1158669695500157404636942283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772446463666771603091294855 1158669695500157404636942283)
              ·
                refine ⟨1738004543250236106955413425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158669695500157404636942283 1738004543250236106955413425)
                ·
                  refine ⟨1303503407437677080216560069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1738004543250236106955413425 1303503407437677080216560069)
                  ·
                    refine ⟨244406888894564452540605013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1303503407437677080216560069 244406888894564452540605013)
                    ·
                      refine ⟨2864143229233177178210215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 244406888894564452540605013 2864143229233177178210215)
                      ·
                        rfl

theorem cell23_5577899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 8].length) (baseStart_5577899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577899 prefixEnd_5577899 := by exact prefixLift 5577899
  have htrace : WordTrace (prefixWord ++ tailWord_5577899) baseStart_5577899 baseEnd_5577899 := by
    simpa [prefixWord, tailWord_5577899, baseEnd_5577899] using wordTrace_append hprefix tailTrace_5577899
  have hstable : (prefixWord ++ tailWord_5577899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577899).length < 2 ^ (prefixWord ++ tailWord_5577899).sum := by decide
  have hdescent : baseEnd_5577899 < baseStart_5577899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577903 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 4, 3, 2]
def baseStart_5577903 : Nat := 118140960795 + 5577903 * 2 ^ 59
def prefixEnd_5577903 : Nat := 4983230072969 + 3 ^ 40 * 5577903 * 2
def baseEnd_5577903 : Nat := 2864145283155795162560197

theorem tailTrace_5577903 : CollatzResearch.WordTrace tailWord_5577903 prefixEnd_5577903 2864145283155795162560197 := by
  unfold tailWord_5577903
  simp only [CollatzResearch.WordTrace]
  refine ⟨203442835911217535834762363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135628557274145023889841575 203442835911217535834762363)
  ·
    refine ⟨305164253866826303752143545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203442835911217535834762363 305164253866826303752143545)
    ·
      refine ⟨228873190400119727814107659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305164253866826303752143545 228873190400119727814107659)
      ·
        refine ⟨343309785600179591721161489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228873190400119727814107659 343309785600179591721161489)
        ·
          refine ⟨257482339200134693790871117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343309785600179591721161489 257482339200134693790871117)
          ·
            refine ⟨96555877200050510171576669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257482339200134693790871117 96555877200050510171576669)
            ·
              refine ⟨36208453950018941314341251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96555877200050510171576669 36208453950018941314341251)
              ·
                refine ⟨54312680925028411971511877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36208453950018941314341251 54312680925028411971511877)
                ·
                  refine ⟨10183627673442827244658477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54312680925028411971511877 10183627673442827244658477)
                  ·
                    refine ⟨3818860377541060216746929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10183627673442827244658477 3818860377541060216746929)
                    ·
                      refine ⟨2864145283155795162560197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3818860377541060216746929 2864145283155795162560197)
                      ·
                        rfl

theorem cell23_5577903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 4, 3, 2].length) (baseStart_5577903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577903 prefixEnd_5577903 := by exact prefixLift 5577903
  have htrace : WordTrace (prefixWord ++ tailWord_5577903) baseStart_5577903 baseEnd_5577903 := by
    simpa [prefixWord, tailWord_5577903, baseEnd_5577903] using wordTrace_append hprefix tailTrace_5577903
  have hstable : (prefixWord ++ tailWord_5577903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577903).length < 2 ^ (prefixWord ++ tailWord_5577903).sum := by decide
  have hdescent : baseEnd_5577903 < baseStart_5577903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577930 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 1, 5]
def baseStart_5577930 : Nat := 118140960795 + 5577930 * 2 ^ 59
def prefixEnd_5577930 : Nat := 4983230072969 + 3 ^ 40 * 5577930 * 2
def baseEnd_5577930 : Nat := 954719715711155518974191

theorem tailTrace_5577930 : CollatzResearch.WordTrace tailWord_5577930 prefixEnd_5577930 954719715711155518974191 := by
  unfold tailWord_5577930
  simp only [CollatzResearch.WordTrace]
  refine ⟨50860955170529929861498811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135629213788079812963996829 50860955170529929861498811)
  ·
    refine ⟨76291432755794894792248217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50860955170529929861498811 76291432755794894792248217)
    ·
      refine ⟨57218574566846171094186163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76291432755794894792248217 57218574566846171094186163)
      ·
        refine ⟨85827861850269256641279245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57218574566846171094186163 85827861850269256641279245)
        ·
          refine ⟨32185448193850971240479717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85827861850269256641279245 32185448193850971240479717)
          ·
            refine ⟨6034771536347057107589947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32185448193850971240479717 6034771536347057107589947)
            ·
              refine ⟨9052157304520585661384921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034771536347057107589947 9052157304520585661384921)
              ·
                refine ⟨6789117978390439246038691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9052157304520585661384921 6789117978390439246038691)
                ·
                  refine ⟨10183676967585658869058037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6789117978390439246038691 10183676967585658869058037)
                  ·
                    refine ⟨954719715711155518974191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10183676967585658869058037 954719715711155518974191)
                    ·
                      rfl

theorem cell23_5577930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_5577930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577930 prefixEnd_5577930 := by exact prefixLift 5577930
  have htrace : WordTrace (prefixWord ++ tailWord_5577930) baseStart_5577930 baseEnd_5577930 := by
    simpa [prefixWord, tailWord_5577930, baseEnd_5577930] using wordTrace_append hprefix tailTrace_5577930
  have hstable : (prefixWord ++ tailWord_5577930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577930).length < 2 ^ (prefixWord ++ tailWord_5577930).sum := by decide
  have hdescent : baseEnd_5577930 < baseStart_5577930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577953 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_5577953 : Nat := 118140960795 + 5577953 * 2 ^ 59
def prefixEnd_5577953 : Nat := 4983230072969 + 3 ^ 40 * 5577953 * 2
def baseEnd_5577953 : Nat := 2864170957188519966934967

theorem tailTrace_5577953 : CollatzResearch.WordTrace tailWord_5577953 prefixEnd_5577953 2864170957188519966934967 := by
  unfold tailWord_5577953
  simp only [CollatzResearch.WordTrace]
  refine ⟨203444659561036394374082513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135629773040690929582721675 203444659561036394374082513)
  ·
    refine ⟨152583494670777295780561885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203444659561036394374082513 152583494670777295780561885)
    ·
      refine ⟨57218810501541485917710707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152583494670777295780561885 57218810501541485917710707)
      ·
        refine ⟨85828215752312228876566061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57218810501541485917710707 85828215752312228876566061)
        ·
          refine ⟨32185580907117085828712273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85828215752312228876566061 32185580907117085828712273)
          ·
            refine ⟨24139185680337814371534205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32185580907117085828712273 24139185680337814371534205)
            ·
              refine ⟨9052194630126680389325327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24139185680337814371534205 9052194630126680389325327)
              ·
                refine ⟨13578291945190020583987991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9052194630126680389325327 13578291945190020583987991)
                ·
                  refine ⟨20367437917785030875981987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13578291945190020583987991 20367437917785030875981987)
                  ·
                    refine ⟨30551156876677546313972981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20367437917785030875981987 30551156876677546313972981)
                    ·
                      refine ⟨2864170957188519966934967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30551156876677546313972981 2864170957188519966934967)
                      ·
                        rfl

theorem cell23_5577953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_5577953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577953 prefixEnd_5577953 := by exact prefixLift 5577953
  have htrace : WordTrace (prefixWord ++ tailWord_5577953) baseStart_5577953 baseEnd_5577953 := by
    simpa [prefixWord, tailWord_5577953, baseEnd_5577953] using wordTrace_append hprefix tailTrace_5577953
  have hstable : (prefixWord ++ tailWord_5577953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577953).length < 2 ^ (prefixWord ++ tailWord_5577953).sum := by decide
  have hdescent : baseEnd_5577953 < baseStart_5577953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577960 : List Nat := [2, 1, 4, 1, 2, 1, 4, 2, 2, 4]
def baseStart_5577960 : Nat := 118140960795 + 5577960 * 2 ^ 59
def prefixEnd_5577960 : Nat := 4983230072969 + 3 ^ 40 * 5577960 * 2
def baseEnd_5577960 : Nat := 954724850517700479849145

theorem tailTrace_5577960 : CollatzResearch.WordTrace tailWord_5577960 prefixEnd_5577960 954724850517700479849145 := by
  unfold tailWord_5577960
  simp only [CollatzResearch.WordTrace]
  refine ⟨101722457436005517284793667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135629943248007356379724889 101722457436005517284793667)
  ·
    refine ⟨152583686154008275927190501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101722457436005517284793667 152583686154008275927190501)
    ·
      refine ⟨28609441153876551736348219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152583686154008275927190501 28609441153876551736348219)
      ·
        refine ⟨42914161730814827604522329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28609441153876551736348219 42914161730814827604522329)
        ·
          refine ⟨32185621298111120703391747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42914161730814827604522329 32185621298111120703391747)
          ·
            refine ⟨48278431947166681055087621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32185621298111120703391747 48278431947166681055087621)
            ·
              refine ⟨9052205990093752697828929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48278431947166681055087621 9052205990093752697828929)
              ·
                refine ⟨6789154492570314523371697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9052205990093752697828929 6789154492570314523371697)
                ·
                  refine ⟨5091865869427735892528773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6789154492570314523371697 5091865869427735892528773)
                  ·
                    refine ⟨954724850517700479849145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5091865869427735892528773 954724850517700479849145)
                    ·
                      rfl

theorem cell23_5577960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_5577960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577960 prefixEnd_5577960 := by exact prefixLift 5577960
  have htrace : WordTrace (prefixWord ++ tailWord_5577960) baseStart_5577960 baseEnd_5577960 := by
    simpa [prefixWord, tailWord_5577960, baseEnd_5577960] using wordTrace_append hprefix tailTrace_5577960
  have hstable : (prefixWord ++ tailWord_5577960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577960).length < 2 ^ (prefixWord ++ tailWord_5577960).sum := by decide
  have hdescent : baseEnd_5577960 < baseStart_5577960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577980 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_5577980 : Nat := 118140960795 + 5577980 * 2 ^ 59
def prefixEnd_5577980 : Nat := 4983230072969 + 3 ^ 40 * 5577980 * 2
def baseEnd_5577980 : Nat := 2864184821166191361297343

theorem tailTrace_5577980 : CollatzResearch.WordTrace tailWord_5577980 prefixEnd_5577980 2864184821166191361297343 := by
  unfold tailWord_5577980
  simp only [CollatzResearch.WordTrace]
  refine ⟨101722822165969288992657697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135630429554625718656876929 101722822165969288992657697)
  ·
    refine ⟨76292116624476966744493273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101722822165969288992657697 76292116624476966744493273)
    ·
      refine ⟨57219087468357725058369955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76292116624476966744493273 57219087468357725058369955)
      ·
        refine ⟨85828631202536587587554933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57219087468357725058369955 85828631202536587587554933)
        ·
          refine ⟨8046434175237805086333275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85828631202536587587554933 8046434175237805086333275)
          ·
            refine ⟨12069651262856707629499913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8046434175237805086333275 12069651262856707629499913)
            ·
              refine ⟨9052238447142530722124935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12069651262856707629499913 9052238447142530722124935)
              ·
                refine ⟨13578357670713796083187403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9052238447142530722124935 13578357670713796083187403)
                ·
                  refine ⟨20367536506070694124781105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13578357670713796083187403 20367536506070694124781105)
                  ·
                    refine ⟨15275652379553020593585829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20367536506070694124781105 15275652379553020593585829)
                    ·
                      refine ⟨2864184821166191361297343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15275652379553020593585829 2864184821166191361297343)
                      ·
                        rfl

theorem cell23_5577980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_5577980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577980 prefixEnd_5577980 := by exact prefixLift 5577980
  have htrace : WordTrace (prefixWord ++ tailWord_5577980) baseStart_5577980 baseEnd_5577980 := by
    simpa [prefixWord, tailWord_5577980, baseEnd_5577980] using wordTrace_append hprefix tailTrace_5577980
  have hstable : (prefixWord ++ tailWord_5577980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577980).length < 2 ^ (prefixWord ++ tailWord_5577980).sum := by decide
  have hdescent : baseEnd_5577980 < baseStart_5577980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5577983 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 3]
def baseStart_5577983 : Nat := 118140960795 + 5577983 * 2 ^ 59
def prefixEnd_5577983 : Nat := 4983230072969 + 3 ^ 40 * 5577983 * 2
def baseEnd_5577983 : Nat := 2864186361608154849559829

theorem tailTrace_5577983 : CollatzResearch.WordTrace tailWord_5577983 prefixEnd_5577983 2864186361608154849559829 := by
  unfold tailWord_5577983
  simp only [CollatzResearch.WordTrace]
  refine ⟨203445753750927709497674603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135630502500618472998449735 203445753750927709497674603)
  ·
    refine ⟨305168630626391564246511905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203445753750927709497674603 305168630626391564246511905)
    ·
      refine ⟨228876472969793673184883929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305168630626391564246511905 228876472969793673184883929)
      ·
        refine ⟨171657354727345254888662947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228876472969793673184883929 171657354727345254888662947)
        ·
          refine ⟨257486032091017882332994421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171657354727345254888662947 257486032091017882332994421)
          ·
            refine ⟨24139315508532926468718227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 257486032091017882332994421 24139315508532926468718227)
            ·
              refine ⟨36208973262799389703077341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24139315508532926468718227 36208973262799389703077341)
              ·
                refine ⟨13578364973549771138654003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36208973262799389703077341 13578364973549771138654003)
                ·
                  refine ⟨20367547460324656707981005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13578364973549771138654003 20367547460324656707981005)
                  ·
                    refine ⟨7637830297621746265492877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20367547460324656707981005 7637830297621746265492877)
                    ·
                      refine ⟨2864186361608154849559829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7637830297621746265492877 2864186361608154849559829)
                      ·
                        rfl

theorem cell23_5577983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_5577983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5577983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5577983 prefixEnd_5577983 := by exact prefixLift 5577983
  have htrace : WordTrace (prefixWord ++ tailWord_5577983) baseStart_5577983 baseEnd_5577983 := by
    simpa [prefixWord, tailWord_5577983, baseEnd_5577983] using wordTrace_append hprefix tailTrace_5577983
  have hstable : (prefixWord ++ tailWord_5577983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5577983).length < 2 ^ (prefixWord ++ tailWord_5577983).sum := by decide
  have hdescent : baseEnd_5577983 < baseStart_5577983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5577983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578033 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 2, 6]
def baseStart_5578033 : Nat := 118140960795 + 5578033 * 2 ^ 59
def prefixEnd_5578033 : Nat := 4983230072969 + 3 ^ 40 * 5578033 * 2
def baseEnd_5578033 : Nat := 954737345213626551311533

theorem tailTrace_5578033 : CollatzResearch.WordTrace tailWord_5578033 prefixEnd_5578033 954737345213626551311533 := by
  unfold tailWord_5578033
  simp only [CollatzResearch.WordTrace]
  refine ⟨203447577400746568036994753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135631718267164378691329835 203447577400746568036994753)
  ·
    refine ⟨152585683050559926027746065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203447577400746568036994753 152585683050559926027746065)
    ·
      refine ⟨114439262287919944520809549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152585683050559926027746065 114439262287919944520809549)
      ·
        refine ⟨42914723357969979195303581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114439262287919944520809549 42914723357969979195303581)
        ·
          refine ⟨16093021259238742198238843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42914723357969979195303581 16093021259238742198238843)
          ·
            refine ⟨24139531888858113297358265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16093021259238742198238843 24139531888858113297358265)
            ·
              refine ⟨18104648916643584973018699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24139531888858113297358265 18104648916643584973018699)
              ·
                refine ⟨27156973374965377459528049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18104648916643584973018699 27156973374965377459528049)
                ·
                  refine ⟨20367730031224033094646037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27156973374965377459528049 20367730031224033094646037)
                  ·
                    refine ⟨954737345213626551311533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20367730031224033094646037 954737345213626551311533)
                    ·
                      rfl

theorem cell23_5578033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_5578033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578033 prefixEnd_5578033 := by exact prefixLift 5578033
  have htrace : WordTrace (prefixWord ++ tailWord_5578033) baseStart_5578033 baseEnd_5578033 := by
    simpa [prefixWord, tailWord_5578033, baseEnd_5578033] using wordTrace_append hprefix tailTrace_5578033
  have hstable : (prefixWord ++ tailWord_5578033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578033).length < 2 ^ (prefixWord ++ tailWord_5578033).sum := by decide
  have hdescent : baseEnd_5578033 < baseStart_5578033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578034 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3]
def baseStart_5578034 : Nat := 118140960795 + 5578034 * 2 ^ 59
def prefixEnd_5578034 : Nat := 4983230072969 + 3 ^ 40 * 5578034 * 2
def baseEnd_5578034 : Nat := 2864212549121534150022095

theorem tailTrace_5578034 : CollatzResearch.WordTrace tailWord_5578034 prefixEnd_5578034 2864212549121534150022095 := by
  unfold tailWord_5578034
  simp only [CollatzResearch.WordTrace]
  refine ⟨50861903468435736301945289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135631742582495296805187437 50861903468435736301945289)
  ·
    refine ⟨38146427601326802226458967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50861903468435736301945289 38146427601326802226458967)
    ·
      refine ⟨57219641401990203339688451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38146427601326802226458967 57219641401990203339688451)
      ·
        refine ⟨85829462102985305009532677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57219641401990203339688451 85829462102985305009532677)
        ·
          refine ⟨16093024144309744689287377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85829462102985305009532677 16093024144309744689287377)
          ·
            refine ⟨12069768108232308516965533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16093024144309744689287377 12069768108232308516965533)
            ·
              refine ⟨4526163040587115693862075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12069768108232308516965533 4526163040587115693862075)
              ·
                refine ⟨6789244560880673540793113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4526163040587115693862075 6789244560880673540793113)
                ·
                  refine ⟨5091933420660505155594835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6789244560880673540793113 5091933420660505155594835)
                  ·
                    refine ⟨7637900130990757733392253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5091933420660505155594835 7637900130990757733392253)
                    ·
                      refine ⟨2864212549121534150022095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7637900130990757733392253 2864212549121534150022095)
                      ·
                        rfl

theorem cell23_5578034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_5578034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578034 prefixEnd_5578034 := by exact prefixLift 5578034
  have htrace : WordTrace (prefixWord ++ tailWord_5578034) baseStart_5578034 baseEnd_5578034 := by
    simpa [prefixWord, tailWord_5578034, baseEnd_5578034] using wordTrace_append hprefix tailTrace_5578034
  have hstable : (prefixWord ++ tailWord_5578034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578034).length < 2 ^ (prefixWord ++ tailWord_5578034).sum := by decide
  have hdescent : baseEnd_5578034 < baseStart_5578034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578073 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 4, 3, 3]
def baseStart_5578073 : Nat := 118140960795 + 5578073 * 2 ^ 59
def prefixEnd_5578073 : Nat := 4983230072969 + 3 ^ 40 * 5578073 * 2
def baseEnd_5578073 : Nat := 2864232574867059497434415

theorem tailTrace_5578073 : CollatzResearch.WordTrace tailWord_5578073 prefixEnd_5578073 2864232574867059497434415 := by
  unfold tailWord_5578073
  simp only [CollatzResearch.WordTrace]
  refine ⟨203449036320601654868450873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135632690880401103245633915 203449036320601654868450873)
  ·
    refine ⟨152586777240451241151338155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203449036320601654868450873 152586777240451241151338155)
    ·
      refine ⟨228880165860676861727007233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152586777240451241151338155 228880165860676861727007233)
      ·
        refine ⟨171660124395507646295255425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228880165860676861727007233 171660124395507646295255425)
        ·
          refine ⟨128745093296630734721441569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171660124395507646295255425 128745093296630734721441569)
          ·
            refine ⟨96558819972473051041081177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128745093296630734721441569 96558819972473051041081177)
            ·
              refine ⟨72419114979354788280810883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96558819972473051041081177 72419114979354788280810883)
              ·
                refine ⟨108628672469032182421216325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72419114979354788280810883 108628672469032182421216325)
                ·
                  refine ⟨20367876087943534203978061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108628672469032182421216325 20367876087943534203978061)
                  ·
                    refine ⟨7637953532978825326491773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20367876087943534203978061 7637953532978825326491773)
                    ·
                      refine ⟨2864232574867059497434415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7637953532978825326491773 2864232574867059497434415)
                      ·
                        rfl

theorem cell23_5578073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_5578073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578073 prefixEnd_5578073 := by exact prefixLift 5578073
  have htrace : WordTrace (prefixWord ++ tailWord_5578073) baseStart_5578073 baseEnd_5578073 := by
    simpa [prefixWord, tailWord_5578073, baseEnd_5578073] using wordTrace_append hprefix tailTrace_5578073
  have hstable : (prefixWord ++ tailWord_5578073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578073).length < 2 ^ (prefixWord ++ tailWord_5578073).sum := by decide
  have hdescent : baseEnd_5578073 < baseStart_5578073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578080 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 7]
def baseStart_5578080 : Nat := 118140960795 + 5578080 * 2 ^ 59
def prefixEnd_5578080 : Nat := 4983230072969 + 3 ^ 40 * 5578080 * 2
def baseEnd_5578080 : Nat := 318248463247960107782987

theorem tailTrace_5578080 : CollatzResearch.WordTrace tailWord_5578080 prefixEnd_5578080 318248463247960107782987 := by
  unfold tailWord_5578080
  simp only [CollatzResearch.WordTrace]
  refine ⟨101724645815788147531977847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135632861087717530042637129 101724645815788147531977847)
  ·
    refine ⟨152586968723682221297966771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101724645815788147531977847 152586968723682221297966771)
    ·
      refine ⟨228880453085523331946950157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152586968723682221297966771 228880453085523331946950157)
      ·
        refine ⟨85830169907071249480106309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228880453085523331946950157 85830169907071249480106309)
        ·
          refine ⟨16093156857575859277519933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85830169907071249480106309 16093156857575859277519933)
          ·
            refine ⟨6034933821590947229069975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16093156857575859277519933 6034933821590947229069975)
            ·
              refine ⟨9052400732386420843604963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6034933821590947229069975 9052400732386420843604963)
              ·
                refine ⟨13578601098579631265407445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9052400732386420843604963 13578601098579631265407445)
                ·
                  refine ⟨318248463247960107782987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13578601098579631265407445 318248463247960107782987)
                  ·
                    rfl

theorem cell23_5578080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 7].length) (baseStart_5578080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578080 prefixEnd_5578080 := by exact prefixLift 5578080
  have htrace : WordTrace (prefixWord ++ tailWord_5578080) baseStart_5578080 baseEnd_5578080 := by
    simpa [prefixWord, tailWord_5578080, baseEnd_5578080] using wordTrace_append hprefix tailTrace_5578080
  have hstable : (prefixWord ++ tailWord_5578080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578080).length < 2 ^ (prefixWord ++ tailWord_5578080).sum := by decide
  have hdescent : baseEnd_5578080 < baseStart_5578080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578157 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_5578157 : Nat := 118140960795 + 5578157 * 2 ^ 59
def prefixEnd_5578157 : Nat := 4983230072969 + 3 ^ 40 * 5578157 * 2
def baseEnd_5578157 : Nat := 954758569080679056261343

theorem tailTrace_5578157 : CollatzResearch.WordTrace tailWord_5578157 prefixEnd_5578157 954758569080679056261343 := by
  unfold tailWord_5578157
  simp only [CollatzResearch.WordTrace]
  refine ⟨203452100052297337214508725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135634733368198224809672483 203452100052297337214508725)
  ·
    refine ⟨19073634379902875363860193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203452100052297337214508725 19073634379902875363860193)
    ·
      refine ⟨14305225784927156522895145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19073634379902875363860193 14305225784927156522895145)
      ·
        refine ⟨10728919338695367392171359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14305225784927156522895145 10728919338695367392171359)
        ·
          refine ⟨16093379008043051088257039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10728919338695367392171359 16093379008043051088257039)
          ·
            refine ⟨24140068512064576632385559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16093379008043051088257039 24140068512064576632385559)
            ·
              refine ⟨36210102768096864948578339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24140068512064576632385559 36210102768096864948578339)
              ·
                refine ⟨54315154152145297422867509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36210102768096864948578339 54315154152145297422867509)
                ·
                  refine ⟨5092045701763621633393829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54315154152145297422867509 5092045701763621633393829)
                  ·
                    refine ⟨954758569080679056261343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5092045701763621633393829 954758569080679056261343)
                    ·
                      rfl

theorem cell23_5578157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_5578157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578157 prefixEnd_5578157 := by exact prefixLift 5578157
  have htrace : WordTrace (prefixWord ++ tailWord_5578157) baseStart_5578157 baseEnd_5578157 := by
    simpa [prefixWord, tailWord_5578157, baseEnd_5578157] using wordTrace_append hprefix tailTrace_5578157
  have hstable : (prefixWord ++ tailWord_5578157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578157).length < 2 ^ (prefixWord ++ tailWord_5578157).sum := by decide
  have hdescent : baseEnd_5578157 < baseStart_5578157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578237 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_5578237 : Nat := 118140960795 + 5578237 * 2 ^ 59
def prefixEnd_5578237 : Nat := 4983230072969 + 3 ^ 40 * 5578237 * 2
def baseEnd_5578237 : Nat := 2864316785694396855783661

theorem tailTrace_5578237 : CollatzResearch.WordTrace tailWord_5578237 prefixEnd_5578237 2864316785694396855783661 := by
  unfold tailWord_5578237
  simp only [CollatzResearch.WordTrace]
  refine ⟨203455017892007510877420965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135636678594671673918280643 203455017892007510877420965)
  ·
    refine ⟨38147815854751408289516431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203455017892007510877420965 38147815854751408289516431)
    ·
      refine ⟨57221723782127112434274647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38147815854751408289516431 57221723782127112434274647)
      ·
        refine ⟨85832585673190668651411971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57221723782127112434274647 85832585673190668651411971)
        ·
          refine ⟨128748878509786002977117957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85832585673190668651411971 128748878509786002977117957)
          ·
            refine ⟨24140414720584875558209617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128748878509786002977117957 24140414720584875558209617)
            ·
              refine ⟨18105311040438656668657213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24140414720584875558209617 18105311040438656668657213)
              ·
                refine ⟨6789491640164496250746455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18105311040438656668657213 6789491640164496250746455)
                ·
                  refine ⟨10184237460246744376119683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6789491640164496250746455 10184237460246744376119683)
                  ·
                    refine ⟨15276356190370116564179525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10184237460246744376119683 15276356190370116564179525)
                    ·
                      refine ⟨2864316785694396855783661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15276356190370116564179525 2864316785694396855783661)
                      ·
                        rfl

theorem cell23_5578237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_5578237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578237 prefixEnd_5578237 := by exact prefixLift 5578237
  have htrace : WordTrace (prefixWord ++ tailWord_5578237) baseStart_5578237 baseEnd_5578237 := by
    simpa [prefixWord, tailWord_5578237, baseEnd_5578237] using wordTrace_append hprefix tailTrace_5578237
  have hstable : (prefixWord ++ tailWord_5578237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578237).length < 2 ^ (prefixWord ++ tailWord_5578237).sum := by decide
  have hdescent : baseEnd_5578237 < baseStart_5578237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578247 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 4, 4]
def baseStart_5578247 : Nat := 118140960795 + 5578247 * 2 ^ 59
def prefixEnd_5578247 : Nat := 4983230072969 + 3 ^ 40 * 5578247 * 2
def baseEnd_5578247 : Nat := 954773973500313938886205

theorem tailTrace_5578247 : CollatzResearch.WordTrace tailWord_5578247 prefixEnd_5578247 954773973500313938886205 := by
  unfold tailWord_5578247
  simp only [CollatzResearch.WordTrace]
  refine ⟨203455382621971282585284995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135636921747980855056856663 203455382621971282585284995)
  ·
    refine ⟨305183073932956923877927493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203455382621971282585284995 305183073932956923877927493)
    ·
      refine ⟨57221826362429423227111405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305183073932956923877927493 57221826362429423227111405)
      ·
        refine ⟨21458184885911033710166777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57221826362429423227111405 21458184885911033710166777)
        ·
          refine ⟨16093638664433275282625083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21458184885911033710166777 16093638664433275282625083)
          ·
            refine ⟨24140457996649912923937625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16093638664433275282625083 24140457996649912923937625)
            ·
              refine ⟨18105343497487434692953219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24140457996649912923937625 18105343497487434692953219)
              ·
                refine ⟨27158015246231152039429829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18105343497487434692953219 27158015246231152039429829)
                ·
                  refine ⟨5092127858668341007393093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27158015246231152039429829 5092127858668341007393093)
                  ·
                    refine ⟨954773973500313938886205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5092127858668341007393093 954773973500313938886205)
                    ·
                      rfl

theorem cell23_5578247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_5578247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578247 prefixEnd_5578247 := by exact prefixLift 5578247
  have htrace : WordTrace (prefixWord ++ tailWord_5578247) baseStart_5578247 baseEnd_5578247 := by
    simpa [prefixWord, tailWord_5578247, baseEnd_5578247] using wordTrace_append hprefix tailTrace_5578247
  have hstable : (prefixWord ++ tailWord_5578247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578247).length < 2 ^ (prefixWord ++ tailWord_5578247).sum := by decide
  have hdescent : baseEnd_5578247 < baseStart_5578247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578250 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_5578250 : Nat := 118140960795 + 5578250 * 2 ^ 59
def prefixEnd_5578250 : Nat := 4983230072969 + 3 ^ 40 * 5578250 * 2
def baseEnd_5578250 : Nat := 2864323460942905304921101

theorem tailTrace_5578250 : CollatzResearch.WordTrace tailWord_5578250 prefixEnd_5578250 2864323460942905304921101 := by
  unfold tailWord_5578250
  simp only [CollatzResearch.WordTrace]
  refine ⟨50863873010240103524411051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135636994693973609398429469 50863873010240103524411051)
  ·
    refine ⟨76295809515360155286616577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50863873010240103524411051 76295809515360155286616577)
    ·
      refine ⟨57221857136520116464962433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76295809515360155286616577 57221857136520116464962433)
      ·
        refine ⟨42916392852390087348721825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57221857136520116464962433 42916392852390087348721825)
        ·
          refine ⟨32187294639292565511541369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42916392852390087348721825 32187294639292565511541369)
          ·
            refine ⟨24140470979469424133656027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32187294639292565511541369 24140470979469424133656027)
            ·
              refine ⟨36210706469204136200484041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24140470979469424133656027 36210706469204136200484041)
              ·
                refine ⟨27158029851903102150363031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36210706469204136200484041 27158029851903102150363031)
                ·
                  refine ⟨40737044777854653225544547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27158029851903102150363031 40737044777854653225544547)
                  ·
                    refine ⟨61105567166781979838316821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40737044777854653225544547 61105567166781979838316821)
                    ·
                      refine ⟨2864323460942905304921101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61105567166781979838316821 2864323460942905304921101)
                      ·
                        rfl

theorem cell23_5578250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_5578250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578250 prefixEnd_5578250 := by exact prefixLift 5578250
  have htrace : WordTrace (prefixWord ++ tailWord_5578250) baseStart_5578250 baseEnd_5578250 := by
    simpa [prefixWord, tailWord_5578250, baseEnd_5578250] using wordTrace_append hprefix tailTrace_5578250
  have hstable : (prefixWord ++ tailWord_5578250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578250).length < 2 ^ (prefixWord ++ tailWord_5578250).sum := by decide
  have hdescent : baseEnd_5578250 < baseStart_5578250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578264 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 2, 4]
def baseStart_5578264 : Nat := 118140960795 + 5578264 * 2 ^ 59
def prefixEnd_5578264 : Nat := 4983230072969 + 3 ^ 40 * 5578264 * 2
def baseEnd_5578264 : Nat := 954776883224022750048679

theorem tailTrace_5578264 : CollatzResearch.WordTrace tailWord_5578264 prefixEnd_5578264 954776883224022750048679 := by
  unfold tailWord_5578264
  simp only [CollatzResearch.WordTrace]
  refine ⟨101728001331454847244326923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135637335108606462992435897 101728001331454847244326923)
  ·
    refine ⟨152592001997182270866490385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101728001331454847244326923 152592001997182270866490385)
    ·
      refine ⟨114444001497886703149867789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152592001997182270866490385 114444001497886703149867789)
      ·
        refine ⟨42916500561707513681200421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114444001497886703149867789 42916500561707513681200421)
        ·
          refine ⟨8046843855320158815225079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42916500561707513681200421 8046843855320158815225079)
          ·
            refine ⟨12070265782980238222837619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8046843855320158815225079 12070265782980238222837619)
            ·
              refine ⟨18105398674470357334256429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12070265782980238222837619 18105398674470357334256429)
              ·
                refine ⟨6789524502926384000346161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18105398674470357334256429 6789524502926384000346161)
                ·
                  refine ⟨5092143377194788000259621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6789524502926384000346161 5092143377194788000259621)
                  ·
                    refine ⟨954776883224022750048679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5092143377194788000259621 954776883224022750048679)
                    ·
                      rfl

theorem cell23_5578264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_5578264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578264 prefixEnd_5578264 := by exact prefixLift 5578264
  have htrace : WordTrace (prefixWord ++ tailWord_5578264) baseStart_5578264 baseEnd_5578264 := by
    simpa [prefixWord, tailWord_5578264, baseEnd_5578264] using wordTrace_append hprefix tailTrace_5578264
  have hstable : (prefixWord ++ tailWord_5578264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578264).length < 2 ^ (prefixWord ++ tailWord_5578264).sum := by decide
  have hdescent : baseEnd_5578264 < baseStart_5578264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578274 : List Nat := [3, 3, 1, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_5578274 : Nat := 118140960795 + 5578274 * 2 ^ 59
def prefixEnd_5578274 : Nat := 4983230072969 + 3 ^ 40 * 5578274 * 2
def baseEnd_5578274 : Nat := 2864335784478613211020991

theorem tailTrace_5578274 : CollatzResearch.WordTrace tailWord_5578274 prefixEnd_5578274 2864335784478613211020991 := by
  unfold tailWord_5578274
  simp only [CollatzResearch.WordTrace]
  refine ⟨50864091848218366549129469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135637578261915644131011917 50864091848218366549129469)
  ·
    refine ⟨19074034443081887455923551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50864091848218366549129469 19074034443081887455923551)
    ·
      refine ⟨28611051664622831183885327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19074034443081887455923551 28611051664622831183885327)
      ·
        refine ⟨42916577496934246775827991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28611051664622831183885327 42916577496934246775827991)
        ·
          refine ⟨64374866245401370163741987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42916577496934246775827991 64374866245401370163741987)
          ·
            refine ⟨96562299368102055245612981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64374866245401370163741987 96562299368102055245612981)
            ·
              refine ⟨9052715565759567679276217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96562299368102055245612981 9052715565759567679276217)
              ·
                refine ⟨6789536674319675759457163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9052715565759567679276217 6789536674319675759457163)
                ·
                  refine ⟨10184305011479513639185745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6789536674319675759457163 10184305011479513639185745)
                  ·
                    refine ⟨7638228758609635229389309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10184305011479513639185745 7638228758609635229389309)
                    ·
                      refine ⟨2864335784478613211020991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7638228758609635229389309 2864335784478613211020991)
                      ·
                        rfl

theorem cell23_5578274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_5578274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578274 prefixEnd_5578274 := by exact prefixLift 5578274
  have htrace : WordTrace (prefixWord ++ tailWord_5578274) baseStart_5578274 baseEnd_5578274 := by
    simpa [prefixWord, tailWord_5578274, baseEnd_5578274] using wordTrace_append hprefix tailTrace_5578274
  have hstable : (prefixWord ++ tailWord_5578274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578274).length < 2 ^ (prefixWord ++ tailWord_5578274).sum := by decide
  have hdescent : baseEnd_5578274 < baseStart_5578274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578320 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 2, 6]
def baseStart_5578320 : Nat := 118140960795 + 5578320 * 2 ^ 59
def prefixEnd_5578320 : Nat := 4983230072969 + 3 ^ 40 * 5578320 * 2
def baseEnd_5578320 : Nat := 954786468196240010348593

theorem tailTrace_5578320 : CollatzResearch.WordTrace tailWord_5578320 prefixEnd_5578320 954786468196240010348593 := by
  unfold tailWord_5578320
  simp only [CollatzResearch.WordTrace]
  refine ⟨101729022575353408026346207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135638696767137877368461609 101729022575353408026346207)
  ·
    refine ⟨152593533863030112039519311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101729022575353408026346207 152593533863030112039519311)
    ·
      refine ⟨228890300794545168059278967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152593533863030112039519311 228890300794545168059278967)
      ·
        refine ⟨343335451191817752088918451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228890300794545168059278967 343335451191817752088918451)
        ·
          refine ⟨515003176787726628133377677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343335451191817752088918451 515003176787726628133377677)
          ·
            refine ⟨193126191295397485550016629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 515003176787726628133377677 193126191295397485550016629)
            ·
              refine ⟨18105580433943514270314059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193126191295397485550016629 18105580433943514270314059)
              ·
                refine ⟨27158370650915271405471089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18105580433943514270314059 27158370650915271405471089)
                ·
                  refine ⟨20368777988186453554103317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27158370650915271405471089 20368777988186453554103317)
                  ·
                    refine ⟨954786468196240010348593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20368777988186453554103317 954786468196240010348593)
                    ·
                      rfl

theorem cell23_5578320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_5578320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578320 prefixEnd_5578320 := by exact prefixLift 5578320
  have htrace : WordTrace (prefixWord ++ tailWord_5578320) baseStart_5578320 baseEnd_5578320 := by
    simpa [prefixWord, tailWord_5578320, baseEnd_5578320] using wordTrace_append hprefix tailTrace_5578320
  have hstable : (prefixWord ++ tailWord_5578320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578320).length < 2 ^ (prefixWord ++ tailWord_5578320).sum := by decide
  have hdescent : baseEnd_5578320 < baseStart_5578320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578330 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_5578330 : Nat := 118140960795 + 5578330 * 2 ^ 59
def prefixEnd_5578330 : Nat := 4983230072969 + 3 ^ 40 * 5578330 * 2
def baseEnd_5578330 : Nat := 2864364539395264991920733

theorem tailTrace_5578330 : CollatzResearch.WordTrace tailWord_5578330 prefixEnd_5578330 2864364539395264991920733 := by
  unfold tailWord_5578330
  simp only [CollatzResearch.WordTrace]
  refine ⟨50864602470167646940139111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135638939920447058507037629 50864602470167646940139111)
  ·
    refine ⟨76296903705251470410208667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50864602470167646940139111 76296903705251470410208667)
    ·
      refine ⟨114445355557877205615313001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76296903705251470410208667 114445355557877205615313001)
      ·
        refine ⟨85834016668407904211484751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114445355557877205615313001 85834016668407904211484751)
        ·
          refine ⟨128751025002611856317227127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85834016668407904211484751 128751025002611856317227127)
          ·
            refine ⟨193126537503917784475840691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128751025002611856317227127 193126537503917784475840691)
            ·
              refine ⟨289689806255876676713761037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193126537503917784475840691 289689806255876676713761037)
              ·
                refine ⟨108633677345953753767660389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289689806255876676713761037 108633677345953753767660389)
                ·
                  refine ⟨20368814502366328831436323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108633677345953753767660389 20368814502366328831436323)
                  ·
                    refine ⟨30553221753549493247154485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20368814502366328831436323 30553221753549493247154485)
                    ·
                      refine ⟨2864364539395264991920733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30553221753549493247154485 2864364539395264991920733)
                      ·
                        rfl

theorem cell23_5578330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_5578330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578330 prefixEnd_5578330 := by exact prefixLift 5578330
  have htrace : WordTrace (prefixWord ++ tailWord_5578330) baseStart_5578330 baseEnd_5578330 := by
    simpa [prefixWord, tailWord_5578330, baseEnd_5578330] using wordTrace_append hprefix tailTrace_5578330
  have hstable : (prefixWord ++ tailWord_5578330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578330).length < 2 ^ (prefixWord ++ tailWord_5578330).sum := by decide
  have hdescent : baseEnd_5578330 < baseStart_5578330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578377 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 2, 3, 3]
def baseStart_5578377 : Nat := 118140960795 + 5578377 * 2 ^ 59
def prefixEnd_5578377 : Nat := 4983230072969 + 3 ^ 40 * 5578377 * 2
def baseEnd_5578377 : Nat := 2864388672986026308033017

theorem tailTrace_5578377 : CollatzResearch.WordTrace tailWord_5578377 prefixEnd_5578377 2864388672986026308033017 := by
  unfold tailWord_5578377
  simp only [CollatzResearch.WordTrace]
  refine ⟨203460124111500314787517385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135640082741000209858344923 203460124111500314787517385)
  ·
    refine ⟨152595093083625236090638039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203460124111500314787517385 152595093083625236090638039)
    ·
      refine ⟨228892639625437854135957059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152595093083625236090638039 228892639625437854135957059)
      ·
        refine ⟨343338959438156781203935589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228892639625437854135957059 343338959438156781203935589)
        ·
          refine ⟨64376054894654396475737923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 343338959438156781203935589 64376054894654396475737923)
          ·
            refine ⟨96564082341981594713606885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64376054894654396475737923 96564082341981594713606885)
            ·
              refine ⟨18105765439121549008801291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96564082341981594713606885 18105765439121549008801291)
              ·
                refine ⟨27158648158682323513201937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18105765439121549008801291 27158648158682323513201937)
                ·
                  refine ⟨20368986119011742634901453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27158648158682323513201937 20368986119011742634901453)
                  ·
                    refine ⟨7638369794629403488088045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20368986119011742634901453 7638369794629403488088045)
                    ·
                      refine ⟨2864388672986026308033017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7638369794629403488088045 2864388672986026308033017)
                      ·
                        rfl

theorem cell23_5578377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3, 3].length) (baseStart_5578377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578377 prefixEnd_5578377 := by exact prefixLift 5578377
  have htrace : WordTrace (prefixWord ++ tailWord_5578377) baseStart_5578377 baseEnd_5578377 := by
    simpa [prefixWord, tailWord_5578377, baseEnd_5578377] using wordTrace_append hprefix tailTrace_5578377
  have hstable : (prefixWord ++ tailWord_5578377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578377).length < 2 ^ (prefixWord ++ tailWord_5578377).sum := by decide
  have hdescent : baseEnd_5578377 < baseStart_5578377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578380 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_5578380 : Nat := 118140960795 + 5578380 * 2 ^ 59
def prefixEnd_5578380 : Nat := 4983230072969 + 3 ^ 40 * 5578380 * 2
def baseEnd_5578380 : Nat := 954796737809329932098501

theorem tailTrace_5578380 : CollatzResearch.WordTrace tailWord_5578380 prefixEnd_5578380 954796737809329932098501 := by
  unfold tailWord_5578380
  simp only [CollatzResearch.WordTrace]
  refine ⟨101730116765244723149938297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135640155686992964199917729 101730116765244723149938297)
  ·
    refine ⟨76297587573933542362453723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101730116765244723149938297 76297587573933542362453723)
    ·
      refine ⟨114446381360900313543680585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76297587573933542362453723 114446381360900313543680585)
      ·
        refine ⟨85834786020675235157760439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114446381360900313543680585 85834786020675235157760439)
        ·
          refine ⟨128752179031012852736640659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85834786020675235157760439 128752179031012852736640659)
          ·
            refine ⟨193128268546519279104960989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128752179031012852736640659 193128268546519279104960989)
            ·
              refine ⟨72423100704944729664360371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193128268546519279104960989 72423100704944729664360371)
              ·
                refine ⟨108634651057417094496540557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72423100704944729664360371 108634651057417094496540557)
                ·
                  refine ⟨40737994146531410436202709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108634651057417094496540557 40737994146531410436202709)
                  ·
                    refine ⟨954796737809329932098501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40737994146531410436202709 954796737809329932098501)
                    ·
                      rfl

theorem cell23_5578380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_5578380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578380 prefixEnd_5578380 := by exact prefixLift 5578380
  have htrace : WordTrace (prefixWord ++ tailWord_5578380) baseStart_5578380 baseEnd_5578380 := by
    simpa [prefixWord, tailWord_5578380, baseEnd_5578380] using wordTrace_append hprefix tailTrace_5578380
  have hstable : (prefixWord ++ tailWord_5578380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578380).length < 2 ^ (prefixWord ++ tailWord_5578380).sum := by decide
  have hdescent : baseEnd_5578380 < baseStart_5578380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578397 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_5578397 : Nat := 118140960795 + 5578397 * 2 ^ 59
def prefixEnd_5578397 : Nat := 4983230072969 + 3 ^ 40 * 5578397 * 2
def baseEnd_5578397 : Nat := 954799647533038743260975

theorem tailTrace_5578397 : CollatzResearch.WordTrace tailWord_5578397 prefixEnd_5578397 954799647533038743260975 := by
  unfold tailWord_5578397
  simp only [CollatzResearch.WordTrace]
  refine ⟨203460853571427858203245445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135640569047618572135496963 203460853571427858203245445)
  ·
    refine ⟨38148910044642723413108521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203460853571427858203245445 38148910044642723413108521)
    ·
      refine ⟨28611682533482042559831391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38148910044642723413108521 28611682533482042559831391)
      ·
        refine ⟨42917523800223063839747087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28611682533482042559831391 42917523800223063839747087)
        ·
          refine ⟨64376285700334595759620631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42917523800223063839747087 64376285700334595759620631)
          ·
            refine ⟨96564428550501893639430947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64376285700334595759620631 96564428550501893639430947)
            ·
              refine ⟨144846642825752840459146421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96564428550501893639430947 144846642825752840459146421)
              ·
                refine ⟨13579372764914328793044977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144846642825752840459146421 13579372764914328793044977)
                ·
                  refine ⟨10184529573685746594783733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13579372764914328793044977 10184529573685746594783733)
                  ·
                    refine ⟨954799647533038743260975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10184529573685746594783733 954799647533038743260975)
                    ·
                      rfl

theorem cell23_5578397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_5578397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578397 prefixEnd_5578397 := by exact prefixLift 5578397
  have htrace : WordTrace (prefixWord ++ tailWord_5578397) baseStart_5578397 baseEnd_5578397 := by
    simpa [prefixWord, tailWord_5578397, baseEnd_5578397] using wordTrace_append hprefix tailTrace_5578397
  have hstable : (prefixWord ++ tailWord_5578397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578397).length < 2 ^ (prefixWord ++ tailWord_5578397).sum := by decide
  have hdescent : baseEnd_5578397 < baseStart_5578397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578401 : List Nat := [1, 2, 3, 3, 2, 3, 1, 3, 5]
def baseStart_5578401 : Nat := 118140960795 + 5578401 * 2 ^ 59
def prefixEnd_5578401 : Nat := 4983230072969 + 3 ^ 40 * 5578401 * 2
def baseEnd_5578401 : Nat := 318266777391303801570323

theorem tailTrace_5578401 : CollatzResearch.WordTrace tailWord_5578401 prefixEnd_5578401 318266777391303801570323 := by
  unfold tailWord_5578401
  simp only [CollatzResearch.WordTrace]
  refine ⟨203460999463413366886391057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135640666308942244590927371 203460999463413366886391057)
  ·
    refine ⟨152595749597560025164793293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203460999463413366886391057 152595749597560025164793293)
    ·
      refine ⟨57223406099085009436797485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152595749597560025164793293 57223406099085009436797485)
      ·
        refine ⟨21458777287156878538799057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57223406099085009436797485 21458777287156878538799057)
        ·
          refine ⟨16094082965367658904099293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21458777287156878538799057 16094082965367658904099293)
          ·
            refine ⟨6035281112012872089037235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16094082965367658904099293 6035281112012872089037235)
            ·
              refine ⟨9052921668019308133555853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6035281112012872089037235 9052921668019308133555853)
              ·
                refine ⟨3394845625507240550083445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9052921668019308133555853 3394845625507240550083445)
                ·
                  refine ⟨318266777391303801570323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3394845625507240550083445 318266777391303801570323)
                  ·
                    rfl

theorem cell23_5578401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 5].length) (baseStart_5578401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578401 prefixEnd_5578401 := by exact prefixLift 5578401
  have htrace : WordTrace (prefixWord ++ tailWord_5578401) baseStart_5578401 baseEnd_5578401 := by
    simpa [prefixWord, tailWord_5578401, baseEnd_5578401] using wordTrace_append hprefix tailTrace_5578401
  have hstable : (prefixWord ++ tailWord_5578401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578401).length < 2 ^ (prefixWord ++ tailWord_5578401).sum := by decide
  have hdescent : baseEnd_5578401 < baseStart_5578401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578487 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 3, 5]
def baseStart_5578487 : Nat := 118140960795 + 5578487 * 2 ^ 59
def prefixEnd_5578487 : Nat := 4983230072969 + 3 ^ 40 * 5578487 * 2
def baseEnd_5578487 : Nat := 954815051952673625885837

theorem tailTrace_5578487 : CollatzResearch.WordTrace tailWord_5578487 prefixEnd_5578487 954815051952673625885837 := by
  unfold tailWord_5578487
  simp only [CollatzResearch.WordTrace]
  refine ⟨203464136141101803574021715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135642757427401202382681143 203464136141101803574021715)
  ·
    refine ⟨305196204211652705361032573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203464136141101803574021715 305196204211652705361032573)
    ·
      refine ⟨114448576579369764510387215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305196204211652705361032573 114448576579369764510387215)
      ·
        refine ⟨171672864869054646765580823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114448576579369764510387215 171672864869054646765580823)
        ·
          refine ⟨257509297303581970148371235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171672864869054646765580823 257509297303581970148371235)
          ·
            refine ⟨386263945955372955222556853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257509297303581970148371235 386263945955372955222556853)
            ·
              refine ⟨36212244933316214552114705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 386263945955372955222556853 36212244933316214552114705)
              ·
                refine ⟨27159183699987160914086029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36212244933316214552114705 27159183699987160914086029)
                ·
                  refine ⟨10184693887495185342782261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27159183699987160914086029 10184693887495185342782261)
                  ·
                    refine ⟨954815051952673625885837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10184693887495185342782261 954815051952673625885837)
                    ·
                      rfl

theorem cell23_5578487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_5578487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578487 prefixEnd_5578487 := by exact prefixLift 5578487
  have htrace : WordTrace (prefixWord ++ tailWord_5578487) baseStart_5578487 baseEnd_5578487 := by
    simpa [prefixWord, tailWord_5578487, baseEnd_5578487] using wordTrace_append hprefix tailTrace_5578487
  have hstable : (prefixWord ++ tailWord_5578487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578487).length < 2 ^ (prefixWord ++ tailWord_5578487).sum := by decide
  have hdescent : baseEnd_5578487 < baseStart_5578487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578502 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5578502 : Nat := 118140960795 + 5578502 * 2 ^ 59
def prefixEnd_5578502 : Nat := 4983230072969 + 3 ^ 40 * 5578502 * 2
def baseEnd_5578502 : Nat := 2864452858067838318969943

theorem tailTrace_5578502 : CollatzResearch.WordTrace tailWord_5578502 prefixEnd_5578502 2864452858067838318969943 := by
  unfold tailWord_5578502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6358271351126483160494305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135643122157364974090545173 6358271351126483160494305)
  ·
    refine ⟨4768703513344862370370729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6358271351126483160494305 4768703513344862370370729)
    ·
      refine ⟨3576527635008646777778047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4768703513344862370370729 3576527635008646777778047)
      ·
        refine ⟨5364791452512970166667071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3576527635008646777778047 5364791452512970166667071)
        ·
          refine ⟨8047187178769455250000607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5364791452512970166667071 8047187178769455250000607)
          ·
            refine ⟨12070780768154182875000911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8047187178769455250000607 12070780768154182875000911)
            ·
              refine ⟨18106171152231274312501367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12070780768154182875000911 18106171152231274312501367)
              ·
                refine ⟨27159256728346911468752051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18106171152231274312501367 27159256728346911468752051)
                ·
                  refine ⟨40738885092520367203128077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27159256728346911468752051 40738885092520367203128077)
                  ·
                    refine ⟨15277081909695137701173029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40738885092520367203128077 15277081909695137701173029)
                    ·
                      refine ⟨2864452858067838318969943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15277081909695137701173029 2864452858067838318969943)
                      ·
                        rfl

theorem cell23_5578502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5578502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578502 prefixEnd_5578502 := by exact prefixLift 5578502
  have htrace : WordTrace (prefixWord ++ tailWord_5578502) baseStart_5578502 baseEnd_5578502 := by
    simpa [prefixWord, tailWord_5578502, baseEnd_5578502] using wordTrace_append hprefix tailTrace_5578502
  have hstable : (prefixWord ++ tailWord_5578502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578502).length < 2 ^ (prefixWord ++ tailWord_5578502).sum := by decide
  have hdescent : baseEnd_5578502 < baseStart_5578502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578504 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 1, 5]
def baseStart_5578504 : Nat := 118140960795 + 5578504 * 2 ^ 59
def prefixEnd_5578504 : Nat := 4983230072969 + 3 ^ 40 * 5578504 * 2
def baseEnd_5578504 : Nat := 954817961676382437048311

theorem tailTrace_5578504 : CollatzResearch.WordTrace tailWord_5578504 prefixEnd_5578504 954817961676382437048311 := by
  unfold tailWord_5578504
  simp only [CollatzResearch.WordTrace]
  refine ⟨101732378091020107738695283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135643170788026810318260377 101732378091020107738695283)
  ·
    refine ⟨152598567136530161608042925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101732378091020107738695283 152598567136530161608042925)
    ·
      refine ⟨57224462676198810603016097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152598567136530161608042925 57224462676198810603016097)
      ·
        refine ⟨42918347007149107952262073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57224462676198810603016097 42918347007149107952262073)
        ·
          refine ⟨32188760255361830964196555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42918347007149107952262073 32188760255361830964196555)
          ·
            refine ⟨48283140383042746446294833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32188760255361830964196555 48283140383042746446294833)
            ·
              refine ⟨36212355287282059834721125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48283140383042746446294833 36212355287282059834721125)
              ·
                refine ⟨6789816616365386219010211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36212355287282059834721125 6789816616365386219010211)
                ·
                  refine ⟨10184724924548079328515317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6789816616365386219010211 10184724924548079328515317)
                  ·
                    refine ⟨954817961676382437048311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10184724924548079328515317 954817961676382437048311)
                    ·
                      rfl

theorem cell23_5578504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_5578504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578504 prefixEnd_5578504 := by exact prefixLift 5578504
  have htrace : WordTrace (prefixWord ++ tailWord_5578504) baseStart_5578504 baseEnd_5578504 := by
    simpa [prefixWord, tailWord_5578504, baseEnd_5578504] using wordTrace_append hprefix tailTrace_5578504
  have hstable : (prefixWord ++ tailWord_5578504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578504).length < 2 ^ (prefixWord ++ tailWord_5578504).sum := by decide
  have hdescent : baseEnd_5578504 < baseStart_5578504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578554 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_5578554 : Nat := 118140960795 + 5578554 * 2 ^ 59
def prefixEnd_5578554 : Nat := 4983230072969 + 3 ^ 40 * 5578554 * 2
def baseEnd_5578554 : Nat := 2864479559061872115519703

theorem tailTrace_5578554 : CollatzResearch.WordTrace tailWord_5578554 prefixEnd_5578554 2864479559061872115519703 := by
  unfold tailWord_5578554
  simp only [CollatzResearch.WordTrace]
  refine ⟨50866644957964768504177679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135644386554572716011140477 50866644957964768504177679)
  ·
    refine ⟨76299967436947152756266519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50866644957964768504177679 76299967436947152756266519)
    ·
      refine ⟨114449951155420729134399779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76299967436947152756266519 114449951155420729134399779)
      ·
        refine ⟨171674926733131093701599669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114449951155420729134399779 171674926733131093701599669)
        ·
          refine ⟨16094524381231040034524969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 171674926733131093701599669 16094524381231040034524969)
          ·
            refine ⟨12070893285923280025893727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16094524381231040034524969 12070893285923280025893727)
            ·
              refine ⟨18106339928884920038840591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12070893285923280025893727 18106339928884920038840591)
              ·
                refine ⟨27159509893327380058260887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18106339928884920038840591 27159509893327380058260887)
                ·
                  refine ⟨40739264839991070087391331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27159509893327380058260887 40739264839991070087391331)
                  ·
                    refine ⟨61108897259986605131086997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40739264839991070087391331 61108897259986605131086997)
                    ·
                      refine ⟨2864479559061872115519703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61108897259986605131086997 2864479559061872115519703)
                      ·
                        rfl

theorem cell23_5578554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_5578554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578554 prefixEnd_5578554 := by exact prefixLift 5578554
  have htrace : WordTrace (prefixWord ++ tailWord_5578554) baseStart_5578554 baseEnd_5578554 := by
    simpa [prefixWord, tailWord_5578554, baseEnd_5578554] using wordTrace_append hprefix tailTrace_5578554
  have hstable : (prefixWord ++ tailWord_5578554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578554).length < 2 ^ (prefixWord ++ tailWord_5578554).sum := by decide
  have hdescent : baseEnd_5578554 < baseStart_5578554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578558 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_5578558 : Nat := 118140960795 + 5578558 * 2 ^ 59
def prefixEnd_5578558 : Nat := 4983230072969 + 3 ^ 40 * 5578558 * 2
def baseEnd_5578558 : Nat := 2864481612984490099869685

theorem tailTrace_5578558 : CollatzResearch.WordTrace tailWord_5578558 prefixEnd_5578558 2864481612984490099869685 := by
  unfold tailWord_5578558
  simp only [CollatzResearch.WordTrace]
  refine ⟨25433340715480572837482041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135644483815896388466570885 25433340715480572837482041)
  ·
    refine ⟨19075005536610429628111531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25433340715480572837482041 19075005536610429628111531)
    ·
      refine ⟨28612508304915644442167297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19075005536610429628111531 28612508304915644442167297)
      ·
        refine ⟨21459381228686733331625473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28612508304915644442167297 21459381228686733331625473)
        ·
          refine ⟨16094535921515049998719105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21459381228686733331625473 16094535921515049998719105)
          ·
            refine ⟨12070901941136287499039329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16094535921515049998719105 12070901941136287499039329)
            ·
              refine ⟨9053176455852215624279497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12070901941136287499039329 9053176455852215624279497)
              ·
                refine ⟨6789882341889161718209623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9053176455852215624279497 6789882341889161718209623)
                ·
                  refine ⟨10184823512833742577314435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6789882341889161718209623 10184823512833742577314435)
                  ·
                    refine ⟨15277235269250613865971653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10184823512833742577314435 15277235269250613865971653)
                    ·
                      refine ⟨2864481612984490099869685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15277235269250613865971653 2864481612984490099869685)
                      ·
                        rfl

theorem cell23_5578558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_5578558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578558 prefixEnd_5578558 := by exact prefixLift 5578558
  have htrace : WordTrace (prefixWord ++ tailWord_5578558) baseStart_5578558 baseEnd_5578558 := by
    simpa [prefixWord, tailWord_5578558, baseEnd_5578558] using wordTrace_append hprefix tailTrace_5578558
  have hstable : (prefixWord ++ tailWord_5578558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578558).length < 2 ^ (prefixWord ++ tailWord_5578558).sum := by decide
  have hdescent : baseEnd_5578558 < baseStart_5578558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578591 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 4, 1, 3]
def baseStart_5578591 : Nat := 118140960795 + 5578591 * 2 ^ 59
def prefixEnd_5578591 : Nat := 4983230072969 + 3 ^ 40 * 5578591 * 2
def baseEnd_5578591 : Nat := 2864498557846088470757033

theorem tailTrace_5578591 : CollatzResearch.WordTrace tailWord_5578591 prefixEnd_5578591 2864498557846088470757033 := by
  unfold tailWord_5578591
  simp only [CollatzResearch.WordTrace]
  refine ⟨203467929332725029335807627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135645286221816686223871751 203467929332725029335807627)
  ·
    refine ⟨305201893999087544003711441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203467929332725029335807627 305201893999087544003711441)
    ·
      refine ⟨228901420499315658002783581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305201893999087544003711441 228901420499315658002783581)
      ·
        refine ⟨85838032687243371751043843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228901420499315658002783581 85838032687243371751043843)
        ·
          refine ⟨128757049030865057626565765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85838032687243371751043843 128757049030865057626565765)
          ·
            refine ⟨24141946693287198304981081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128757049030865057626565765 24141946693287198304981081)
            ·
              refine ⟨18106460019965398728735811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24141946693287198304981081 18106460019965398728735811)
              ·
                refine ⟨27159690029948098093103717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18106460019965398728735811 27159690029948098093103717)
                ·
                  refine ⟨5092441880615268392456947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27159690029948098093103717 5092441880615268392456947)
                  ·
                    refine ⟨7638662820922902588685421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5092441880615268392456947 7638662820922902588685421)
                    ·
                      refine ⟨2864498557846088470757033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7638662820922902588685421 2864498557846088470757033)
                      ·
                        rfl

theorem cell23_5578591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_5578591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578591 prefixEnd_5578591 := by exact prefixLift 5578591
  have htrace : WordTrace (prefixWord ++ tailWord_5578591) baseStart_5578591 baseEnd_5578591 := by
    simpa [prefixWord, tailWord_5578591, baseEnd_5578591] using wordTrace_append hprefix tailTrace_5578591
  have hstable : (prefixWord ++ tailWord_5578591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578591).length < 2 ^ (prefixWord ++ tailWord_5578591).sum := by decide
  have hdescent : baseEnd_5578591 < baseStart_5578591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578592 : List Nat := [2, 1, 1, 3, 3, 3, 3, 2, 1, 2, 2]
def baseStart_5578592 : Nat := 118140960795 + 5578592 * 2 ^ 59
def prefixEnd_5578592 : Nat := 4983230072969 + 3 ^ 40 * 5578592 * 2
def baseEnd_5578592 : Nat := 2864499071326742966844529

theorem tailTrace_5578592 : CollatzResearch.WordTrace tailWord_5578592 prefixEnd_5578592 2864499071326742966844529 := by
  unfold tailWord_5578592
  simp only [CollatzResearch.WordTrace]
  refine ⟨101733982902860703253297015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135645310537147604337729353 101733982902860703253297015)
  ·
    refine ⟨152600974354291054879945523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101733982902860703253297015 152600974354291054879945523)
    ·
      refine ⟨228901461531436582319918285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152600974354291054879945523 228901461531436582319918285)
      ·
        refine ⟨85838048074288718369969357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228901461531436582319918285 85838048074288718369969357)
        ·
          refine ⟨32189268027858269388738509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85838048074288718369969357 32189268027858269388738509)
          ·
            refine ⟨12070975510446851020776941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32189268027858269388738509 12070975510446851020776941)
            ·
              refine ⟨4526615816417569132791353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12070975510446851020776941 4526615816417569132791353)
              ·
                refine ⟨3394961862313176849593515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4526615816417569132791353 3394961862313176849593515)
                ·
                  refine ⟨5092442793469765274390273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3394961862313176849593515 5092442793469765274390273)
                  ·
                    refine ⟨3819332095102323955792705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5092442793469765274390273 3819332095102323955792705)
                    ·
                      refine ⟨2864499071326742966844529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3819332095102323955792705 2864499071326742966844529)
                      ·
                        rfl

theorem cell23_5578592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_5578592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578592 prefixEnd_5578592 := by exact prefixLift 5578592
  have htrace : WordTrace (prefixWord ++ tailWord_5578592) baseStart_5578592 baseEnd_5578592 := by
    simpa [prefixWord, tailWord_5578592, baseEnd_5578592] using wordTrace_append hprefix tailTrace_5578592
  have hstable : (prefixWord ++ tailWord_5578592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578592).length < 2 ^ (prefixWord ++ tailWord_5578592).sum := by decide
  have hdescent : baseEnd_5578592 < baseStart_5578592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578602 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 2, 4]
def baseStart_5578602 : Nat := 118140960795 + 5578602 * 2 ^ 59
def prefixEnd_5578602 : Nat := 4983230072969 + 3 ^ 40 * 5578602 * 2
def baseEnd_5578602 : Nat := 954834735377762642573161

theorem tailTrace_5578602 : CollatzResearch.WordTrace tailWord_5578602 prefixEnd_5578602 954834735377762642573161 := by
  unfold tailWord_5578602
  simp only [CollatzResearch.WordTrace]
  refine ⟨50867082633921294553614515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135645553690456785476305373 50867082633921294553614515)
  ·
    refine ⟨76300623950881941830421773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50867082633921294553614515 76300623950881941830421773)
    ·
      refine ⟨28612733981580728186408165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76300623950881941830421773 28612733981580728186408165)
      ·
        refine ⟨5364887621546386534951531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28612733981580728186408165 5364887621546386534951531)
        ·
          refine ⟨8047331432319579802427297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5364887621546386534951531 8047331432319579802427297)
          ·
            refine ⟨6035498574239684851820473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8047331432319579802427297 6035498574239684851820473)
            ·
              refine ⟨4526623930679763638865355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6035498574239684851820473 4526623930679763638865355)
              ·
                refine ⟨6789935896019645458298033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4526623930679763638865355 6789935896019645458298033)
                ·
                  refine ⟨5092451922014734093723525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6789935896019645458298033 5092451922014734093723525)
                  ·
                    refine ⟨954834735377762642573161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5092451922014734093723525 954834735377762642573161)
                    ·
                      rfl

theorem cell23_5578602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_5578602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578602 prefixEnd_5578602 := by exact prefixLift 5578602
  have htrace : WordTrace (prefixWord ++ tailWord_5578602) baseStart_5578602 baseEnd_5578602 := by
    simpa [prefixWord, tailWord_5578602, baseEnd_5578602] using wordTrace_append hprefix tailTrace_5578602
  have hstable : (prefixWord ++ tailWord_5578602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578602).length < 2 ^ (prefixWord ++ tailWord_5578602).sum := by decide
  have hdescent : baseEnd_5578602 < baseStart_5578602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578618 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2]
def baseStart_5578618 : Nat := 118140960795 + 5578618 * 2 ^ 59
def prefixEnd_5578618 : Nat := 4983230072969 + 3 ^ 40 * 5578618 * 2
def baseEnd_5578618 : Nat := 2864512421823759865119409

theorem tailTrace_5578618 : CollatzResearch.WordTrace tailWord_5578618 prefixEnd_5578618 2864512421823759865119409 := by
  unfold tailWord_5578618
  simp only [CollatzResearch.WordTrace]
  refine ⟨50867228525906803236760127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135645942735751475298027005 50867228525906803236760127)
  ·
    refine ⟨76300842788860204855140191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50867228525906803236760127 76300842788860204855140191)
    ·
      refine ⟨114451264183290307282710287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76300842788860204855140191 114451264183290307282710287)
      ·
        refine ⟨171676896274935460924065431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114451264183290307282710287 171676896274935460924065431)
        ·
          refine ⟨257515344412403191386098147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171676896274935460924065431 257515344412403191386098147)
          ·
            refine ⟨386273016618604787079147221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257515344412403191386098147 386273016618604787079147221)
            ·
              refine ⟨9053273826998549697167513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 386273016618604787079147221 9053273826998549697167513)
              ·
                refine ⟨6789955370248912272875635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9053273826998549697167513 6789955370248912272875635)
                ·
                  refine ⟨10184933055373368409313453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6789955370248912272875635 10184933055373368409313453)
                  ·
                    refine ⟨3819349895765013153492545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10184933055373368409313453 3819349895765013153492545)
                    ·
                      refine ⟨2864512421823759865119409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3819349895765013153492545 2864512421823759865119409)
                      ·
                        rfl

theorem cell23_5578618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2].length) (baseStart_5578618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578618 prefixEnd_5578618 := by exact prefixLift 5578618
  have htrace : WordTrace (prefixWord ++ tailWord_5578618) baseStart_5578618 baseEnd_5578618 := by
    simpa [prefixWord, tailWord_5578618, baseEnd_5578618] using wordTrace_append hprefix tailTrace_5578618
  have hstable : (prefixWord ++ tailWord_5578618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578618).length < 2 ^ (prefixWord ++ tailWord_5578618).sum := by decide
  have hdescent : baseEnd_5578618 < baseStart_5578618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578716 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_5578716 : Nat := 118140960795 + 5578716 * 2 ^ 59
def prefixEnd_5578716 : Nat := 4983230072969 + 3 ^ 40 * 5578716 * 2
def baseEnd_5578716 : Nat := 2864562742927900481693959

theorem tailTrace_5578716 : CollatzResearch.WordTrace tailWord_5578716 prefixEnd_5578716 2864562742927900481693959 := by
  unfold tailWord_5578716
  simp only [CollatzResearch.WordTrace]
  refine ⟨101736244228636087842054001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135648325638181450456072001 101736244228636087842054001)
  ·
    refine ⟨76302183171477065881540501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101736244228636087842054001 76302183171477065881540501)
    ·
      refine ⟨3576664836162987463197211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76302183171477065881540501 3576664836162987463197211)
      ·
        refine ⟨5364997254244481194795817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3576664836162987463197211 5364997254244481194795817)
        ·
          refine ⟨4023747940683360896096863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5364997254244481194795817 4023747940683360896096863)
          ·
            refine ⟨6035621911025041344145295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4023747940683360896096863 6035621911025041344145295)
            ·
              refine ⟨9053432866537562016217943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6035621911025041344145295 9053432866537562016217943)
              ·
                refine ⟨13580149299806343024326915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9053432866537562016217943 13580149299806343024326915)
                ·
                  refine ⟨20370223949709514536490373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13580149299806343024326915 20370223949709514536490373)
                  ·
                    refine ⟨3819416990570533975591945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20370223949709514536490373 3819416990570533975591945)
                    ·
                      refine ⟨2864562742927900481693959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3819416990570533975591945 2864562742927900481693959)
                      ·
                        rfl

theorem cell23_5578716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_5578716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578716 prefixEnd_5578716 := by exact prefixLift 5578716
  have htrace : WordTrace (prefixWord ++ tailWord_5578716) baseStart_5578716 baseEnd_5578716 := by
    simpa [prefixWord, tailWord_5578716, baseEnd_5578716] using wordTrace_append hprefix tailTrace_5578716
  have hstable : (prefixWord ++ tailWord_5578716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578716).length < 2 ^ (prefixWord ++ tailWord_5578716).sum := by decide
  have hdescent : baseEnd_5578716 < baseStart_5578716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578744 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 8]
def baseStart_5578744 : Nat := 118140960795 + 5578744 * 2 ^ 59
def prefixEnd_5578744 : Nat := 4983230072969 + 3 ^ 40 * 5578744 * 2
def baseEnd_5578744 : Nat := 318286346709580708015981

theorem tailTrace_5578744 : CollatzResearch.WordTrace tailWord_5578744 prefixEnd_5578744 318286346709580708015981 := by
  unfold tailWord_5578744
  simp only [CollatzResearch.WordTrace]
  refine ⟨101736754850585368233063643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135649006467447157644084857 101736754850585368233063643)
  ·
    refine ⟨152605132275878052349595465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101736754850585368233063643 152605132275878052349595465)
    ·
      refine ⟨114453849206908539262196599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152605132275878052349595465 114453849206908539262196599)
      ·
        refine ⟨171680773810362808893294899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114453849206908539262196599 171680773810362808893294899)
        ·
          refine ⟨257521160715544213339942349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171680773810362808893294899 257521160715544213339942349)
          ·
            refine ⟨96570435268329080002478381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257521160715544213339942349 96570435268329080002478381)
            ·
              refine ⟨36213913225623405000929393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96570435268329080002478381 36213913225623405000929393)
              ·
                refine ⟨27160434919217553750697045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36213913225623405000929393 27160434919217553750697045)
                ·
                  refine ⟨318286346709580708015981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27160434919217553750697045 318286346709580708015981)
                  ·
                    rfl

theorem cell23_5578744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 8].length) (baseStart_5578744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578744 prefixEnd_5578744 := by exact prefixLift 5578744
  have htrace : WordTrace (prefixWord ++ tailWord_5578744) baseStart_5578744 baseEnd_5578744 := by
    simpa [prefixWord, tailWord_5578744, baseEnd_5578744] using wordTrace_append hprefix tailTrace_5578744
  have hstable : (prefixWord ++ tailWord_5578744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578744).length < 2 ^ (prefixWord ++ tailWord_5578744).sum := by decide
  have hdescent : baseEnd_5578744 < baseStart_5578744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578778 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 6]
def baseStart_5578778 : Nat := 118140960795 + 5578778 * 2 ^ 59
def prefixEnd_5578778 : Nat := 4983230072969 + 3 ^ 40 * 5578778 * 2
def baseEnd_5578778 : Nat := 318288286525386582124297

theorem tailTrace_5578778 : CollatzResearch.WordTrace tailWord_5578778 prefixEnd_5578778 318288286525386582124297 := by
  unfold tailWord_5578778
  simp only [CollatzResearch.WordTrace]
  refine ⟨50868687445761890068216247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135649833188698373515243325 50868687445761890068216247)
  ·
    refine ⟨76303031168642835102324371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50868687445761890068216247 76303031168642835102324371)
    ·
      refine ⟨114454546752964252653486557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76303031168642835102324371 114454546752964252653486557)
      ·
        refine ⟨42920455032361594745057459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114454546752964252653486557 42920455032361594745057459)
        ·
          refine ⟨64380682548542392117586189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42920455032361594745057459 64380682548542392117586189)
          ·
            refine ⟨24142755955703397044094821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64380682548542392117586189 24142755955703397044094821)
            ·
              refine ⟨4526766741694386945767779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24142755955703397044094821 4526766741694386945767779)
              ·
                refine ⟨6790150112541580418651669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4526766741694386945767779 6790150112541580418651669)
                ·
                  refine ⟨318288286525386582124297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6790150112541580418651669 318288286525386582124297)
                  ·
                    rfl

theorem cell23_5578778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_5578778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578778 prefixEnd_5578778 := by exact prefixLift 5578778
  have htrace : WordTrace (prefixWord ++ tailWord_5578778) baseStart_5578778 baseEnd_5578778 := by
    simpa [prefixWord, tailWord_5578778, baseEnd_5578778] using wordTrace_append hprefix tailTrace_5578778
  have hstable : (prefixWord ++ tailWord_5578778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578778).length < 2 ^ (prefixWord ++ tailWord_5578778).sum := by decide
  have hdescent : baseEnd_5578778 < baseStart_5578778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578792 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5578792 : Nat := 118140960795 + 5578792 * 2 ^ 59
def prefixEnd_5578792 : Nat := 4983230072969 + 3 ^ 40 * 5578792 * 2
def baseEnd_5578792 : Nat := 2864601767457642184343609

theorem tailTrace_5578792 : CollatzResearch.WordTrace tailWord_5578792 prefixEnd_5578792 2864601767457642184343609 := by
  unfold tailWord_5578792
  simp only [CollatzResearch.WordTrace]
  refine ⟨101737630202498420331937315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135650173603331227109249753 101737630202498420331937315)
  ·
    refine ⟨152606445303747630497905973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101737630202498420331937315 152606445303747630497905973)
    ·
      refine ⟨14306854247226340359178685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152606445303747630497905973 14306854247226340359178685)
      ·
        refine ⟨5365070342709877634692007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14306854247226340359178685 5365070342709877634692007)
        ·
          refine ⟨8047605514064816452038011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365070342709877634692007 8047605514064816452038011)
          ·
            refine ⟨12071408271097224678057017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8047605514064816452038011 12071408271097224678057017)
            ·
              refine ⟨9053556203322918508542763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12071408271097224678057017 9053556203322918508542763)
              ·
                refine ⟨13580334304984377762814145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9053556203322918508542763 13580334304984377762814145)
                ·
                  refine ⟨10185250728738283322110609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13580334304984377762814145 10185250728738283322110609)
                  ·
                    refine ⟨7638938046553712491582957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10185250728738283322110609 7638938046553712491582957)
                    ·
                      refine ⟨2864601767457642184343609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7638938046553712491582957 2864601767457642184343609)
                      ·
                        rfl

theorem cell23_5578792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5578792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578792 prefixEnd_5578792 := by exact prefixLift 5578792
  have htrace : WordTrace (prefixWord ++ tailWord_5578792) baseStart_5578792 baseEnd_5578792 := by
    simpa [prefixWord, tailWord_5578792, baseEnd_5578792] using wordTrace_append hprefix tailTrace_5578792
  have hstable : (prefixWord ++ tailWord_5578792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578792).length < 2 ^ (prefixWord ++ tailWord_5578792).sum := by decide
  have hdescent : baseEnd_5578792 < baseStart_5578792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578822 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_5578822 : Nat := 118140960795 + 5578822 * 2 ^ 59
def prefixEnd_5578822 : Nat := 4983230072969 + 3 ^ 40 * 5578822 * 2
def baseEnd_5578822 : Nat := 2864617171877277066968471

theorem tailTrace_5578822 : CollatzResearch.WordTrace tailWord_5578822 prefixEnd_5578822 2864617171877277066968471 := by
  unfold tailWord_5578822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6358636081090254868358335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 135650903063258770524977813 6358636081090254868358335)
  ·
    refine ⟨9537954121635382302537503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6358636081090254868358335 9537954121635382302537503)
    ·
      refine ⟨14306931182453073453806255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9537954121635382302537503 14306931182453073453806255)
      ·
        refine ⟨21460396773679610180709383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14306931182453073453806255 21460396773679610180709383)
        ·
          refine ⟨32190595160519415271064075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21460396773679610180709383 32190595160519415271064075)
          ·
            refine ⟨48285892740779122906596113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32190595160519415271064075 48285892740779122906596113)
            ·
              refine ⟨36214419555584342179947085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48285892740779122906596113 36214419555584342179947085)
              ·
                refine ⟨13580407333344128317480157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36214419555584342179947085 13580407333344128317480157)
                ·
                  refine ⟨5092652750004048119055059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13580407333344128317480157 5092652750004048119055059)
                  ·
                    refine ⟨7638979125006072178582589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5092652750004048119055059 7638979125006072178582589)
                    ·
                      refine ⟨2864617171877277066968471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7638979125006072178582589 2864617171877277066968471)
                      ·
                        rfl

theorem cell23_5578822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_5578822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578822 prefixEnd_5578822 := by exact prefixLift 5578822
  have htrace : WordTrace (prefixWord ++ tailWord_5578822) baseStart_5578822 baseEnd_5578822 := by
    simpa [prefixWord, tailWord_5578822, baseEnd_5578822] using wordTrace_append hprefix tailTrace_5578822
  have hstable : (prefixWord ++ tailWord_5578822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578822).length < 2 ^ (prefixWord ++ tailWord_5578822).sum := by decide
  have hdescent : baseEnd_5578822 < baseStart_5578822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578845 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_5578845 : Nat := 118140960795 + 5578845 * 2 ^ 59
def prefixEnd_5578845 : Nat := 4983230072969 + 3 ^ 40 * 5578845 * 2
def baseEnd_5578845 : Nat := 2864628981932330476980865

theorem tailTrace_5578845 : CollatzResearch.WordTrace tailWord_5578845 prefixEnd_5578845 2864628981932330476980865 := by
  unfold tailWord_5578845
  simp only [CollatzResearch.WordTrace]
  refine ⟨203477193473804830715553989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135651462315869887143702659 203477193473804830715553989)
  ·
    refine ⟨38151973776338405759166373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203477193473804830715553989 38151973776338405759166373)
    ·
      refine ⟨7153495083063451079843695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38151973776338405759166373 7153495083063451079843695)
      ·
        refine ⟨10730242624595176619765543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7153495083063451079843695 10730242624595176619765543)
        ·
          refine ⟨16095363936892764929648315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10730242624595176619765543 16095363936892764929648315)
          ·
            refine ⟨24143045905339147394472473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16095363936892764929648315 24143045905339147394472473)
            ·
              refine ⟨18107284429004360545854355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24143045905339147394472473 18107284429004360545854355)
              ·
                refine ⟨27160926643506540818781533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18107284429004360545854355 27160926643506540818781533)
                ·
                  refine ⟨10185347491314952807043075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27160926643506540818781533 10185347491314952807043075)
                  ·
                    refine ⟨15278021236972429210564613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10185347491314952807043075 15278021236972429210564613)
                    ·
                      refine ⟨2864628981932330476980865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15278021236972429210564613 2864628981932330476980865)
                      ·
                        rfl

theorem cell23_5578845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_5578845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578845 prefixEnd_5578845 := by exact prefixLift 5578845
  have htrace : WordTrace (prefixWord ++ tailWord_5578845) baseStart_5578845 baseEnd_5578845 := by
    simpa [prefixWord, tailWord_5578845, baseEnd_5578845] using wordTrace_append hprefix tailTrace_5578845
  have hstable : (prefixWord ++ tailWord_5578845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578845).length < 2 ^ (prefixWord ++ tailWord_5578845).sum := by decide
  have hdescent : baseEnd_5578845 < baseStart_5578845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578848 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 3]
def baseStart_5578848 : Nat := 118140960795 + 5578848 * 2 ^ 59
def prefixEnd_5578848 : Nat := 4983230072969 + 3 ^ 40 * 5578848 * 2
def baseEnd_5578848 : Nat := 2864630522374293965243351

theorem tailTrace_5578848 : CollatzResearch.WordTrace tailWord_5578848 prefixEnd_5578848 2864630522374293965243351 := by
  unfold tailWord_5578848
  simp only [CollatzResearch.WordTrace]
  refine ⟨101738651446396981113956599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135651535261862641485275465 101738651446396981113956599)
  ·
    refine ⟨152607977169595471670934899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101738651446396981113956599 152607977169595471670934899)
    ·
      refine ⟨228911965754393207506402349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152607977169595471670934899 228911965754393207506402349)
      ·
        refine ⟨85841987157897452814900881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228911965754393207506402349 85841987157897452814900881)
        ·
          refine ⟨64381490368423089611175661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85841987157897452814900881 64381490368423089611175661)
          ·
            refine ⟨24143058888158658604190873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64381490368423089611175661 24143058888158658604190873)
            ·
              refine ⟨18107294166118993953143155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24143058888158658604190873 18107294166118993953143155)
              ·
                refine ⟨27160941249178490929714733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18107294166118993953143155 27160941249178490929714733)
                ·
                  refine ⟨10185352968441934098643025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27160941249178490929714733 10185352968441934098643025)
                  ·
                    refine ⟨7639014726331450573982269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10185352968441934098643025 7639014726331450573982269)
                    ·
                      refine ⟨2864630522374293965243351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7639014726331450573982269 2864630522374293965243351)
                      ·
                        rfl

theorem cell23_5578848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_5578848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578848 prefixEnd_5578848 := by exact prefixLift 5578848
  have htrace : WordTrace (prefixWord ++ tailWord_5578848) baseStart_5578848 baseEnd_5578848 := by
    simpa [prefixWord, tailWord_5578848, baseEnd_5578848] using wordTrace_append hprefix tailTrace_5578848
  have hstable : (prefixWord ++ tailWord_5578848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578848).length < 2 ^ (prefixWord ++ tailWord_5578848).sum := by decide
  have hdescent : baseEnd_5578848 < baseStart_5578848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578946 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_5578946 : Nat := 118140960795 + 5578946 * 2 ^ 59
def prefixEnd_5578946 : Nat := 4983230072969 + 3 ^ 40 * 5578946 * 2
def baseEnd_5578946 : Nat := 2864680843478434581817901

theorem tailTrace_5578946 : CollatzResearch.WordTrace tailWord_5578946 prefixEnd_5578946 2864680843478434581817901 := by
  unfold tailWord_5578946
  simp only [CollatzResearch.WordTrace]
  refine ⟨50870219311609731241245173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135653918164292616643320461 50870219311609731241245173)
  ·
    refine ⟨4769083060463412303866735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50870219311609731241245173 4769083060463412303866735)
    ·
      refine ⟨7153624590695118455800103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4769083060463412303866735 7153624590695118455800103)
      ·
        refine ⟨10730436886042677683700155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7153624590695118455800103 10730436886042677683700155)
        ·
          refine ⟨16095655329064016525550233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10730436886042677683700155 16095655329064016525550233)
          ·
            refine ⟨12071741496798012394162675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16095655329064016525550233 12071741496798012394162675)
            ·
              refine ⟨18107612245197018591244013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12071741496798012394162675 18107612245197018591244013)
              ·
                refine ⟨6790354591948881971716505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18107612245197018591244013 6790354591948881971716505)
                ·
                  refine ⟨5092765943961661478787379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6790354591948881971716505 5092765943961661478787379)
                  ·
                    refine ⟨7639148915942492218181069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5092765943961661478787379 7639148915942492218181069)
                    ·
                      refine ⟨2864680843478434581817901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7639148915942492218181069 2864680843478434581817901)
                      ·
                        rfl

theorem cell23_5578946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_5578946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578946 prefixEnd_5578946 := by exact prefixLift 5578946
  have htrace : WordTrace (prefixWord ++ tailWord_5578946) baseStart_5578946 baseEnd_5578946 := by
    simpa [prefixWord, tailWord_5578946, baseEnd_5578946] using wordTrace_append hprefix tailTrace_5578946
  have hstable : (prefixWord ++ tailWord_5578946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578946).length < 2 ^ (prefixWord ++ tailWord_5578946).sum := by decide
  have hdescent : baseEnd_5578946 < baseStart_5578946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578956 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5578956 : Nat := 118140960795 + 5578956 * 2 ^ 59
def prefixEnd_5578956 : Nat := 4983230072969 + 3 ^ 40 * 5578956 * 2
def baseEnd_5578956 : Nat := 2864685978284979542692855

theorem tailTrace_5578956 : CollatzResearch.WordTrace tailWord_5578956 prefixEnd_5578956 2864685978284979542692855 := by
  unfold tailWord_5578956
  simp only [CollatzResearch.WordTrace]
  refine ⟨101740620988201348336422361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135654161317601797781896481 101740620988201348336422361)
  ·
    refine ⟨76305465741151011252316771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101740620988201348336422361 76305465741151011252316771)
    ·
      refine ⟨114458198611726516878475157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76305465741151011252316771 114458198611726516878475157)
      ·
        refine ⟨5365228059924680478678523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114458198611726516878475157 5365228059924680478678523)
        ·
          refine ⟨8047842089887020718017785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365228059924680478678523 8047842089887020718017785)
          ·
            refine ⟨6035881567415265538513339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8047842089887020718017785 6035881567415265538513339)
            ·
              refine ⟨9053822351122898307770009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6035881567415265538513339 9053822351122898307770009)
              ·
                refine ⟨6790366763342173730827507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9053822351122898307770009 6790366763342173730827507)
                ·
                  refine ⟨10185550145013260596241261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6790366763342173730827507 10185550145013260596241261)
                  ·
                    refine ⟨3819581304379972723590473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10185550145013260596241261 3819581304379972723590473)
                    ·
                      refine ⟨2864685978284979542692855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3819581304379972723590473 2864685978284979542692855)
                      ·
                        rfl

theorem cell23_5578956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5578956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578956 prefixEnd_5578956 := by exact prefixLift 5578956
  have htrace : WordTrace (prefixWord ++ tailWord_5578956) baseStart_5578956 baseEnd_5578956 := by
    simpa [prefixWord, tailWord_5578956, baseEnd_5578956] using wordTrace_append hprefix tailTrace_5578956
  have hstable : (prefixWord ++ tailWord_5578956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578956).length < 2 ^ (prefixWord ++ tailWord_5578956).sum := by decide
  have hdescent : baseEnd_5578956 < baseStart_5578956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5578988 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_5578988 : Nat := 118140960795 + 5578988 * 2 ^ 59
def prefixEnd_5578988 : Nat := 4983230072969 + 3 ^ 40 * 5578988 * 2
def baseEnd_5578988 : Nat := 954900803221974472497569

theorem tailTrace_5578988 : CollatzResearch.WordTrace tailWord_5578988 prefixEnd_5578988 954900803221974472497569 := by
  unfold tailWord_5578988
  simp only [CollatzResearch.WordTrace]
  refine ⟨101741204556143383069004809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135654939408191177425339745 101741204556143383069004809)
  ·
    refine ⟨76305903417107537301753607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101741204556143383069004809 76305903417107537301753607)
    ·
      refine ⟨114458855125661305952630411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76305903417107537301753607 114458855125661305952630411)
      ·
        refine ⟨171688282688491958928945617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114458855125661305952630411 171688282688491958928945617)
        ·
          refine ⟨128766212016368969196709213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171688282688491958928945617 128766212016368969196709213)
          ·
            refine ⟨48287329506138363448765955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128766212016368969196709213 48287329506138363448765955)
            ·
              refine ⟨72430994259207545173148933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48287329506138363448765955 72430994259207545173148933)
              ·
                refine ⟨13580811423601414719965425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72430994259207545173148933 13580811423601414719965425)
                ·
                  refine ⟨10185608567701061039974069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13580811423601414719965425 10185608567701061039974069)
                  ·
                    refine ⟨954900803221974472497569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10185608567701061039974069 954900803221974472497569)
                    ·
                      rfl

theorem cell23_5578988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_5578988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5578988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5578988 prefixEnd_5578988 := by exact prefixLift 5578988
  have htrace : WordTrace (prefixWord ++ tailWord_5578988) baseStart_5578988 baseEnd_5578988 := by
    simpa [prefixWord, tailWord_5578988, baseEnd_5578988] using wordTrace_append hprefix tailTrace_5578988
  have hstable : (prefixWord ++ tailWord_5578988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5578988).length < 2 ^ (prefixWord ++ tailWord_5578988).sum := by decide
  have hdescent : baseEnd_5578988 < baseStart_5578988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5578988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579008 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 4]
def baseStart_5579008 : Nat := 118140960795 + 5579008 * 2 ^ 59
def prefixEnd_5579008 : Nat := 4983230072969 + 3 ^ 40 * 5579008 * 2
def baseEnd_5579008 : Nat := 2864712679279013339242615

theorem tailTrace_5579008 : CollatzResearch.WordTrace tailWord_5579008 prefixEnd_5579008 2864712679279013339242615 := by
  unfold tailWord_5579008
  simp only [CollatzResearch.WordTrace]
  refine ⟨101741569286107154776868839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135655425714809539702491785 101741569286107154776868839)
  ·
    refine ⟨152612353929160732165303259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101741569286107154776868839 152612353929160732165303259)
    ·
      refine ⟨228918530893741098247954889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152612353929160732165303259 228918530893741098247954889)
      ·
        refine ⟨171688898170305823685966167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228918530893741098247954889 171688898170305823685966167)
        ·
          refine ⟨257533347255458735528949251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171688898170305823685966167 257533347255458735528949251)
          ·
            refine ⟨386300020883188103293423877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257533347255458735528949251 386300020883188103293423877)
            ·
              refine ⟨72431253915597769367516977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 386300020883188103293423877 72431253915597769367516977)
              ·
                refine ⟨54323440436698327025637733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72431253915597769367516977 54323440436698327025637733)
                ·
                  refine ⟨10185645081880936317307075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54323440436698327025637733 10185645081880936317307075)
                  ·
                    refine ⟨15278467622821404475960613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10185645081880936317307075 15278467622821404475960613)
                    ·
                      refine ⟨2864712679279013339242615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15278467622821404475960613 2864712679279013339242615)
                      ·
                        rfl

theorem cell23_5579008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_5579008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579008 prefixEnd_5579008 := by exact prefixLift 5579008
  have htrace : WordTrace (prefixWord ++ tailWord_5579008) baseStart_5579008 baseEnd_5579008 := by
    simpa [prefixWord, tailWord_5579008, baseEnd_5579008] using wordTrace_append hprefix tailTrace_5579008
  have hstable : (prefixWord ++ tailWord_5579008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579008).length < 2 ^ (prefixWord ++ tailWord_5579008).sum := by decide
  have hdescent : baseEnd_5579008 < baseStart_5579008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579025 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 4]
def baseStart_5579025 : Nat := 118140960795 + 5579025 * 2 ^ 59
def prefixEnd_5579025 : Nat := 4983230072969 + 3 ^ 40 * 5579025 * 2
def baseEnd_5579025 : Nat := 2864721408450139772730037

theorem tailTrace_5579025 : CollatzResearch.WordTrace tailWord_5579025 prefixEnd_5579025 2864721408450139772730037 := by
  unfold tailWord_5579025
  simp only [CollatzResearch.WordTrace]
  refine ⟨203483758613152721457106529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135655839075435147638071019 203483758613152721457106529)
  ·
    refine ⟨152612818959864541092829897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203483758613152721457106529 152612818959864541092829897)
    ·
      refine ⟨114459614219898405819622423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152612818959864541092829897 114459614219898405819622423)
      ·
        refine ⟨171689421329847608729433635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114459614219898405819622423 171689421329847608729433635)
        ·
          refine ⟨257534131994771413094150453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171689421329847608729433635 257534131994771413094150453)
          ·
            refine ⟨24143824874509819977576605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 257534131994771413094150453 24143824874509819977576605)
            ·
              refine ⟨9053934327941182491591227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24143824874509819977576605 9053934327941182491591227)
              ·
                refine ⟨13580901491911773737386841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9053934327941182491591227 13580901491911773737386841)
                ·
                  refine ⟨10185676118933830303040131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13580901491911773737386841 10185676118933830303040131)
                  ·
                    refine ⟨15278514178400745454560197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10185676118933830303040131 15278514178400745454560197)
                    ·
                      refine ⟨2864721408450139772730037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15278514178400745454560197 2864721408450139772730037)
                      ·
                        rfl

theorem cell23_5579025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_5579025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579025 prefixEnd_5579025 := by exact prefixLift 5579025
  have htrace : WordTrace (prefixWord ++ tailWord_5579025) baseStart_5579025 baseEnd_5579025 := by
    simpa [prefixWord, tailWord_5579025, baseEnd_5579025] using wordTrace_append hprefix tailTrace_5579025
  have hstable : (prefixWord ++ tailWord_5579025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579025).length < 2 ^ (prefixWord ++ tailWord_5579025).sum := by decide
  have hdescent : baseEnd_5579025 < baseStart_5579025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579042 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_5579042 : Nat := 118140960795 + 5579042 * 2 ^ 59
def prefixEnd_5579042 : Nat := 4983230072969 + 3 ^ 40 * 5579042 * 2
def baseEnd_5579042 : Nat := 2864730137621266206217459

theorem tailTrace_5579042 : CollatzResearch.WordTrace tailWord_5579042 prefixEnd_5579042 2864730137621266206217459 := by
  unfold tailWord_5579042
  simp only [CollatzResearch.WordTrace]
  refine ⟨50871094663522783340118845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135656252436060755573650253 50871094663522783340118845)
  ·
    refine ⟨19076660498821043752544567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50871094663522783340118845 19076660498821043752544567)
    ·
      refine ⟨28614990748231565628816851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19076660498821043752544567 28614990748231565628816851)
      ·
        refine ⟨42922486122347348443225277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28614990748231565628816851 42922486122347348443225277)
        ·
          refine ⟨16095932295880255666209479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42922486122347348443225277 16095932295880255666209479)
          ·
            refine ⟨24143898443820383499314219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16095932295880255666209479 24143898443820383499314219)
            ·
              refine ⟨36215847665730575248971329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24143898443820383499314219 36215847665730575248971329)
              ·
                refine ⟨27161885749297931436728497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36215847665730575248971329 27161885749297931436728497)
                ·
                  refine ⟨20371414311973448577546373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27161885749297931436728497 20371414311973448577546373)
                  ·
                    refine ⟨3819640183495021608289945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20371414311973448577546373 3819640183495021608289945)
                    ·
                      refine ⟨2864730137621266206217459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3819640183495021608289945 2864730137621266206217459)
                      ·
                        rfl

theorem cell23_5579042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_5579042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579042 prefixEnd_5579042 := by exact prefixLift 5579042
  have htrace : WordTrace (prefixWord ++ tailWord_5579042) baseStart_5579042 baseEnd_5579042 := by
    simpa [prefixWord, tailWord_5579042, baseEnd_5579042] using wordTrace_append hprefix tailTrace_5579042
  have hstable : (prefixWord ++ tailWord_5579042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579042).length < 2 ^ (prefixWord ++ tailWord_5579042).sum := by decide
  have hdescent : baseEnd_5579042 < baseStart_5579042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579052 : List Nat := [2, 2, 1, 1, 1, 3, 4, 4, 1, 4]
def baseStart_5579052 : Nat := 118140960795 + 5579052 * 2 ^ 59
def prefixEnd_5579052 : Nat := 4983230072969 + 3 ^ 40 * 5579052 * 2
def baseEnd_5579052 : Nat := 954911757475937055697471

theorem tailTrace_5579052 : CollatzResearch.WordTrace tailWord_5579052 prefixEnd_5579052 954911757475937055697471 := by
  unfold tailWord_5579052
  simp only [CollatzResearch.WordTrace]
  refine ⟨101742371692027452534169705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135656495589369936712226273 101742371692027452534169705)
  ·
    refine ⟨76306778769020589400627279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101742371692027452534169705 76306778769020589400627279)
    ·
      refine ⟨114460168153530884100940919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76306778769020589400627279 114460168153530884100940919)
      ·
        refine ⟨171690252230296326151411379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114460168153530884100940919 171690252230296326151411379)
        ·
          refine ⟨257535378345444489227117069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171690252230296326151411379 257535378345444489227117069)
          ·
            refine ⟨96575766879541683460168901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257535378345444489227117069 96575766879541683460168901)
            ·
              refine ⟨18107956289914065648781669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96575766879541683460168901 18107956289914065648781669)
              ·
                refine ⟨3395241804358887309146563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18107956289914065648781669 3395241804358887309146563)
                ·
                  refine ⟨5092862706538330963719845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3395241804358887309146563 5092862706538330963719845)
                  ·
                    refine ⟨954911757475937055697471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5092862706538330963719845 954911757475937055697471)
                    ·
                      rfl

theorem cell23_5579052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_5579052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579052 prefixEnd_5579052 := by exact prefixLift 5579052
  have htrace : WordTrace (prefixWord ++ tailWord_5579052) baseStart_5579052 baseEnd_5579052 := by
    simpa [prefixWord, tailWord_5579052, baseEnd_5579052] using wordTrace_append hprefix tailTrace_5579052
  have hstable : (prefixWord ++ tailWord_5579052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579052).length < 2 ^ (prefixWord ++ tailWord_5579052).sum := by decide
  have hdescent : baseEnd_5579052 < baseStart_5579052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579068 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_5579068 : Nat := 118140960795 + 5579068 * 2 ^ 59
def prefixEnd_5579068 : Nat := 4983230072969 + 3 ^ 40 * 5579068 * 2
def baseEnd_5579068 : Nat := 2864743488118283104492339

theorem tailTrace_5579068 : CollatzResearch.WordTrace tailWord_5579068 prefixEnd_5579068 2864743488118283104492339 := by
  unfold tailWord_5579068
  simp only [CollatzResearch.WordTrace]
  refine ⟨101742663475998469900460929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135656884634664626533947905 101742663475998469900460929)
  ·
    refine ⟨76306997606998852425345697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101742663475998469900460929 76306997606998852425345697)
    ·
      refine ⟨57230248205249139319009273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76306997606998852425345697 57230248205249139319009273)
      ·
        refine ⟨42922686153936854489256955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57230248205249139319009273 42922686153936854489256955)
        ·
          refine ⟨64384029230905281733885433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42922686153936854489256955 64384029230905281733885433)
          ·
            refine ⟨48288021923178961300414075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64384029230905281733885433 48288021923178961300414075)
            ·
              refine ⟨72432032884768441950621113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48288021923178961300414075 72432032884768441950621113)
              ·
                refine ⟨54324024663576331462965835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72432032884768441950621113 54324024663576331462965835)
                ·
                  refine ⟨81486036995364497194448753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54324024663576331462965835 81486036995364497194448753)
                  ·
                    refine ⟨61114527746523372895836565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81486036995364497194448753 61114527746523372895836565)
                    ·
                      refine ⟨2864743488118283104492339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61114527746523372895836565 2864743488118283104492339)
                      ·
                        rfl

theorem cell23_5579068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_5579068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579068 prefixEnd_5579068 := by exact prefixLift 5579068
  have htrace : WordTrace (prefixWord ++ tailWord_5579068) baseStart_5579068 baseEnd_5579068 := by
    simpa [prefixWord, tailWord_5579068, baseEnd_5579068] using wordTrace_append hprefix tailTrace_5579068
  have hstable : (prefixWord ++ tailWord_5579068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579068).length < 2 ^ (prefixWord ++ tailWord_5579068).sum := by decide
  have hdescent : baseEnd_5579068 < baseStart_5579068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579095 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 1, 5]
def baseStart_5579095 : Nat := 118140960795 + 5579095 * 2 ^ 59
def prefixEnd_5579095 : Nat := 4983230072969 + 3 ^ 40 * 5579095 * 2
def baseEnd_5579095 : Nat := 954919117365318166284905

theorem tailTrace_5579095 : CollatzResearch.WordTrace tailWord_5579095 prefixEnd_5579095 954919117365318166284905 := by
  unfold tailWord_5579095
  simp only [CollatzResearch.WordTrace]
  refine ⟨203486311722899123412154739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135657541148599415608103159 203486311722899123412154739)
  ·
    refine ⟨305229467584348685118232109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203486311722899123412154739 305229467584348685118232109)
    ·
      refine ⟨114461050344130756919337041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305229467584348685118232109 114461050344130756919337041)
      ·
        refine ⟨85845787758098067689502781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114461050344130756919337041 85845787758098067689502781)
        ·
          refine ⟨32192170409286775383563543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85845787758098067689502781 32192170409286775383563543)
          ·
            refine ⟨48288255613930163075345315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32192170409286775383563543 48288255613930163075345315)
            ·
              refine ⟨72432383420895244613017973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48288255613930163075345315 72432383420895244613017973)
              ·
                refine ⟨6790535945708929182470435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72432383420895244613017973 6790535945708929182470435)
                ·
                  refine ⟨10185803918563393773705653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6790535945708929182470435 10185803918563393773705653)
                  ·
                    refine ⟨954919117365318166284905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10185803918563393773705653 954919117365318166284905)
                    ·
                      rfl

theorem cell23_5579095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_5579095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579095 prefixEnd_5579095 := by exact prefixLift 5579095
  have htrace : WordTrace (prefixWord ++ tailWord_5579095) baseStart_5579095 baseEnd_5579095 := by
    simpa [prefixWord, tailWord_5579095, baseEnd_5579095] using wordTrace_append hprefix tailTrace_5579095
  have hstable : (prefixWord ++ tailWord_5579095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579095).length < 2 ^ (prefixWord ++ tailWord_5579095).sum := by decide
  have hdescent : baseEnd_5579095 < baseStart_5579095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579109 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 3, 1, 3]
def baseStart_5579109 : Nat := 118140960795 + 5579109 * 2 ^ 59
def prefixEnd_5579109 : Nat := 4983230072969 + 3 ^ 40 * 5579109 * 2
def baseEnd_5579109 : Nat := 2864764540825117444079651

theorem tailTrace_5579109 : CollatzResearch.WordTrace tailWord_5579109 prefixEnd_5579109 2864764540825117444079651 := by
  unfold tailWord_5579109
  simp only [CollatzResearch.WordTrace]
  refine ⟨203486822344848403803164381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135657881563232269202109587 203486822344848403803164381)
  ·
    refine ⟨76307558379318151426186643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203486822344848403803164381 76307558379318151426186643)
    ·
      refine ⟨114461337568977227139279965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76307558379318151426186643 114461337568977227139279965)
      ·
        refine ⟨42923001588366460177229987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114461337568977227139279965 42923001588366460177229987)
        ·
          refine ⟨64384502382549690265844981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42923001588366460177229987 64384502382549690265844981)
          ·
            refine ⟨6036047098364033462422967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64384502382549690265844981 6036047098364033462422967)
            ·
              refine ⟨9054070647546050193634451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6036047098364033462422967 9054070647546050193634451)
              ·
                refine ⟨13581105971319075290451677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9054070647546050193634451 13581105971319075290451677)
                ·
                  refine ⟨5092914739244653233919379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13581105971319075290451677 5092914739244653233919379)
                  ·
                    refine ⟨7639372108866979850879069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5092914739244653233919379 7639372108866979850879069)
                    ·
                      refine ⟨2864764540825117444079651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7639372108866979850879069 2864764540825117444079651)
                      ·
                        rfl

theorem cell23_5579109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_5579109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579109 prefixEnd_5579109 := by exact prefixLift 5579109
  have htrace : WordTrace (prefixWord ++ tailWord_5579109) baseStart_5579109 baseEnd_5579109 := by
    simpa [prefixWord, tailWord_5579109, baseEnd_5579109] using wordTrace_append hprefix tailTrace_5579109
  have hstable : (prefixWord ++ tailWord_5579109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579109).length < 2 ^ (prefixWord ++ tailWord_5579109).sum := by decide
  have hdescent : baseEnd_5579109 < baseStart_5579109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579135 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 3]
def baseStart_5579135 : Nat := 118140960795 + 5579135 * 2 ^ 59
def prefixEnd_5579135 : Nat := 4983230072969 + 3 ^ 40 * 5579135 * 2
def baseEnd_5579135 : Nat := 2864777891322134342354531

theorem tailTrace_5579135 : CollatzResearch.WordTrace tailWord_5579135 prefixEnd_5579135 2864777891322134342354531 := by
  unfold tailWord_5579135
  simp only [CollatzResearch.WordTrace]
  refine ⟨203487770642754210243610859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135658513761836140162407239 203487770642754210243610859)
  ·
    refine ⟨305231655964131315365416289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203487770642754210243610859 305231655964131315365416289)
    ·
      refine ⟨228923741973098486524062217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305231655964131315365416289 228923741973098486524062217)
      ·
        refine ⟨171692806479823864893046663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228923741973098486524062217 171692806479823864893046663)
        ·
          refine ⟨257539209719735797339569995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171692806479823864893046663 257539209719735797339569995)
          ·
            refine ⟨386308814579603696009354993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257539209719735797339569995 386308814579603696009354993)
            ·
              refine ⟨289731610934702772007016245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386308814579603696009354993 289731610934702772007016245)
              ·
                refine ⟨27162338525128384875657773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 289731610934702772007016245 27162338525128384875657773)
                ·
                  refine ⟨10185876946923144328371665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27162338525128384875657773 10185876946923144328371665)
                  ·
                    refine ⟨7639407710192358246278749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10185876946923144328371665 7639407710192358246278749)
                    ·
                      refine ⟨2864777891322134342354531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7639407710192358246278749 2864777891322134342354531)
                      ·
                        rfl

theorem cell23_5579135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_5579135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579135 prefixEnd_5579135 := by exact prefixLift 5579135
  have htrace : WordTrace (prefixWord ++ tailWord_5579135) baseStart_5579135 baseEnd_5579135 := by
    simpa [prefixWord, tailWord_5579135, baseEnd_5579135] using wordTrace_append hprefix tailTrace_5579135
  have hstable : (prefixWord ++ tailWord_5579135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579135).length < 2 ^ (prefixWord ++ tailWord_5579135).sum := by decide
  have hdescent : baseEnd_5579135 < baseStart_5579135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579145 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 4]
def baseStart_5579145 : Nat := 118140960795 + 5579145 * 2 ^ 59
def prefixEnd_5579145 : Nat := 4983230072969 + 3 ^ 40 * 5579145 * 2
def baseEnd_5579145 : Nat := 2864783026128679303229485

theorem tailTrace_5579145 : CollatzResearch.WordTrace tailWord_5579145 prefixEnd_5579145 2864783026128679303229485 := by
  unfold tailWord_5579145
  simp only [CollatzResearch.WordTrace]
  refine ⟨203488135372717981951474889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135658756915145321300983259 203488135372717981951474889)
  ·
    refine ⟨152616101529538486463606167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203488135372717981951474889 152616101529538486463606167)
    ·
      refine ⟨228924152294307729695409251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152616101529538486463606167 228924152294307729695409251)
      ·
        refine ⟨343386228441461594543113877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228924152294307729695409251 343386228441461594543113877)
        ·
          refine ⟨16096229458193512244208463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 343386228441461594543113877 16096229458193512244208463)
          ·
            refine ⟨24144344187290268366312695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16096229458193512244208463 24144344187290268366312695)
            ·
              refine ⟨36216516280935402549469043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24144344187290268366312695 36216516280935402549469043)
              ·
                refine ⟨54324774421403103824203565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36216516280935402549469043 54324774421403103824203565)
                ·
                  refine ⟨20371790408026163934076337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54324774421403103824203565 20371790408026163934076337)
                  ·
                    refine ⟨15278842806019622950557253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20371790408026163934076337 15278842806019622950557253)
                    ·
                      refine ⟨2864783026128679303229485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15278842806019622950557253 2864783026128679303229485)
                      ·
                        rfl

theorem cell23_5579145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_5579145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579145 prefixEnd_5579145 := by exact prefixLift 5579145
  have htrace : WordTrace (prefixWord ++ tailWord_5579145) baseStart_5579145 baseEnd_5579145 := by
    simpa [prefixWord, tailWord_5579145, baseEnd_5579145] using wordTrace_append hprefix tailTrace_5579145
  have hstable : (prefixWord ++ tailWord_5579145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579145).length < 2 ^ (prefixWord ++ tailWord_5579145).sum := by decide
  have hdescent : baseEnd_5579145 < baseStart_5579145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579146 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 1, 5]
def baseStart_5579146 : Nat := 118140960795 + 5579146 * 2 ^ 59
def prefixEnd_5579146 : Nat := 4983230072969 + 3 ^ 40 * 5579146 * 2
def baseEnd_5579146 : Nat := 954927846536444599772327

theorem tailTrace_5579146 : CollatzResearch.WordTrace tailWord_5579146 prefixEnd_5579146 954927846536444599772327 := by
  unfold tailWord_5579146
  simp only [CollatzResearch.WordTrace]
  refine ⟨50872042961428589780565323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135658781230476239414840861 50872042961428589780565323)
  ·
    refine ⟨76308064442142884670847985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50872042961428589780565323 76308064442142884670847985)
    ·
      refine ⟨57231048331607163503135989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76308064442142884670847985 57231048331607163503135989)
      ·
        refine ⟨5365410781088171578418999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57231048331607163503135989 5365410781088171578418999)
        ·
          refine ⟨8048116171632257367628499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5365410781088171578418999 8048116171632257367628499)
          ·
            refine ⟨12072174257448386051442749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8048116171632257367628499 12072174257448386051442749)
            ·
              refine ⟨4527065346543144769291031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12072174257448386051442749 4527065346543144769291031)
              ·
                refine ⟨6790598019814717153936547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4527065346543144769291031 6790598019814717153936547)
                ·
                  refine ⟨10185897029722075730904821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6790598019814717153936547 10185897029722075730904821)
                  ·
                    refine ⟨954927846536444599772327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10185897029722075730904821 954927846536444599772327)
                    ·
                      rfl

theorem cell23_5579146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_5579146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579146 prefixEnd_5579146 := by exact prefixLift 5579146
  have htrace : WordTrace (prefixWord ++ tailWord_5579146) baseStart_5579146 baseEnd_5579146 := by
    simpa [prefixWord, tailWord_5579146, baseEnd_5579146] using wordTrace_append hprefix tailTrace_5579146
  have hstable : (prefixWord ++ tailWord_5579146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579146).length < 2 ^ (prefixWord ++ tailWord_5579146).sum := by decide
  have hdescent : baseEnd_5579146 < baseStart_5579146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579312 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 4]
def baseStart_5579312 : Nat := 118140960795 + 5579312 * 2 ^ 59
def prefixEnd_5579312 : Nat := 4983230072969 + 3 ^ 40 * 5579312 * 2
def baseEnd_5579312 : Nat := 2864868777397980149841217

theorem tailTrace_5579312 : CollatzResearch.WordTrace tailWord_5579312 prefixEnd_5579312 2864868777397980149841217 := by
  unfold tailWord_5579312
  simp only [CollatzResearch.WordTrace]
  refine ⟨101747113181556484736402095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135662817575408646315202793 101747113181556484736402095)
  ·
    refine ⟨152620669772334727104603143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101747113181556484736402095 152620669772334727104603143)
    ·
      refine ⟨228931004658502090656904715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152620669772334727104603143 228931004658502090656904715)
      ·
        refine ⟨343396506987753135985357073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228931004658502090656904715 343396506987753135985357073)
        ·
          refine ⟨257547380240814851989017805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343396506987753135985357073 257547380240814851989017805)
          ·
            refine ⟨96580267590305569495881677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257547380240814851989017805 96580267590305569495881677)
            ·
              refine ⟨36217600346364588560955629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96580267590305569495881677 36217600346364588560955629)
              ·
                refine ⟨13581600129886720710358361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36217600346364588560955629 13581600129886720710358361)
                ·
                  refine ⟨10186200097415040532768771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13581600129886720710358361 10186200097415040532768771)
                  ·
                    refine ⟨15279300146122560799153157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10186200097415040532768771 15279300146122560799153157)
                    ·
                      refine ⟨2864868777397980149841217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15279300146122560799153157 2864868777397980149841217)
                      ·
                        rfl

theorem cell23_5579312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_5579312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579312 prefixEnd_5579312 := by exact prefixLift 5579312
  have htrace : WordTrace (prefixWord ++ tailWord_5579312) baseStart_5579312 baseEnd_5579312 := by
    simpa [prefixWord, tailWord_5579312, baseEnd_5579312] using wordTrace_append hprefix tailTrace_5579312
  have hstable : (prefixWord ++ tailWord_5579312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579312).length < 2 ^ (prefixWord ++ tailWord_5579312).sum := by decide
  have hdescent : baseEnd_5579312 < baseStart_5579312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579329 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_5579329 : Nat := 118140960795 + 5579329 * 2 ^ 59
def prefixEnd_5579329 : Nat := 4983230072969 + 3 ^ 40 * 5579329 * 2
def baseEnd_5579329 : Nat := 2864877506569106583328639

theorem tailTrace_5579329 : CollatzResearch.WordTrace tailWord_5579329 prefixEnd_5579329 2864877506569106583328639 := by
  unfold tailWord_5579329
  simp only [CollatzResearch.WordTrace]
  refine ⟨203494846404051381376173041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135663230936034254250782027 203494846404051381376173041)
  ·
    refine ⟨152621134803038536032129781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203494846404051381376173041 152621134803038536032129781)
    ·
      refine ⟨14308231387784862753012167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152621134803038536032129781 14308231387784862753012167)
      ·
        refine ⟨21462347081677294129518251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14308231387784862753012167 21462347081677294129518251)
        ·
          refine ⟨32193520622515941194277377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21462347081677294129518251 32193520622515941194277377)
          ·
            refine ⟨24145140466886955895708033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32193520622515941194277377 24145140466886955895708033)
            ·
              refine ⟨18108855350165216921781025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24145140466886955895708033 18108855350165216921781025)
              ·
                refine ⟨13581641512623912691335769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18108855350165216921781025 13581641512623912691335769)
                ·
                  refine ⟨10186231134467934518501827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13581641512623912691335769 10186231134467934518501827)
                  ·
                    refine ⟨15279346701701901777752741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10186231134467934518501827 15279346701701901777752741)
                    ·
                      refine ⟨2864877506569106583328639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15279346701701901777752741 2864877506569106583328639)
                      ·
                        rfl

theorem cell23_5579329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_5579329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579329 prefixEnd_5579329 := by exact prefixLift 5579329
  have htrace : WordTrace (prefixWord ++ tailWord_5579329) baseStart_5579329 baseEnd_5579329 := by
    simpa [prefixWord, tailWord_5579329, baseEnd_5579329] using wordTrace_append hprefix tailTrace_5579329
  have hstable : (prefixWord ++ tailWord_5579329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579329).length < 2 ^ (prefixWord ++ tailWord_5579329).sum := by decide
  have hdescent : baseEnd_5579329 < baseStart_5579329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579352 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 6]
def baseStart_5579352 : Nat := 118140960795 + 5579352 * 2 ^ 59
def prefixEnd_5579352 : Nat := 4983230072969 + 3 ^ 40 * 5579352 * 2
def baseEnd_5579352 : Nat := 318321035180462221482337

theorem tailTrace_5579352 : CollatzResearch.WordTrace tailWord_5579352 prefixEnd_5579352 318321035180462221482337 := by
  unfold tailWord_5579352
  simp only [CollatzResearch.WordTrace]
  refine ⟨101747842641484028152130155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135663790188645370869506873 101747842641484028152130155)
  ·
    refine ⟨152621763962226042228195233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101747842641484028152130155 152621763962226042228195233)
    ·
      refine ⟨114466322971669531671146425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152621763962226042228195233 114466322971669531671146425)
      ·
        refine ⟨85849742228752148753359819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114466322971669531671146425 85849742228752148753359819)
        ·
          refine ⟨128774613343128223130039729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85849742228752148753359819 128774613343128223130039729)
          ·
            refine ⟨96580960007346167347529797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128774613343128223130039729 96580960007346167347529797)
            ·
              refine ⟨18108930001377406377661837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96580960007346167347529797 18108930001377406377661837)
              ·
                refine ⟨6790848750516527391623189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18108930001377406377661837 6790848750516527391623189)
                ·
                  refine ⟨318321035180462221482337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6790848750516527391623189 318321035180462221482337)
                  ·
                    rfl

theorem cell23_5579352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 6].length) (baseStart_5579352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579352 prefixEnd_5579352 := by exact prefixLift 5579352
  have htrace : WordTrace (prefixWord ++ tailWord_5579352) baseStart_5579352 baseEnd_5579352 := by
    simpa [prefixWord, tailWord_5579352, baseEnd_5579352] using wordTrace_append hprefix tailTrace_5579352
  have hstable : (prefixWord ++ tailWord_5579352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579352).length < 2 ^ (prefixWord ++ tailWord_5579352).sum := by decide
  have hdescent : baseEnd_5579352 < baseStart_5579352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579356 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 3, 4]
def baseStart_5579356 : Nat := 118140960795 + 5579356 * 2 ^ 59
def prefixEnd_5579356 : Nat := 4983230072969 + 3 ^ 40 * 5579356 * 2
def baseEnd_5579356 : Nat := 954963790182259325897005

theorem tailTrace_5579356 : CollatzResearch.WordTrace tailWord_5579356 prefixEnd_5579356 954963790182259325897005 := by
  unfold tailWord_5579356
  simp only [CollatzResearch.WordTrace]
  refine ⟨101747915587476782493702961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135663887449969043324937281 101747915587476782493702961)
  ·
    refine ⟨76310936690607586870277221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101747915587476782493702961 76310936690607586870277221)
    ·
      refine ⟨14308300629488922538176979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76310936690607586870277221 14308300629488922538176979)
      ·
        refine ⟨21462450944233383807265469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14308300629488922538176979 21462450944233383807265469)
        ·
          refine ⟨8048419104087518927724551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21462450944233383807265469 8048419104087518927724551)
          ·
            refine ⟨12072628656131278391586827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8048419104087518927724551 12072628656131278391586827)
            ·
              refine ⟨18108942984196917587380241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12072628656131278391586827 18108942984196917587380241)
              ·
                refine ⟨13581707238147688190535181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18108942984196917587380241 13581707238147688190535181)
                ·
                  refine ⟨5093140214305383071450693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13581707238147688190535181 5093140214305383071450693)
                  ·
                    refine ⟨954963790182259325897005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5093140214305383071450693 954963790182259325897005)
                    ·
                      rfl

theorem cell23_5579356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_5579356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579356 prefixEnd_5579356 := by exact prefixLift 5579356
  have htrace : WordTrace (prefixWord ++ tailWord_5579356) baseStart_5579356 baseEnd_5579356 := by
    simpa [prefixWord, tailWord_5579356, baseEnd_5579356] using wordTrace_append hprefix tailTrace_5579356
  have hstable : (prefixWord ++ tailWord_5579356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579356).length < 2 ^ (prefixWord ++ tailWord_5579356).sum := by decide
  have hdescent : baseEnd_5579356 < baseStart_5579356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579373 : List Nat := [1, 5, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_5579373 : Nat := 118140960795 + 5579373 * 2 ^ 59
def prefixEnd_5579373 : Nat := 4983230072969 + 3 ^ 40 * 5579373 * 2
def baseEnd_5579373 : Nat := 954966699905968137059479

theorem tailTrace_5579373 : CollatzResearch.WordTrace tailWord_5579373 prefixEnd_5579373 954966699905968137059479 := by
  unfold tailWord_5579373
  simp only [CollatzResearch.WordTrace]
  refine ⟨203496451215891976890774773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135664300810594651260516515 203496451215891976890774773)
  ·
    refine ⟨19077792301489872833510135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203496451215891976890774773 19077792301489872833510135)
    ·
      refine ⟨28616688452234809250265203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19077792301489872833510135 28616688452234809250265203)
      ·
        refine ⟨42925032678352213875397805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28616688452234809250265203 42925032678352213875397805)
        ·
          refine ⟨16096887254382080203274177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42925032678352213875397805 16096887254382080203274177)
          ·
            refine ⟨12072665440786560152455633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16096887254382080203274177 12072665440786560152455633)
            ·
              refine ⟨9054499080589920114341725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12072665440786560152455633 9054499080589920114341725)
              ·
                refine ⟨3395437155221220042878147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9054499080589920114341725 3395437155221220042878147)
                ·
                  refine ⟨5093155732831830064317221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3395437155221220042878147 5093155732831830064317221)
                  ·
                    refine ⟨954966699905968137059479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5093155732831830064317221 954966699905968137059479)
                    ·
                      rfl

theorem cell23_5579373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_5579373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579373 prefixEnd_5579373 := by exact prefixLift 5579373
  have htrace : WordTrace (prefixWord ++ tailWord_5579373) baseStart_5579373 baseEnd_5579373 := by
    simpa [prefixWord, tailWord_5579373, baseEnd_5579373] using wordTrace_append hprefix tailTrace_5579373
  have hstable : (prefixWord ++ tailWord_5579373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579373).length < 2 ^ (prefixWord ++ tailWord_5579373).sum := by decide
  have hdescent : baseEnd_5579373 < baseStart_5579373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579396 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_5579396 : Nat := 118140960795 + 5579396 * 2 ^ 59
def prefixEnd_5579396 : Nat := 4983230072969 + 3 ^ 40 * 5579396 * 2
def baseEnd_5579396 : Nat := 2864911909772957821190831

theorem tailTrace_5579396 : CollatzResearch.WordTrace tailWord_5579396 prefixEnd_5579396 2864911909772957821190831 := by
  unfold tailWord_5579396
  simp only [CollatzResearch.WordTrace]
  refine ⟨101748645047404325909431021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135664860063205767879241361 101748645047404325909431021)
  ·
    refine ⟨38155741892776622216036633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101748645047404325909431021 38155741892776622216036633)
    ·
      refine ⟨28616806419582466662027475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38155741892776622216036633 28616806419582466662027475)
      ·
        refine ⟨42925209629373699993041213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28616806419582466662027475 42925209629373699993041213)
        ·
          refine ⟨16096953611015137497390455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42925209629373699993041213 16096953611015137497390455)
          ·
            refine ⟨24145430416522706246085683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16096953611015137497390455 24145430416522706246085683)
            ·
              refine ⟨36218145624784059369128525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24145430416522706246085683 36218145624784059369128525)
              ·
                refine ⟨13581804609294022263423197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36218145624784059369128525 13581804609294022263423197)
                ·
                  refine ⟨5093176728485258348783699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13581804609294022263423197 5093176728485258348783699)
                  ·
                    refine ⟨7639765092727887523175549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5093176728485258348783699 7639765092727887523175549)
                    ·
                      refine ⟨2864911909772957821190831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7639765092727887523175549 2864911909772957821190831)
                      ·
                        rfl

theorem cell23_5579396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_5579396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579396 prefixEnd_5579396 := by exact prefixLift 5579396
  have htrace : WordTrace (prefixWord ++ tailWord_5579396) baseStart_5579396 baseEnd_5579396 := by
    simpa [prefixWord, tailWord_5579396, baseEnd_5579396] using wordTrace_append hprefix tailTrace_5579396
  have hstable : (prefixWord ++ tailWord_5579396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579396).length < 2 ^ (prefixWord ++ tailWord_5579396).sum := by decide
  have hdescent : baseEnd_5579396 < baseStart_5579396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579439 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 5]
def baseStart_5579439 : Nat := 118140960795 + 5579439 * 2 ^ 59
def prefixEnd_5579439 : Nat := 4983230072969 + 3 ^ 40 * 5579439 * 2
def baseEnd_5579439 : Nat := 2864933989441101152953133

theorem tailTrace_5579439 : CollatzResearch.WordTrace tailWord_5579439 prefixEnd_5579439 2864933989441101152953133 := by
  unfold tailWord_5579439
  simp only [CollatzResearch.WordTrace]
  refine ⟨203498858433652870162677371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135665905622435246775118247 203498858433652870162677371)
  ·
    refine ⟨305248287650479305244016057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203498858433652870162677371 305248287650479305244016057)
    ·
      refine ⟨228936215737859478933012043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305248287650479305244016057 228936215737859478933012043)
      ·
        refine ⟨343404323606789218399518065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228936215737859478933012043 343404323606789218399518065)
        ·
          refine ⟨257553242705091913799638549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343404323606789218399518065 257553242705091913799638549)
          ·
            refine ⟨12072808251801183459358057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 257553242705091913799638549 12072808251801183459358057)
            ·
              refine ⟨9054606188850887594518543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12072808251801183459358057 9054606188850887594518543)
              ·
                refine ⟨13581909283276331391777815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9054606188850887594518543 13581909283276331391777815)
                ·
                  refine ⟨20372863924914497087666723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13581909283276331391777815 20372863924914497087666723)
                  ·
                    refine ⟨30559295887371745631500085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20372863924914497087666723 30559295887371745631500085)
                    ·
                      refine ⟨2864933989441101152953133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30559295887371745631500085 2864933989441101152953133)
                      ·
                        rfl

theorem cell23_5579439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 5].length) (baseStart_5579439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579439 prefixEnd_5579439 := by exact prefixLift 5579439
  have htrace : WordTrace (prefixWord ++ tailWord_5579439) baseStart_5579439 baseEnd_5579439 := by
    simpa [prefixWord, tailWord_5579439, baseEnd_5579439] using wordTrace_append hprefix tailTrace_5579439
  have hstable : (prefixWord ++ tailWord_5579439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579439).length < 2 ^ (prefixWord ++ tailWord_5579439).sum := by decide
  have hdescent : baseEnd_5579439 < baseStart_5579439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579453 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 3, 2, 2]
def baseStart_5579453 : Nat := 118140960795 + 5579453 * 2 ^ 59
def prefixEnd_5579453 : Nat := 4983230072969 + 3 ^ 40 * 5579453 * 2
def baseEnd_5579453 : Nat := 2864941178170264098178069

theorem tailTrace_5579453 : CollatzResearch.WordTrace tailWord_5579453 prefixEnd_5579453 2864941178170264098178069 := by
  unfold tailWord_5579453
  simp only [CollatzResearch.WordTrace]
  refine ⟨203499369055602150553687013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135666246037068100369124675 203499369055602150553687013)
  ·
    refine ⟨38156131697925403228816315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203499369055602150553687013 38156131697925403228816315)
    ·
      refine ⟨57234197546888104843224473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38156131697925403228816315 57234197546888104843224473)
      ·
        refine ⟨42925648160166078632418355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57234197546888104843224473 42925648160166078632418355)
        ·
          refine ⟨64388472240249117948627533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42925648160166078632418355 64388472240249117948627533)
          ·
            refine ⟨24145677090093419230735325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64388472240249117948627533 24145677090093419230735325)
            ·
              refine ⟨9054628908785032211525747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24145677090093419230735325 9054628908785032211525747)
              ·
                refine ⟨13581943363177548317288621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9054628908785032211525747 13581943363177548317288621)
                ·
                  refine ⟨5093228761191580618983233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13581943363177548317288621 5093228761191580618983233)
                  ·
                    refine ⟨3819921570893685464237425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5093228761191580618983233 3819921570893685464237425)
                    ·
                      refine ⟨2864941178170264098178069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3819921570893685464237425 2864941178170264098178069)
                      ·
                        rfl

theorem cell23_5579453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_5579453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579453 prefixEnd_5579453 := by exact prefixLift 5579453
  have htrace : WordTrace (prefixWord ++ tailWord_5579453) baseStart_5579453 baseEnd_5579453 := by
    simpa [prefixWord, tailWord_5579453, baseEnd_5579453] using wordTrace_append hprefix tailTrace_5579453
  have hstable : (prefixWord ++ tailWord_5579453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579453).length < 2 ^ (prefixWord ++ tailWord_5579453).sum := by decide
  have hdescent : baseEnd_5579453 < baseStart_5579453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579503 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 2, 1, 3]
def baseStart_5579503 : Nat := 118140960795 + 5579503 * 2 ^ 59
def prefixEnd_5579503 : Nat := 4983230072969 + 3 ^ 40 * 5579503 * 2
def baseEnd_5579503 : Nat := 2864966852202988902552839

theorem tailTrace_5579503 : CollatzResearch.WordTrace tailWord_5579503 prefixEnd_5579503 2864966852202988902552839 := by
  unfold tailWord_5579503
  simp only [CollatzResearch.WordTrace]
  refine ⟨203501192705421009093007163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135667461803614006062004775 203501192705421009093007163)
  ·
    refine ⟨305251789058131513639510745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203501192705421009093007163 305251789058131513639510745)
    ·
      refine ⟨228938841793598635229633059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305251789058131513639510745 228938841793598635229633059)
      ·
        refine ⟨343408262690397952844449589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228938841793598635229633059 343408262690397952844449589)
        ·
          refine ⟨32194524627224808079167149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 343408262690397952844449589 32194524627224808079167149)
          ·
            refine ⟨12072946735209303029687681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32194524627224808079167149 12072946735209303029687681)
            ·
              refine ⟨9054710051406977272265761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12072946735209303029687681 9054710051406977272265761)
              ·
                refine ⟨6791032538555232954199321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9054710051406977272265761 6791032538555232954199321)
                ·
                  refine ⟨5093274403916424715649491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6791032538555232954199321 5093274403916424715649491)
                  ·
                    refine ⟨7639911605874637073474237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5093274403916424715649491 7639911605874637073474237)
                    ·
                      refine ⟨2864966852202988902552839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7639911605874637073474237 2864966852202988902552839)
                      ·
                        rfl

theorem cell23_5579503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 1, 3].length) (baseStart_5579503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579503 prefixEnd_5579503 := by exact prefixLift 5579503
  have htrace : WordTrace (prefixWord ++ tailWord_5579503) baseStart_5579503 baseEnd_5579503 := by
    simpa [prefixWord, tailWord_5579503, baseEnd_5579503] using wordTrace_append hprefix tailTrace_5579503
  have hstable : (prefixWord ++ tailWord_5579503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579503).length < 2 ^ (prefixWord ++ tailWord_5579503).sum := by decide
  have hdescent : baseEnd_5579503 < baseStart_5579503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579566 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_5579566 : Nat := 118140960795 + 5579566 * 2 ^ 59
def prefixEnd_5579566 : Nat := 4983230072969 + 3 ^ 40 * 5579566 * 2
def baseEnd_5579566 : Nat := 318333244609358017340561

theorem tailTrace_5579566 : CollatzResearch.WordTrace tailWord_5579566 prefixEnd_5579566 318333244609358017340561 := by
  unfold tailWord_5579566
  simp only [CollatzResearch.WordTrace]
  refine ⟨25437936313024096356568819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135668993669461847235033701 25437936313024096356568819)
  ·
    refine ⟨38156904469536144534853229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25437936313024096356568819 38156904469536144534853229)
    ·
      refine ⟨14308839176076054200569961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38156904469536144534853229 14308839176076054200569961)
      ·
        refine ⟨10731629382057040650427471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14308839176076054200569961 10731629382057040650427471)
        ·
          refine ⟨16097444073085560975641207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10731629382057040650427471 16097444073085560975641207)
          ·
            refine ⟨24146166109628341463461811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16097444073085560975641207 24146166109628341463461811)
            ·
              refine ⟨36219249164442512195192717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24146166109628341463461811 36219249164442512195192717)
              ·
                refine ⟨13582218436665942073197269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36219249164442512195192717 13582218436665942073197269)
                ·
                  refine ⟨318333244609358017340561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13582218436665942073197269 318333244609358017340561)
                  ·
                    rfl

theorem cell23_5579566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_5579566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579566 prefixEnd_5579566 := by exact prefixLift 5579566
  have htrace : WordTrace (prefixWord ++ tailWord_5579566) baseStart_5579566 baseEnd_5579566 := by
    simpa [prefixWord, tailWord_5579566, baseEnd_5579566] using wordTrace_append hprefix tailTrace_5579566
  have hstable : (prefixWord ++ tailWord_5579566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579566).length < 2 ^ (prefixWord ++ tailWord_5579566).sum := by decide
  have hdescent : baseEnd_5579566 < baseStart_5579566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579599 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 4]
def baseStart_5579599 : Nat := 118140960795 + 5579599 * 2 ^ 59
def prefixEnd_5579599 : Nat := 4983230072969 + 3 ^ 40 * 5579599 * 2
def baseEnd_5579599 : Nat := 2865016146345820526952397

theorem tailTrace_5579599 : CollatzResearch.WordTrace tailWord_5579599 prefixEnd_5579599 2865016146345820526952397 := by
  unfold tailWord_5579599
  simp only [CollatzResearch.WordTrace]
  refine ⟨203504694113073217488501851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135669796075382144992334567 203504694113073217488501851)
  ·
    refine ⟨305257041169609826232752777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203504694113073217488501851 305257041169609826232752777)
    ·
      refine ⟨228942780877207369674564583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305257041169609826232752777 228942780877207369674564583)
      ·
        refine ⟨343414171315811054511846875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228942780877207369674564583 343414171315811054511846875)
        ·
          refine ⟨515121256973716581767770313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343414171315811054511846875 515121256973716581767770313)
          ·
            refine ⟨386340942730287436325827735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515121256973716581767770313 386340942730287436325827735)
            ·
              refine ⟨579511414095431154488741603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386340942730287436325827735 579511414095431154488741603)
              ·
                refine ⟨869267121143146731733112405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579511414095431154488741603 869267121143146731733112405)
                ·
                  refine ⟨10186724075896250762497411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 869267121143146731733112405 10186724075896250762497411)
                  ·
                    refine ⟨15280086113844376143746117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10186724075896250762497411 15280086113844376143746117)
                    ·
                      refine ⟨2865016146345820526952397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15280086113844376143746117 2865016146345820526952397)
                      ·
                        rfl

theorem cell23_5579599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_5579599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579599 prefixEnd_5579599 := by exact prefixLift 5579599
  have htrace : WordTrace (prefixWord ++ tailWord_5579599) baseStart_5579599 baseEnd_5579599 := by
    simpa [prefixWord, tailWord_5579599, baseEnd_5579599] using wordTrace_append hprefix tailTrace_5579599
  have hstable : (prefixWord ++ tailWord_5579599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579599).length < 2 ^ (prefixWord ++ tailWord_5579599).sum := by decide
  have hdescent : baseEnd_5579599 < baseStart_5579599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579616 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 4]
def baseStart_5579616 : Nat := 118140960795 + 5579616 * 2 ^ 59
def prefixEnd_5579616 : Nat := 4983230072969 + 3 ^ 40 * 5579616 * 2
def baseEnd_5579616 : Nat := 2865024875516946960439819

theorem tailTrace_5579616 : CollatzResearch.WordTrace tailWord_5579616 prefixEnd_5579616 2865024875516946960439819 := by
  unfold tailWord_5579616
  simp only [CollatzResearch.WordTrace]
  refine ⟨101752657077005814695935351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135670209436007752927913801 101752657077005814695935351)
  ·
    refine ⟨152628985615508722043903027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101752657077005814695935351 152628985615508722043903027)
    ·
      refine ⟨228943478423263083065854541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152628985615508722043903027 228943478423263083065854541)
      ·
        refine ⟨85853804408723656149695453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228943478423263083065854541 85853804408723656149695453)
        ·
          refine ⟨32195176653271371056135795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85853804408723656149695453 32195176653271371056135795)
          ·
            refine ⟨48292764979907056584203693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32195176653271371056135795 48292764979907056584203693)
            ·
              refine ⟨18109786867465146219076385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48292764979907056584203693 18109786867465146219076385)
              ·
                refine ⟨13582340150598859664307289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18109786867465146219076385 13582340150598859664307289)
                ·
                  refine ⟨10186755112949144748230467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13582340150598859664307289 10186755112949144748230467)
                  ·
                    refine ⟨15280132669423717122345701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10186755112949144748230467 15280132669423717122345701)
                    ·
                      refine ⟨2865024875516946960439819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15280132669423717122345701 2865024875516946960439819)
                      ·
                        rfl

theorem cell23_5579616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_5579616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579616 prefixEnd_5579616 := by exact prefixLift 5579616
  have htrace : WordTrace (prefixWord ++ tailWord_5579616) baseStart_5579616 baseEnd_5579616 := by
    simpa [prefixWord, tailWord_5579616, baseEnd_5579616] using wordTrace_append hprefix tailTrace_5579616
  have hstable : (prefixWord ++ tailWord_5579616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579616).length < 2 ^ (prefixWord ++ tailWord_5579616).sum := by decide
  have hdescent : baseEnd_5579616 < baseStart_5579616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579653 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 2, 2, 3]
def baseStart_5579653 : Nat := 118140960795 + 5579653 * 2 ^ 59
def prefixEnd_5579653 : Nat := 4983230072969 + 3 ^ 40 * 5579653 * 2
def baseEnd_5579653 : Nat := 2865043874301163315677149

theorem tailTrace_5579653 : CollatzResearch.WordTrace tailWord_5579653 prefixEnd_5579653 2865043874301163315677149 := by
  unfold tailWord_5579653
  simp only [CollatzResearch.WordTrace]
  refine ⟨203506663654877584710967613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135671109103251723140645075 203506663654877584710967613)
  ·
    refine ⟨76314998870579094266612855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203506663654877584710967613 76314998870579094266612855)
    ·
      refine ⟨114472498305868641399919283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76314998870579094266612855 114472498305868641399919283)
      ·
        refine ⟨171708747458802962099878925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114472498305868641399919283 171708747458802962099878925)
        ·
          refine ⟨64390780297051110787454597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171708747458802962099878925 64390780297051110787454597)
          ·
            refine ⟨12073271305697083272647737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64390780297051110787454597 12073271305697083272647737)
            ·
              refine ⟨9054953479272812454485803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12073271305697083272647737 9054953479272812454485803)
              ·
                refine ⟨13582430218909218681728705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9054953479272812454485803 13582430218909218681728705)
                ·
                  refine ⟨10186822664181914011296529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13582430218909218681728705 10186822664181914011296529)
                  ·
                    refine ⟨7640116998136435508472397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10186822664181914011296529 7640116998136435508472397)
                    ·
                      refine ⟨2865043874301163315677149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7640116998136435508472397 2865043874301163315677149)
                      ·
                        rfl

theorem cell23_5579653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_5579653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579653 prefixEnd_5579653 := by exact prefixLift 5579653
  have htrace : WordTrace (prefixWord ++ tailWord_5579653) baseStart_5579653 baseEnd_5579653 := by
    simpa [prefixWord, tailWord_5579653, baseEnd_5579653] using wordTrace_append hprefix tailTrace_5579653
  have hstable : (prefixWord ++ tailWord_5579653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579653).length < 2 ^ (prefixWord ++ tailWord_5579653).sum := by decide
  have hdescent : baseEnd_5579653 < baseStart_5579653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579706 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_5579706 : Nat := 118140960795 + 5579706 * 2 ^ 59
def prefixEnd_5579706 : Nat := 4983230072969 + 3 ^ 40 * 5579706 * 2
def baseEnd_5579706 : Nat := 2865071088775851608314405

theorem tailTrace_5579706 : CollatzResearch.WordTrace tailWord_5579706 prefixEnd_5579706 2865071088775851608314405 := by
  unfold tailWord_5579706
  simp only [CollatzResearch.WordTrace]
  refine ⟨50877149180921393690661743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135672397815790383175097981 50877149180921393690661743)
  ·
    refine ⟨76315723771382090535992615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50877149180921393690661743 76315723771382090535992615)
    ·
      refine ⟨114473585657073135803988923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76315723771382090535992615 114473585657073135803988923)
      ·
        refine ⟨171710378485609703705983385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114473585657073135803988923 171710378485609703705983385)
        ·
          refine ⟨128782783864207277779487539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171710378485609703705983385 128782783864207277779487539)
          ·
            refine ⟨193174175796310916669231309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128782783864207277779487539 193174175796310916669231309)
            ·
              refine ⟨72440315923616593750961741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193174175796310916669231309 72440315923616593750961741)
              ·
                refine ⟨27165118471356222656610653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72440315923616593750961741 27165118471356222656610653)
                ·
                  refine ⟨10186919426758583496228995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27165118471356222656610653 10186919426758583496228995)
                  ·
                    refine ⟨15280379140137875244343493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10186919426758583496228995 15280379140137875244343493)
                    ·
                      refine ⟨2865071088775851608314405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15280379140137875244343493 2865071088775851608314405)
                      ·
                        rfl

theorem cell23_5579706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_5579706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579706 prefixEnd_5579706 := by exact prefixLift 5579706
  have htrace : WordTrace (prefixWord ++ tailWord_5579706) baseStart_5579706 baseEnd_5579706 := by
    simpa [prefixWord, tailWord_5579706, baseEnd_5579706] using wordTrace_append hprefix tailTrace_5579706
  have hstable : (prefixWord ++ tailWord_5579706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579706).length < 2 ^ (prefixWord ++ tailWord_5579706).sum := by decide
  have hdescent : baseEnd_5579706 < baseStart_5579706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579723 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 4]
def baseStart_5579723 : Nat := 118140960795 + 5579723 * 2 ^ 59
def prefixEnd_5579723 : Nat := 4983230072969 + 3 ^ 40 * 5579723 * 2
def baseEnd_5579723 : Nat := 2865079817946978041801827

theorem tailTrace_5579723 : CollatzResearch.WordTrace tailWord_5579723 prefixEnd_5579723 2865079817946978041801827 := by
  unfold tailWord_5579723
  simp only [CollatzResearch.WordTrace]
  refine ⟨203509216764623986666015823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135672811176415991110677215 203509216764623986666015823)
  ·
    refine ⟨305263825146935979999023735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203509216764623986666015823 305263825146935979999023735)
    ·
      refine ⟨457895737720403969998535603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305263825146935979999023735 457895737720403969998535603)
      ·
        refine ⟨686843606580605954997803405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457895737720403969998535603 686843606580605954997803405)
        ·
          refine ⟨257566352467727233124176277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 686843606580605954997803405 257566352467727233124176277)
          ·
            refine ⟨12073422771924714052695763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 257566352467727233124176277 12073422771924714052695763)
            ·
              refine ⟨18110134157887071079043645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12073422771924714052695763 18110134157887071079043645)
              ·
                refine ⟨6791300309207651654641367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18110134157887071079043645 6791300309207651654641367)
                ·
                  refine ⟨10186950463811477481962051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6791300309207651654641367 10186950463811477481962051)
                  ·
                    refine ⟨15280425695717216222943077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10186950463811477481962051 15280425695717216222943077)
                    ·
                      refine ⟨2865079817946978041801827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15280425695717216222943077 2865079817946978041801827)
                      ·
                        rfl

theorem cell23_5579723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 1, 4].length) (baseStart_5579723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579723 prefixEnd_5579723 := by exact prefixLift 5579723
  have htrace : WordTrace (prefixWord ++ tailWord_5579723) baseStart_5579723 baseEnd_5579723 := by
    simpa [prefixWord, tailWord_5579723, baseEnd_5579723] using wordTrace_append hprefix tailTrace_5579723
  have hstable : (prefixWord ++ tailWord_5579723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579723).length < 2 ^ (prefixWord ++ tailWord_5579723).sum := by decide
  have hdescent : baseEnd_5579723 < baseStart_5579723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579729 : List Nat := [1, 2, 2, 1, 2, 1, 14]
def baseStart_5579729 : Nat := 118140960795 + 5579729 * 2 ^ 59
def prefixEnd_5579729 : Nat := 4983230072969 + 3 ^ 40 * 5579729 * 2
def baseEnd_5579729 : Nat := 35371393812727222448479

theorem tailTrace_5579729 : CollatzResearch.WordTrace tailWord_5579729 prefixEnd_5579729 35371393812727222448479 := by
  unfold tailWord_5579729
  simp only [CollatzResearch.WordTrace]
  refine ⟨203509435602602249690734241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135672957068401499793822827 203509435602602249690734241)
  ·
    refine ⟨152632076701951687268050681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203509435602602249690734241 152632076701951687268050681)
    ·
      refine ⟨114474057526463765451038011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152632076701951687268050681 114474057526463765451038011)
      ·
        refine ⟨171711086289695648176557017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114474057526463765451038011 171711086289695648176557017)
        ·
          refine ⟨128783314717271736132417763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171711086289695648176557017 128783314717271736132417763)
          ·
            refine ⟨193174972075907604198626645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128783314717271736132417763 193174972075907604198626645)
            ·
              refine ⟨35371393812727222448479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 193174972075907604198626645 35371393812727222448479)
              ·
                rfl

theorem cell23_5579729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 14].length) (baseStart_5579729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579729 prefixEnd_5579729 := by exact prefixLift 5579729
  have htrace : WordTrace (prefixWord ++ tailWord_5579729) baseStart_5579729 baseEnd_5579729 := by
    simpa [prefixWord, tailWord_5579729, baseEnd_5579729] using wordTrace_append hprefix tailTrace_5579729
  have hstable : (prefixWord ++ tailWord_5579729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579729).length < 2 ^ (prefixWord ++ tailWord_5579729).sum := by decide
  have hdescent : baseEnd_5579729 < baseStart_5579729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579734 : List Nat := [5, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_5579734 : Nat := 118140960795 + 5579734 * 2 ^ 59
def prefixEnd_5579734 : Nat := 4983230072969 + 3 ^ 40 * 5579734 * 2
def baseEnd_5579734 : Nat := 2865085466234177498764277

theorem tailTrace_5579734 : CollatzResearch.WordTrace tailWord_5579734 prefixEnd_5579734 2865085466234177498764277 := by
  unfold tailWord_5579734
  simp only [CollatzResearch.WordTrace]
  refine ⟨12719351122974008471541641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135673078645056090363110837 12719351122974008471541641)
  ·
    refine ⟨9539513342230506353656231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12719351122974008471541641 9539513342230506353656231)
    ·
      refine ⟨14309270013345759530484347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9539513342230506353656231 14309270013345759530484347)
      ·
        refine ⟨21463905020018639295726521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14309270013345759530484347 21463905020018639295726521)
        ·
          refine ⟨16097928765013979471794891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21463905020018639295726521 16097928765013979471794891)
          ·
            refine ⟨24146893147520969207692337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16097928765013979471794891 24146893147520969207692337)
            ·
              refine ⟨18110169860640726905769253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24146893147520969207692337 18110169860640726905769253)
              ·
                refine ⟨3395656848870136294831735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18110169860640726905769253 3395656848870136294831735)
                ·
                  refine ⟨5093485273305204442247603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3395656848870136294831735 5093485273305204442247603)
                  ·
                    refine ⟨7640227909957806663371405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5093485273305204442247603 7640227909957806663371405)
                    ·
                      refine ⟨2865085466234177498764277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7640227909957806663371405 2865085466234177498764277)
                      ·
                        rfl

theorem cell23_5579734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_5579734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579734 prefixEnd_5579734 := by exact prefixLift 5579734
  have htrace : WordTrace (prefixWord ++ tailWord_5579734) baseStart_5579734 baseEnd_5579734 := by
    simpa [prefixWord, tailWord_5579734, baseEnd_5579734] using wordTrace_append hprefix tailTrace_5579734
  have hstable : (prefixWord ++ tailWord_5579734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579734).length < 2 ^ (prefixWord ++ tailWord_5579734).sum := by decide
  have hdescent : baseEnd_5579734 < baseStart_5579734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579743 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 5]
def baseStart_5579743 : Nat := 118140960795 + 5579743 * 2 ^ 59
def prefixEnd_5579743 : Nat := 4983230072969 + 3 ^ 40 * 5579743 * 2
def baseEnd_5579743 : Nat := 2865090087560067963551735

theorem tailTrace_5579743 : CollatzResearch.WordTrace tailWord_5579743 prefixEnd_5579743 2865090087560067963551735 := by
  unfold tailWord_5579743
  simp only [CollatzResearch.WordTrace]
  refine ⟨203509946224551530081743883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135673297483034353387829255 203509946224551530081743883)
  ·
    refine ⟨305264919336827295122615825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203509946224551530081743883 305264919336827295122615825)
    ·
      refine ⟨228948689502620471341961869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305264919336827295122615825 228948689502620471341961869)
      ·
        refine ⟨85855758563482676753235701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228948689502620471341961869 85855758563482676753235701)
        ·
          refine ⟨8048977365326500945615847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 85855758563482676753235701 8048977365326500945615847)
          ·
            refine ⟨12073466047989751418423771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8048977365326500945615847 12073466047989751418423771)
            ·
              refine ⟨18110199071984627127635657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12073466047989751418423771 18110199071984627127635657)
              ·
                refine ⟨13582649303988470345726743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18110199071984627127635657 13582649303988470345726743)
                ·
                  refine ⟨20373973955982705518590115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13582649303988470345726743 20373973955982705518590115)
                  ·
                    refine ⟨30560960933974058277885173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20373973955982705518590115 30560960933974058277885173)
                    ·
                      refine ⟨2865090087560067963551735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30560960933974058277885173 2865090087560067963551735)
                      ·
                        rfl

theorem cell23_5579743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_5579743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579743 prefixEnd_5579743 := by exact prefixLift 5579743
  have htrace : WordTrace (prefixWord ++ tailWord_5579743) baseStart_5579743 baseEnd_5579743 := by
    simpa [prefixWord, tailWord_5579743, baseEnd_5579743] using wordTrace_append hprefix tailTrace_5579743
  have hstable : (prefixWord ++ tailWord_5579743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579743).length < 2 ^ (prefixWord ++ tailWord_5579743).sum := by decide
  have hdescent : baseEnd_5579743 < baseStart_5579743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579790 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_5579790 : Nat := 118140960795 + 5579790 * 2 ^ 59
def prefixEnd_5579790 : Nat := 4983230072969 + 3 ^ 40 * 5579790 * 2
def baseEnd_5579790 : Nat := 2865114221150829279664019

theorem tailTrace_5579790 : CollatzResearch.WordTrace tailWord_5579790 prefixEnd_5579790 2865114221150829279664019 := by
  unfold tailWord_5579790
  simp only [CollatzResearch.WordTrace]
  refine ⟨25438957556922657138588103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135674440303587504739136549 25438957556922657138588103)
  ·
    refine ⟨38158436335383985707882155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25438957556922657138588103 38158436335383985707882155)
    ·
      refine ⟨57237654503075978561823233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38158436335383985707882155 57237654503075978561823233)
      ·
        refine ⟨42928240877306983921367425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57237654503075978561823233 42928240877306983921367425)
        ·
          refine ⟨32196180657980237941025569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42928240877306983921367425 32196180657980237941025569)
          ·
            refine ⟨24147135493485178455769177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32196180657980237941025569 24147135493485178455769177)
            ·
              refine ⟨18110351620113883841826883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24147135493485178455769177 18110351620113883841826883)
              ·
                refine ⟨27165527430170825762740325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18110351620113883841826883 27165527430170825762740325)
                ·
                  refine ⟨5093536393157029830513811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27165527430170825762740325 5093536393157029830513811)
                  ·
                    refine ⟨7640304589735544745770717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5093536393157029830513811 7640304589735544745770717)
                    ·
                      refine ⟨2865114221150829279664019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7640304589735544745770717 2865114221150829279664019)
                      ·
                        rfl

theorem cell23_5579790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_5579790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579790 prefixEnd_5579790 := by exact prefixLift 5579790
  have htrace : WordTrace (prefixWord ++ tailWord_5579790) baseStart_5579790 baseEnd_5579790 := by
    simpa [prefixWord, tailWord_5579790, baseEnd_5579790] using wordTrace_append hprefix tailTrace_5579790
  have hstable : (prefixWord ++ tailWord_5579790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579790).length < 2 ^ (prefixWord ++ tailWord_5579790).sum := by decide
  have hdescent : baseEnd_5579790 < baseStart_5579790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579807 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 2, 1, 3]
def baseStart_5579807 : Nat := 118140960795 + 5579807 * 2 ^ 59
def prefixEnd_5579807 : Nat := 4983230072969 + 3 ^ 40 * 5579807 * 2
def baseEnd_5579807 : Nat := 2865122950321955713151441

theorem tailTrace_5579807 : CollatzResearch.WordTrace tailWord_5579807 prefixEnd_5579807 2865122950321955713151441 := by
  unfold tailWord_5579807
  simp only [CollatzResearch.WordTrace]
  refine ⟨203512280496319669012073675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135674853664213112674715783 203512280496319669012073675)
  ·
    refine ⟨305268420744479503518110513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203512280496319669012073675 305268420744479503518110513)
    ·
      refine ⟨228951315558359627638582885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305268420744479503518110513 228951315558359627638582885)
      ·
        refine ⟨42928371667192430182234291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228951315558359627638582885 42928371667192430182234291)
        ·
          refine ⟨64392557500788645273351437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42928371667192430182234291 64392557500788645273351437)
          ·
            refine ⟨24147209062795741977506789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64392557500788645273351437 24147209062795741977506789)
            ·
              refine ⟨4527601699274201620782523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24147209062795741977506789 4527601699274201620782523)
              ·
                refine ⟨6791402548911302431173785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4527601699274201620782523 6791402548911302431173785)
                ·
                  refine ⟨5093551911683476823380339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6791402548911302431173785 5093551911683476823380339)
                  ·
                    refine ⟨7640327867525215235070509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5093551911683476823380339 7640327867525215235070509)
                    ·
                      refine ⟨2865122950321955713151441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7640327867525215235070509 2865122950321955713151441)
                      ·
                        rfl

theorem cell23_5579807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_5579807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579807 prefixEnd_5579807 := by exact prefixLift 5579807
  have htrace : WordTrace (prefixWord ++ tailWord_5579807) baseStart_5579807 baseEnd_5579807 := by
    simpa [prefixWord, tailWord_5579807, baseEnd_5579807] using wordTrace_append hprefix tailTrace_5579807
  have hstable : (prefixWord ++ tailWord_5579807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579807).length < 2 ^ (prefixWord ++ tailWord_5579807).sum := by decide
  have hdescent : baseEnd_5579807 < baseStart_5579807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579833 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 5]
def baseStart_5579833 : Nat := 118140960795 + 5579833 * 2 ^ 59
def prefixEnd_5579833 : Nat := 4983230072969 + 3 ^ 40 * 5579833 * 2
def baseEnd_5579833 : Nat := 2865136300818972611426321

theorem tailTrace_5579833 : CollatzResearch.WordTrace tailWord_5579833 prefixEnd_5579833 2865136300818972611426321 := by
  unfold tailWord_5579833
  simp only [CollatzResearch.WordTrace]
  refine ⟨203513228794225475452520153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135675485862816983635013435 203513228794225475452520153)
  ·
    refine ⟨152634921595669106589390115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203513228794225475452520153 152634921595669106589390115)
    ·
      refine ⟨228952382393503659884085173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152634921595669106589390115 228952382393503659884085173)
      ·
        refine ⟨21464285849390968114132985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228952382393503659884085173 21464285849390968114132985)
        ·
          refine ⟨16098214387043226085599739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21464285849390968114132985 16098214387043226085599739)
          ·
            refine ⟨24147321580564839128399609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16098214387043226085599739 24147321580564839128399609)
            ·
              refine ⟨18110491185423629346299707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24147321580564839128399609 18110491185423629346299707)
              ·
                refine ⟨27165736778135444019449561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18110491185423629346299707 27165736778135444019449561)
                ·
                  refine ⟨20374302583601583014587171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27165736778135444019449561 20374302583601583014587171)
                  ·
                    refine ⟨30561453875402374521880757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20374302583601583014587171 30561453875402374521880757)
                    ·
                      refine ⟨2865136300818972611426321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30561453875402374521880757 2865136300818972611426321)
                      ·
                        rfl

theorem cell23_5579833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_5579833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579833 prefixEnd_5579833 := by exact prefixLift 5579833
  have htrace : WordTrace (prefixWord ++ tailWord_5579833) baseStart_5579833 baseEnd_5579833 := by
    simpa [prefixWord, tailWord_5579833, baseEnd_5579833] using wordTrace_append hprefix tailTrace_5579833
  have hstable : (prefixWord ++ tailWord_5579833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579833).length < 2 ^ (prefixWord ++ tailWord_5579833).sum := by decide
  have hdescent : baseEnd_5579833 < baseStart_5579833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579847 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 2, 2, 2]
def baseStart_5579847 : Nat := 118140960795 + 5579847 * 2 ^ 59
def prefixEnd_5579847 : Nat := 4983230072969 + 3 ^ 40 * 5579847 * 2
def baseEnd_5579847 : Nat := 2865143489548135556651257

theorem tailTrace_5579847 : CollatzResearch.WordTrace tailWord_5579847 prefixEnd_5579847 2865143489548135556651257 := by
  unfold tailWord_5579847
  simp only [CollatzResearch.WordTrace]
  refine ⟨203513739416174755843529795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135675826277449837229019863 203513739416174755843529795)
  ·
    refine ⟨305270609124262133765294693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203513739416174755843529795 305270609124262133765294693)
    ·
      refine ⟨57238239210799150080992755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 305270609124262133765294693 57238239210799150080992755)
      ·
        refine ⟨85857358816198725121489133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57238239210799150080992755 85857358816198725121489133)
        ·
          refine ⟨32196509556074521920558425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85857358816198725121489133 32196509556074521920558425)
          ·
            refine ⟨24147382167055891440418819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32196509556074521920558425 24147382167055891440418819)
            ·
              refine ⟨36221073250583837160628229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24147382167055891440418819 36221073250583837160628229)
              ·
                refine ⟨6791451234484469467617793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36221073250583837160628229 6791451234484469467617793)
                ·
                  refine ⟨5093588425863352100713345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6791451234484469467617793 5093588425863352100713345)
                  ·
                    refine ⟨3820191319397514075535009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5093588425863352100713345 3820191319397514075535009)
                    ·
                      refine ⟨2865143489548135556651257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820191319397514075535009 2865143489548135556651257)
                      ·
                        rfl

theorem cell23_5579847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_5579847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579847 prefixEnd_5579847 := by exact prefixLift 5579847
  have htrace : WordTrace (prefixWord ++ tailWord_5579847) baseStart_5579847 baseEnd_5579847 := by
    simpa [prefixWord, tailWord_5579847, baseEnd_5579847] using wordTrace_append hprefix tailTrace_5579847
  have hstable : (prefixWord ++ tailWord_5579847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579847).length < 2 ^ (prefixWord ++ tailWord_5579847).sum := by decide
  have hdescent : baseEnd_5579847 < baseStart_5579847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579923 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 3]
def baseStart_5579923 : Nat := 118140960795 + 5579923 * 2 ^ 59
def prefixEnd_5579923 : Nat := 4983230072969 + 3 ^ 40 * 5579923 * 2
def baseEnd_5579923 : Nat := 2865182514077877259300907

theorem tailTrace_5579923 : CollatzResearch.WordTrace tailWord_5579923 prefixEnd_5579923 2865182514077877259300907 := by
  unfold tailWord_5579923
  simp only [CollatzResearch.WordTrace]
  refine ⟨203516511363899420823296423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135677674242599613882197615 203516511363899420823296423)
  ·
    refine ⟨305274767045849131234944635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203516511363899420823296423 305274767045849131234944635)
    ·
      refine ⟨457912150568773696852416953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305274767045849131234944635 457912150568773696852416953)
      ·
        refine ⟨343434112926580272639312715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457912150568773696852416953 343434112926580272639312715)
        ·
          refine ⟨515151169389870408958969073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343434112926580272639312715 515151169389870408958969073)
          ·
            refine ⟨386363377042402806719226805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515151169389870408958969073 386363377042402806719226805)
            ·
              refine ⟨36221566597725263129927513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 386363377042402806719226805 36221566597725263129927513)
              ·
                refine ⟨27166174948293947347445635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36221566597725263129927513 27166174948293947347445635)
                ·
                  refine ⟨40749262422440921021168453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27166174948293947347445635 40749262422440921021168453)
                  ·
                    refine ⟨7640486704207672691469085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40749262422440921021168453 7640486704207672691469085)
                    ·
                      refine ⟨2865182514077877259300907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7640486704207672691469085 2865182514077877259300907)
                      ·
                        rfl

theorem cell23_5579923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 3].length) (baseStart_5579923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579923 prefixEnd_5579923 := by exact prefixLift 5579923
  have htrace : WordTrace (prefixWord ++ tailWord_5579923) baseStart_5579923 baseEnd_5579923 := by
    simpa [prefixWord, tailWord_5579923, baseEnd_5579923] using wordTrace_append hprefix tailTrace_5579923
  have hstable : (prefixWord ++ tailWord_5579923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579923).length < 2 ^ (prefixWord ++ tailWord_5579923).sum := by decide
  have hdescent : baseEnd_5579923 < baseStart_5579923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579933 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_5579933 : Nat := 118140960795 + 5579933 * 2 ^ 59
def prefixEnd_5579933 : Nat := 4983230072969 + 3 ^ 40 * 5579933 * 2
def baseEnd_5579933 : Nat := 2865187648884422220175861

theorem tailTrace_5579933 : CollatzResearch.WordTrace tailWord_5579933 prefixEnd_5579933 2865187648884422220175861 := by
  unfold tailWord_5579933
  simp only [CollatzResearch.WordTrace]
  refine ⟨203516876093863192531160453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135677917395908795020773635 203516876093863192531160453)
  ·
    refine ⟨38159414267599348599592585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203516876093863192531160453 38159414267599348599592585)
    ·
      refine ⟨28619560700699511449694439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38159414267599348599592585 28619560700699511449694439)
      ·
        refine ⟨42929341051049267174541659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28619560700699511449694439 42929341051049267174541659)
        ·
          refine ⟨64394011576573900761812489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42929341051049267174541659 64394011576573900761812489)
          ·
            refine ⟨48295508682430425571359367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64394011576573900761812489 48295508682430425571359367)
            ·
              refine ⟨72443263023645638357039051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48295508682430425571359367 72443263023645638357039051)
              ·
                refine ⟨108664894535468457535558577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72443263023645638357039051 108664894535468457535558577)
                ·
                  refine ⟨81498670901601343151668933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108664894535468457535558577 81498670901601343151668933)
                  ·
                    refine ⟨15281000794050251840937925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81498670901601343151668933 15281000794050251840937925)
                    ·
                      refine ⟨2865187648884422220175861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15281000794050251840937925 2865187648884422220175861)
                      ·
                        rfl

theorem cell23_5579933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_5579933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579933 prefixEnd_5579933 := by exact prefixLift 5579933
  have htrace : WordTrace (prefixWord ++ tailWord_5579933) baseStart_5579933 baseEnd_5579933 := by
    simpa [prefixWord, tailWord_5579933, baseEnd_5579933] using wordTrace_append hprefix tailTrace_5579933
  have hstable : (prefixWord ++ tailWord_5579933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579933).length < 2 ^ (prefixWord ++ tailWord_5579933).sum := by decide
  have hdescent : baseEnd_5579933 < baseStart_5579933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579940 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_5579940 : Nat := 118140960795 + 5579940 * 2 ^ 59
def prefixEnd_5579940 : Nat := 4983230072969 + 3 ^ 40 * 5579940 * 2
def baseEnd_5579940 : Nat := 2865191243249003692788329

theorem tailTrace_5579940 : CollatzResearch.WordTrace tailWord_5579940 prefixEnd_5579940 2865191243249003692788329 := by
  unfold tailWord_5579940
  simp only [CollatzResearch.WordTrace]
  refine ⟨101758565702418916363332637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135678087603225221817776849 101758565702418916363332637)
  ·
    refine ⟨38159462138407093636249739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101758565702418916363332637 38159462138407093636249739)
    ·
      refine ⟨57239193207610640454374609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38159462138407093636249739 57239193207610640454374609)
      ·
        refine ⟨42929394905707980340780957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57239193207610640454374609 42929394905707980340780957)
        ·
          refine ⟨16098523089640492627792859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42929394905707980340780957 16098523089640492627792859)
          ·
            refine ⟨24147784634460738941689289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16098523089640492627792859 24147784634460738941689289)
            ·
              refine ⟨18110838475845554206266967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24147784634460738941689289 18110838475845554206266967)
              ·
                refine ⟨27166257713768331309400451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18110838475845554206266967 27166257713768331309400451)
                ·
                  refine ⟨40749386570652496964100677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27166257713768331309400451 40749386570652496964100677)
                  ·
                    refine ⟨7640509981997343180768877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40749386570652496964100677 7640509981997343180768877)
                    ·
                      refine ⟨2865191243249003692788329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7640509981997343180768877 2865191243249003692788329)
                      ·
                        rfl

theorem cell23_5579940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_5579940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579940 prefixEnd_5579940 := by exact prefixLift 5579940
  have htrace : WordTrace (prefixWord ++ tailWord_5579940) baseStart_5579940 baseEnd_5579940 := by
    simpa [prefixWord, tailWord_5579940, baseEnd_5579940] using wordTrace_append hprefix tailTrace_5579940
  have hstable : (prefixWord ++ tailWord_5579940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579940).length < 2 ^ (prefixWord ++ tailWord_5579940).sum := by decide
  have hdescent : baseEnd_5579940 < baseStart_5579940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5579973 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_5579973 : Nat := 118140960795 + 5579973 * 2 ^ 59
def prefixEnd_5579973 : Nat := 4983230072969 + 3 ^ 40 * 5579973 * 2
def baseEnd_5579973 : Nat := 955069396036867354558559

theorem tailTrace_5579973 : CollatzResearch.WordTrace tailWord_5579973 prefixEnd_5579973 955069396036867354558559 := by
  unfold tailWord_5579973
  simp only [CollatzResearch.WordTrace]
  refine ⟨203518335013718279362616573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135678890009145519575077715 203518335013718279362616573)
  ·
    refine ⟨76319375630144354760981215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203518335013718279362616573 76319375630144354760981215)
    ·
      refine ⟨114479063445216532141471823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76319375630144354760981215 114479063445216532141471823)
      ·
        refine ⟨171718595167824798212207735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114479063445216532141471823 171718595167824798212207735)
        ·
          refine ⟨257577892751737197318311603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171718595167824798212207735 257577892751737197318311603)
          ·
            refine ⟨386366839127605795977467405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257577892751737197318311603 386366839127605795977467405)
            ·
              refine ⟨144887564672852173491550277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386366839127605795977467405 144887564672852173491550277)
              ·
                refine ⟨27166418376159782529665677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144887564672852173491550277 27166418376159782529665677)
                ·
                  refine ⟨10187406891059918448624629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27166418376159782529665677 10187406891059918448624629)
                  ·
                    refine ⟨955069396036867354558559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10187406891059918448624629 955069396036867354558559)
                    ·
                      rfl

theorem cell23_5579973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_5579973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5579973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5579973 prefixEnd_5579973 := by exact prefixLift 5579973
  have htrace : WordTrace (prefixWord ++ tailWord_5579973) baseStart_5579973 baseEnd_5579973 := by
    simpa [prefixWord, tailWord_5579973, baseEnd_5579973] using wordTrace_append hprefix tailTrace_5579973
  have hstable : (prefixWord ++ tailWord_5579973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5579973).length < 2 ^ (prefixWord ++ tailWord_5579973).sum := by decide
  have hdescent : baseEnd_5579973 < baseStart_5579973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5579973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580044 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 3, 2, 2]
def baseStart_5580044 : Nat := 118140960795 + 5580044 * 2 ^ 59
def prefixEnd_5580044 : Nat := 4983230072969 + 3 ^ 40 * 5580044 * 2
def baseEnd_5580044 : Nat := 2865244645237071285887851

theorem tailTrace_5580044 : CollatzResearch.WordTrace tailWord_5580044 prefixEnd_5580044 2865244645237071285887851 := by
  unfold tailWord_5580044
  simp only [CollatzResearch.WordTrace]
  refine ⟨101760462298230529244225593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135680616397640705658967457 101760462298230529244225593)
  ·
    refine ⟨76320346723672896933169195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101760462298230529244225593 76320346723672896933169195)
    ·
      refine ⟨114480520085509345399753793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76320346723672896933169195 114480520085509345399753793)
      ·
        refine ⟨85860390064132009049815345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114480520085509345399753793 85860390064132009049815345)
        ·
          refine ⟨64395292548099006787361509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85860390064132009049815345 64395292548099006787361509)
          ·
            refine ⟨12074117352768563772630283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64395292548099006787361509 12074117352768563772630283)
            ·
              refine ⟨18111176029152845658945425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12074117352768563772630283 18111176029152845658945425)
              ·
                refine ⟨13583382021864634244209069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18111176029152845658945425 13583382021864634244209069)
                ·
                  refine ⟨5093768258199237841578401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13583382021864634244209069 5093768258199237841578401)
                  ·
                    refine ⟨3820326193649428381183801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5093768258199237841578401 3820326193649428381183801)
                    ·
                      refine ⟨2865244645237071285887851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820326193649428381183801 2865244645237071285887851)
                      ·
                        rfl

theorem cell23_5580044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_5580044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580044 prefixEnd_5580044 := by exact prefixLift 5580044
  have htrace : WordTrace (prefixWord ++ tailWord_5580044) baseStart_5580044 baseEnd_5580044 := by
    simpa [prefixWord, tailWord_5580044, baseEnd_5580044] using wordTrace_append hprefix tailTrace_5580044
  have hstable : (prefixWord ++ tailWord_5580044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580044).length < 2 ^ (prefixWord ++ tailWord_5580044).sum := by decide
  have hdescent : baseEnd_5580044 < baseStart_5580044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580061 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_5580061 : Nat := 118140960795 + 5580061 * 2 ^ 59
def prefixEnd_5580061 : Nat := 4983230072969 + 3 ^ 40 * 5580061 * 2
def baseEnd_5580061 : Nat := 2865253374408197719375273

theorem tailTrace_5580061 : CollatzResearch.WordTrace tailWord_5580061 prefixEnd_5580061 2865253374408197719375273 := by
  unfold tailWord_5580061
  simp only [CollatzResearch.WordTrace]
  refine ⟨203521544637399470391820037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135681029758266313594546691 203521544637399470391820037)
  ·
    refine ⟨38160289619512400698466257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203521544637399470391820037 38160289619512400698466257)
    ·
      refine ⟨28620217214634300523849693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38160289619512400698466257 28620217214634300523849693)
      ·
        refine ⟨10732581455487862696443635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28620217214634300523849693 10732581455487862696443635)
        ·
          refine ⟨16098872183231794044665453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10732581455487862696443635 16098872183231794044665453)
          ·
            refine ⟨6037077068711922766749545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16098872183231794044665453 6037077068711922766749545)
            ·
              refine ⟨4527807801533942075062159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6037077068711922766749545 4527807801533942075062159)
              ·
                refine ⟨6791711702300913112593239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4527807801533942075062159 6791711702300913112593239)
                ·
                  refine ⟨10187567553451369668889859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6791711702300913112593239 10187567553451369668889859)
                  ·
                    refine ⟨15281351330177054503334789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10187567553451369668889859 15281351330177054503334789)
                    ·
                      refine ⟨2865253374408197719375273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15281351330177054503334789 2865253374408197719375273)
                      ·
                        rfl

theorem cell23_5580061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_5580061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580061 prefixEnd_5580061 := by exact prefixLift 5580061
  have htrace : WordTrace (prefixWord ++ tailWord_5580061) baseStart_5580061 baseEnd_5580061 := by
    simpa [prefixWord, tailWord_5580061, baseEnd_5580061] using wordTrace_append hprefix tailTrace_5580061
  have hstable : (prefixWord ++ tailWord_5580061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580061).length < 2 ^ (prefixWord ++ tailWord_5580061).sum := by decide
  have hdescent : baseEnd_5580061 < baseStart_5580061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580064 : List Nat := [2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 3]
def baseStart_5580064 : Nat := 118140960795 + 5580064 * 2 ^ 59
def prefixEnd_5580064 : Nat := 4983230072969 + 3 ^ 40 * 5580064 * 2
def baseEnd_5580064 : Nat := 2865254914850161207637759

theorem tailTrace_5580064 : CollatzResearch.WordTrace tailWord_5580064 prefixEnd_5580064 2865254914850161207637759 := by
  unfold tailWord_5580064
  simp only [CollatzResearch.WordTrace]
  refine ⟨101760827028194300952089623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135681102704259067936119497 101760827028194300952089623)
  ·
    refine ⟨152641240542291451428134435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101760827028194300952089623 152641240542291451428134435)
    ·
      refine ⟨228961860813437177142201653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152641240542291451428134435 228961860813437177142201653)
      ·
        refine ⟨21465174451259735357081405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228961860813437177142201653 21465174451259735357081405)
        ·
          refine ⟨8049440419222400758905527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21465174451259735357081405 8049440419222400758905527)
          ·
            refine ⟨12074160628833601138358291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8049440419222400758905527 12074160628833601138358291)
            ·
              refine ⟨18111240943250401707537437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12074160628833601138358291 18111240943250401707537437)
              ·
                refine ⟨6791715353718900640326539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18111240943250401707537437 6791715353718900640326539)
                ·
                  refine ⟨10187573030578350960489809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6791715353718900640326539 10187573030578350960489809)
                  ·
                    refine ⟨7640679772933763220367357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10187573030578350960489809 7640679772933763220367357)
                    ·
                      refine ⟨2865254914850161207637759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7640679772933763220367357 2865254914850161207637759)
                      ·
                        rfl

theorem cell23_5580064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_5580064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580064 prefixEnd_5580064 := by exact prefixLift 5580064
  have htrace : WordTrace (prefixWord ++ tailWord_5580064) baseStart_5580064 baseEnd_5580064 := by
    simpa [prefixWord, tailWord_5580064, baseEnd_5580064] using wordTrace_append hprefix tailTrace_5580064
  have hstable : (prefixWord ++ tailWord_5580064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580064).length < 2 ^ (prefixWord ++ tailWord_5580064).sum := by decide
  have hdescent : baseEnd_5580064 < baseStart_5580064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580118 : List Nat := [5, 2, 3, 1, 2, 1, 9]
def baseStart_5580118 : Nat := 118140960795 + 5580118 * 2 ^ 59
def prefixEnd_5580118 : Nat := 4983230072969 + 3 ^ 40 * 5580118 * 2
def baseEnd_5580118 : Nat := 35373859787722271560031

theorem tailTrace_5580118 : CollatzResearch.WordTrace tailWord_5580118 prefixEnd_5580118 35373859787722271560031 := by
  unfold tailWord_5580118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12720226474887060570415313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135682415732128646084430005 12720226474887060570415313)
  ·
    refine ⟨9540169856165295427811485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12720226474887060570415313 9540169856165295427811485)
    ·
      refine ⟨3577563696061985785429307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9540169856165295427811485 3577563696061985785429307)
      ·
        refine ⟨5366345544092978678143961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3577563696061985785429307 5366345544092978678143961)
        ·
          refine ⟨4024759158069734008607971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5366345544092978678143961 4024759158069734008607971)
          ·
            refine ⟨6037138737104601012911957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4024759158069734008607971 6037138737104601012911957)
            ·
              refine ⟨35373859787722271560031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6037138737104601012911957 35373859787722271560031)
              ·
                rfl

theorem cell23_5580118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 9].length) (baseStart_5580118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580118 prefixEnd_5580118 := by exact prefixLift 5580118
  have htrace : WordTrace (prefixWord ++ tailWord_5580118) baseStart_5580118 baseEnd_5580118 := by
    simpa [prefixWord, tailWord_5580118, baseEnd_5580118] using wordTrace_append hprefix tailTrace_5580118
  have hstable : (prefixWord ++ tailWord_5580118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580118).length < 2 ^ (prefixWord ++ tailWord_5580118).sum := by decide
  have hdescent : baseEnd_5580118 < baseStart_5580118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580120 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 2, 1, 5]
def baseStart_5580120 : Nat := 118140960795 + 5580120 * 2 ^ 59
def prefixEnd_5580120 : Nat := 4983230072969 + 3 ^ 40 * 5580120 * 2
def baseEnd_5580120 : Nat := 2865283669766812988537501

theorem tailTrace_5580120 : CollatzResearch.WordTrace tailWord_5580120 prefixEnd_5580120 2865283669766812988537501 := by
  unfold tailWord_5580120
  simp only [CollatzResearch.WordTrace]
  refine ⟨101761848272092861734108907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135682464362790482312145209 101761848272092861734108907)
  ·
    refine ⟨152642772408139292601163361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101761848272092861734108907 152642772408139292601163361)
    ·
      refine ⟨114482079306104469450872521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152642772408139292601163361 114482079306104469450872521)
      ·
        refine ⟨85861559479578352088154391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114482079306104469450872521 85861559479578352088154391)
        ·
          refine ⟨128792339219367528132231587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85861559479578352088154391 128792339219367528132231587)
          ·
            refine ⟨193188508829051292198347381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128792339219367528132231587 193188508829051292198347381)
            ·
              refine ⟨18111422702723558643595067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193188508829051292198347381 18111422702723558643595067)
              ·
                refine ⟨27167134054085337965392601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18111422702723558643595067 27167134054085337965392601)
                ·
                  refine ⟨20375350540564003474044451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27167134054085337965392601 20375350540564003474044451)
                  ·
                    refine ⟨30563025810846005211066677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20375350540564003474044451 30563025810846005211066677)
                    ·
                      refine ⟨2865283669766812988537501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30563025810846005211066677 2865283669766812988537501)
                      ·
                        rfl

theorem cell23_5580120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_5580120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580120 prefixEnd_5580120 := by exact prefixLift 5580120
  have htrace : WordTrace (prefixWord ++ tailWord_5580120) baseStart_5580120 baseEnd_5580120 := by
    simpa [prefixWord, tailWord_5580120, baseEnd_5580120] using wordTrace_append hprefix tailTrace_5580120
  have hstable : (prefixWord ++ tailWord_5580120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580120).length < 2 ^ (prefixWord ++ tailWord_5580120).sum := by decide
  have hdescent : baseEnd_5580120 < baseStart_5580120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580191 : List Nat := [1, 1, 2, 5, 1, 4, 2, 2, 5]
def baseStart_5580191 : Nat := 118140960795 + 5580191 * 2 ^ 59
def prefixEnd_5580191 : Nat := 4983230072969 + 3 ^ 40 * 5580191 * 2
def baseEnd_5580191 : Nat := 318368902988142467861075

theorem tailTrace_5580191 : CollatzResearch.WordTrace tailWord_5580191 prefixEnd_5580191 318368902988142467861075 := by
  unfold tailWord_5580191
  simp only [CollatzResearch.WordTrace]
  refine ⟨203526286126928502594052427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135684190751285668396034951 203526286126928502594052427)
  ·
    refine ⟨305289429190392753891078641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203526286126928502594052427 305289429190392753891078641)
    ·
      refine ⟨228967071892794565418308981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305289429190392753891078641 228967071892794565418308981)
      ·
        refine ⟨21465662989949490507966467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228967071892794565418308981 21465662989949490507966467)
        ·
          refine ⟨32198494484924235761949701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21465662989949490507966467 32198494484924235761949701)
          ·
            refine ⟨6037217715923294205365569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32198494484924235761949701 6037217715923294205365569)
            ·
              refine ⟨4527913286942470654024177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6037217715923294205365569 4527913286942470654024177)
              ·
                refine ⟨3395934965206852990518133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4527913286942470654024177 3395934965206852990518133)
                ·
                  refine ⟨318368902988142467861075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3395934965206852990518133 318368902988142467861075)
                  ·
                    rfl

theorem cell23_5580191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 5].length) (baseStart_5580191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580191 prefixEnd_5580191 := by exact prefixLift 5580191
  have htrace : WordTrace (prefixWord ++ tailWord_5580191) baseStart_5580191 baseEnd_5580191 := by
    simpa [prefixWord, tailWord_5580191, baseEnd_5580191] using wordTrace_append hprefix tailTrace_5580191
  have hstable : (prefixWord ++ tailWord_5580191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580191).length < 2 ^ (prefixWord ++ tailWord_5580191).sum := by decide
  have hdescent : baseEnd_5580191 < baseStart_5580191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580194 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_5580194 : Nat := 118140960795 + 5580194 * 2 ^ 59
def prefixEnd_5580194 : Nat := 4983230072969 + 3 ^ 40 * 5580194 * 2
def baseEnd_5580194 : Nat := 2865321667335245699012161

theorem tailTrace_5580194 : CollatzResearch.WordTrace tailWord_5580194 prefixEnd_5580194 2865321667335245699012161 := by
  unfold tailWord_5580194
  simp only [CollatzResearch.WordTrace]
  refine ⟨50881598886479408526602909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135684263697278422737607757 50881598886479408526602909)
  ·
    refine ⟨19080599582429778197476091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50881598886479408526602909 19080599582429778197476091)
    ·
      refine ⟨28620899373644667296214137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19080599582429778197476091 28620899373644667296214137)
      ·
        refine ⟨21465674530233500472160603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28620899373644667296214137 21465674530233500472160603)
        ·
          refine ⟨32198511795350250708240905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21465674530233500472160603 32198511795350250708240905)
          ·
            refine ⟨24148883846512688031180679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32198511795350250708240905 24148883846512688031180679)
            ·
              refine ⟨36223325769769032046771019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24148883846512688031180679 36223325769769032046771019)
              ·
                refine ⟨54334988654653548070156529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36223325769769032046771019 54334988654653548070156529)
                ·
                  refine ⟨40751241490990161052617397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54334988654653548070156529 40751241490990161052617397)
                  ·
                    refine ⟨3820428889780327598682881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40751241490990161052617397 3820428889780327598682881)
                    ·
                      refine ⟨2865321667335245699012161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820428889780327598682881 2865321667335245699012161)
                      ·
                        rfl

theorem cell23_5580194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_5580194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580194 prefixEnd_5580194 := by exact prefixLift 5580194
  have htrace : WordTrace (prefixWord ++ tailWord_5580194) baseStart_5580194 baseEnd_5580194 := by
    simpa [prefixWord, tailWord_5580194, baseEnd_5580194] using wordTrace_append hprefix tailTrace_5580194
  have hstable : (prefixWord ++ tailWord_5580194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580194).length < 2 ^ (prefixWord ++ tailWord_5580194).sum := by decide
  have hdescent : baseEnd_5580194 < baseStart_5580194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580264 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 6]
def baseStart_5580264 : Nat := 118140960795 + 5580264 * 2 ^ 59
def prefixEnd_5580264 : Nat := 4983230072969 + 3 ^ 40 * 5580264 * 2
def baseEnd_5580264 : Nat := 318373067886784491681871

theorem tailTrace_5580264 : CollatzResearch.WordTrace tailWord_5580264 prefixEnd_5580264 318373067886784491681871 := by
  unfold tailWord_5580264
  simp only [CollatzResearch.WordTrace]
  refine ⟨101764474327832018030729923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135685965770442690707639897 101764474327832018030729923)
  ·
    refine ⟨152646711491748027046094885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101764474327832018030729923 152646711491748027046094885)
    ·
      refine ⟨28621258404702755071142791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152646711491748027046094885 28621258404702755071142791)
      ·
        refine ⟨42931887607054132606714187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28621258404702755071142791 42931887607054132606714187)
        ·
          refine ⟨64397831410581198910071281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42931887607054132606714187 64397831410581198910071281)
          ·
            refine ⟨48298373557935899182553461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64397831410581198910071281 48298373557935899182553461)
            ·
              refine ⟨4527972521056490548364387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48298373557935899182553461 4527972521056490548364387)
              ·
                refine ⟨6791958781584735822546581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4527972521056490548364387 6791958781584735822546581)
                ·
                  refine ⟨318373067886784491681871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6791958781584735822546581 318373067886784491681871)
                  ·
                    rfl

theorem cell23_5580264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 6].length) (baseStart_5580264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580264 prefixEnd_5580264 := by exact prefixLift 5580264
  have htrace : WordTrace (prefixWord ++ tailWord_5580264) baseStart_5580264 baseEnd_5580264 := by
    simpa [prefixWord, tailWord_5580264, baseEnd_5580264] using wordTrace_append hprefix tailTrace_5580264
  have hstable : (prefixWord ++ tailWord_5580264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580264).length < 2 ^ (prefixWord ++ tailWord_5580264).sum := by decide
  have hdescent : baseEnd_5580264 < baseStart_5580264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580284 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 1, 5, 2]
def baseStart_5580284 : Nat := 118140960795 + 5580284 * 2 ^ 59
def prefixEnd_5580284 : Nat := 4983230072969 + 3 ^ 40 * 5580284 * 2
def baseEnd_5580284 : Nat := 2865367880594150346886747

theorem tailTrace_5580284 : CollatzResearch.WordTrace tailWord_5580284 prefixEnd_5580284 2865367880594150346886747 := by
  unfold tailWord_5580284
  simp only [CollatzResearch.WordTrace]
  refine ⟨101764839057795789738593953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135686452077061052984791937 101764839057795789738593953)
  ·
    refine ⟨76323629293346842303945465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101764839057795789738593953 76323629293346842303945465)
    ·
      refine ⟨57242721970010131727959099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76323629293346842303945465 57242721970010131727959099)
      ·
        refine ⟨85864082955015197591938649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57242721970010131727959099 85864082955015197591938649)
        ·
          refine ⟨64398062216261398193953987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85864082955015197591938649 64398062216261398193953987)
          ·
            refine ⟨96597093324392097290930981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64398062216261398193953987 96597093324392097290930981)
            ·
              refine ⟨18111954998323518242049559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96597093324392097290930981 18111954998323518242049559)
              ·
                refine ⟨27167932497485277363074339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18111954998323518242049559 27167932497485277363074339)
                ·
                  refine ⟨40751898746227916044611509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27167932497485277363074339 40751898746227916044611509)
                  ·
                    refine ⟨3820490507458867129182329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40751898746227916044611509 3820490507458867129182329)
                    ·
                      refine ⟨2865367880594150346886747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820490507458867129182329 2865367880594150346886747)
                      ·
                        rfl

theorem cell23_5580284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_5580284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580284 prefixEnd_5580284 := by exact prefixLift 5580284
  have htrace : WordTrace (prefixWord ++ tailWord_5580284) baseStart_5580284 baseEnd_5580284 := by
    simpa [prefixWord, tailWord_5580284, baseEnd_5580284] using wordTrace_append hprefix tailTrace_5580284
  have hstable : (prefixWord ++ tailWord_5580284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580284).length < 2 ^ (prefixWord ++ tailWord_5580284).sum := by decide
  have hdescent : baseEnd_5580284 < baseStart_5580284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580291 : List Nat := [1, 1, 1, 3, 2, 1, 2, 7, 1, 1, 3]
def baseStart_5580291 : Nat := 118140960795 + 5580291 * 2 ^ 59
def prefixEnd_5580291 : Nat := 4983230072969 + 3 ^ 40 * 5580291 * 2
def baseEnd_5580291 : Nat := 2865371474958731819499215

theorem tailTrace_5580291 : CollatzResearch.WordTrace tailWord_5580291 prefixEnd_5580291 2865371474958731819499215 := by
  unfold tailWord_5580291
  simp only [CollatzResearch.WordTrace]
  refine ⟨203529933426566219672692727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135686622284377479781795151 203529933426566219672692727)
  ·
    refine ⟨305294900139849329509039091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203529933426566219672692727 305294900139849329509039091)
    ·
      refine ⟨457942350209773994263558637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305294900139849329509039091 457942350209773994263558637)
      ·
        refine ⟨171728381328665247848834489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 457942350209773994263558637 171728381328665247848834489)
        ·
          refine ⟨128796285996498935886625867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171728381328665247848834489 128796285996498935886625867)
          ·
            refine ⟨193194428994748403829938801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128796285996498935886625867 193194428994748403829938801)
            ·
              refine ⟨144895821746061302872454101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193194428994748403829938801 144895821746061302872454101)
              ·
                refine ⟨3395995822173311786073143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 144895821746061302872454101 3395995822173311786073143)
                ·
                  refine ⟨5093993733259967679109715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3395995822173311786073143 5093993733259967679109715)
                  ·
                    refine ⟨7640990599889951518664573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5093993733259967679109715 7640990599889951518664573)
                    ·
                      refine ⟨2865371474958731819499215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7640990599889951518664573 2865371474958731819499215)
                      ·
                        rfl

theorem cell23_5580291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 1, 1, 3].length) (baseStart_5580291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580291 prefixEnd_5580291 := by exact prefixLift 5580291
  have htrace : WordTrace (prefixWord ++ tailWord_5580291) baseStart_5580291 baseEnd_5580291 := by
    simpa [prefixWord, tailWord_5580291, baseEnd_5580291] using wordTrace_append hprefix tailTrace_5580291
  have hstable : (prefixWord ++ tailWord_5580291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580291).length < 2 ^ (prefixWord ++ tailWord_5580291).sum := by decide
  have hdescent : baseEnd_5580291 < baseStart_5580291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580328 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 1, 5]
def baseStart_5580328 : Nat := 118140960795 + 5580328 * 2 ^ 59
def prefixEnd_5580328 : Nat := 4983230072969 + 3 ^ 40 * 5580328 * 2
def baseEnd_5580328 : Nat := 955130157914316058245515

theorem tailTrace_5580328 : CollatzResearch.WordTrace tailWord_5580328 prefixEnd_5580328 955130157914316058245515 := by
  unfold tailWord_5580328
  simp only [CollatzResearch.WordTrace]
  refine ⟨101765641463716087495894819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135687521951621449994526425 101765641463716087495894819)
  ·
    refine ⟨152648462195574131243842229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101765641463716087495894819 152648462195574131243842229)
    ·
      refine ⟨14310793330835074804110209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152648462195574131243842229 14310793330835074804110209)
      ·
        refine ⟨10733094998126306103082657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14310793330835074804110209 10733094998126306103082657)
        ·
          refine ⟨8049821248594729577311993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10733094998126306103082657 8049821248594729577311993)
          ·
            refine ⟨6037365936446047182983995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8049821248594729577311993 6037365936446047182983995)
            ·
              refine ⟨9056048904669070774475993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6037365936446047182983995 9056048904669070774475993)
              ·
                refine ⟨6792036678501803080856995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9056048904669070774475993 6792036678501803080856995)
                ·
                  refine ⟨10188055017752704621285493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6792036678501803080856995 10188055017752704621285493)
                  ·
                    refine ⟨955130157914316058245515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10188055017752704621285493 955130157914316058245515)
                    ·
                      rfl

theorem cell23_5580328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_5580328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580328 prefixEnd_5580328 := by exact prefixLift 5580328
  have htrace : WordTrace (prefixWord ++ tailWord_5580328) baseStart_5580328 baseEnd_5580328 := by
    simpa [prefixWord, tailWord_5580328, baseEnd_5580328] using wordTrace_append hprefix tailTrace_5580328
  have hstable : (prefixWord ++ tailWord_5580328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580328).length < 2 ^ (prefixWord ++ tailWord_5580328).sum := by decide
  have hdescent : baseEnd_5580328 < baseStart_5580328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580344 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_5580344 : Nat := 118140960795 + 5580344 * 2 ^ 59
def prefixEnd_5580344 : Nat := 4983230072969 + 3 ^ 40 * 5580344 * 2
def baseEnd_5580344 : Nat := 2865398689433420112136471

theorem tailTrace_5580344 : CollatzResearch.WordTrace tailWord_5580344 prefixEnd_5580344 2865398689433420112136471 := by
  unfold tailWord_5580344
  simp only [CollatzResearch.WordTrace]
  refine ⟨101765933247687104862186043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135687910996916139816248057 101765933247687104862186043)
  ·
    refine ⟨152648899871530657293279065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101765933247687104862186043 152648899871530657293279065)
    ·
      refine ⟨114486674903647992969959299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152648899871530657293279065 114486674903647992969959299)
      ·
        refine ⟨171730012355471989454938949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114486674903647992969959299 171730012355471989454938949)
        ·
          refine ⟨32199377316650998022801053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171730012355471989454938949 32199377316650998022801053)
          ·
            refine ⟨12074766493744124258550395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32199377316650998022801053 12074766493744124258550395)
            ·
              refine ⟨18112149740616186387825593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12074766493744124258550395 18112149740616186387825593)
              ·
                refine ⟨13584112305462139790869195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18112149740616186387825593 13584112305462139790869195)
                ·
                  refine ⟨20376168458193209686303793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13584112305462139790869195 20376168458193209686303793)
                  ·
                    refine ⟨15282126343644907264727845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20376168458193209686303793 15282126343644907264727845)
                    ·
                      refine ⟨2865398689433420112136471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15282126343644907264727845 2865398689433420112136471)
                      ·
                        rfl

theorem cell23_5580344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_5580344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580344 prefixEnd_5580344 := by exact prefixLift 5580344
  have htrace : WordTrace (prefixWord ++ tailWord_5580344) baseStart_5580344 baseEnd_5580344 := by
    simpa [prefixWord, tailWord_5580344, baseEnd_5580344] using wordTrace_append hprefix tailTrace_5580344
  have hstable : (prefixWord ++ tailWord_5580344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580344).length < 2 ^ (prefixWord ++ tailWord_5580344).sum := by decide
  have hdescent : baseEnd_5580344 < baseStart_5580344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580348 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 1, 1, 4]
def baseStart_5580348 : Nat := 118140960795 + 5580348 * 2 ^ 59
def prefixEnd_5580348 : Nat := 4983230072969 + 3 ^ 40 * 5580348 * 2
def baseEnd_5580348 : Nat := 2865400743356038096486453

theorem tailTrace_5580348 : CollatzResearch.WordTrace tailWord_5580348 prefixEnd_5580348 2865400743356038096486453 := by
  unfold tailWord_5580348
  simp only [CollatzResearch.WordTrace]
  refine ⟨101766006193679859203758849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135688008258239812271678465 101766006193679859203758849)
  ·
    refine ⟨76324504645259894402819137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101766006193679859203758849 76324504645259894402819137)
    ·
      refine ⟨57243378483944920802114353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76324504645259894402819137 57243378483944920802114353)
      ·
        refine ⟨42932533862958690601585765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57243378483944920802114353 42932533862958690601585765)
        ·
          refine ⟨8049850099304754487797331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42932533862958690601585765 8049850099304754487797331)
          ·
            refine ⟨12074775148957131731695997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8049850099304754487797331 12074775148957131731695997)
            ·
              refine ⟨4528040680858924399385999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12074775148957131731695997 4528040680858924399385999)
              ·
                refine ⟨6792061021288386599078999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528040680858924399385999 6792061021288386599078999)
                ·
                  refine ⟨10188091531932579898618499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6792061021288386599078999 10188091531932579898618499)
                  ·
                    refine ⟨15282137297898869847927749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10188091531932579898618499 15282137297898869847927749)
                    ·
                      refine ⟨2865400743356038096486453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15282137297898869847927749 2865400743356038096486453)
                      ·
                        rfl

theorem cell23_5580348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_5580348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580348 prefixEnd_5580348 := by exact prefixLift 5580348
  have htrace : WordTrace (prefixWord ++ tailWord_5580348) baseStart_5580348 baseEnd_5580348 := by
    simpa [prefixWord, tailWord_5580348, baseEnd_5580348] using wordTrace_append hprefix tailTrace_5580348
  have hstable : (prefixWord ++ tailWord_5580348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580348).length < 2 ^ (prefixWord ++ tailWord_5580348).sum := by decide
  have hdescent : baseEnd_5580348 < baseStart_5580348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580391 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_5580391 : Nat := 118140960795 + 5580391 * 2 ^ 59
def prefixEnd_5580391 : Nat := 4983230072969 + 3 ^ 40 * 5580391 * 2
def baseEnd_5580391 : Nat := 2865422823024181428248755

theorem tailTrace_5580391 : CollatzResearch.WordTrace tailWord_5580391 prefixEnd_5580391 2865422823024181428248755 := by
  unfold tailWord_5580391
  simp only [CollatzResearch.WordTrace]
  refine ⟨203533580726203936751333027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135689053817469291167555351 203533580726203936751333027)
  ·
    refine ⟨305300371089305905126999541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203533580726203936751333027 305300371089305905126999541)
    ·
      refine ⟨28621909789622428605656207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 305300371089305905126999541 28621909789622428605656207)
      ·
        refine ⟨42932864684433642908484311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28621909789622428605656207 42932864684433642908484311)
        ·
          refine ⟨64399297026650464362726467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42932864684433642908484311 64399297026650464362726467)
          ·
            refine ⟨96598945539975696544089701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64399297026650464362726467 96598945539975696544089701)
            ·
              refine ⟨18112302288745443102016819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96598945539975696544089701 18112302288745443102016819)
              ·
                refine ⟨27168453433118164653025229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18112302288745443102016819 27168453433118164653025229)
                ·
                  refine ⟨10188170037419311744884461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27168453433118164653025229 10188170037419311744884461)
                  ·
                    refine ⟨3820563764032241904331673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10188170037419311744884461 3820563764032241904331673)
                    ·
                      refine ⟨2865422823024181428248755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820563764032241904331673 2865422823024181428248755)
                      ·
                        rfl

theorem cell23_5580391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_5580391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580391 prefixEnd_5580391 := by exact prefixLift 5580391
  have htrace : WordTrace (prefixWord ++ tailWord_5580391) baseStart_5580391 baseEnd_5580391 := by
    simpa [prefixWord, tailWord_5580391, baseEnd_5580391] using wordTrace_append hprefix tailTrace_5580391
  have hstable : (prefixWord ++ tailWord_5580391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580391).length < 2 ^ (prefixWord ++ tailWord_5580391).sum := by decide
  have hdescent : baseEnd_5580391 < baseStart_5580391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580407 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_5580407 : Nat := 118140960795 + 5580407 * 2 ^ 59
def prefixEnd_5580407 : Nat := 4983230072969 + 3 ^ 40 * 5580407 * 2
def baseEnd_5580407 : Nat := 2865431038714653365648681

theorem tailTrace_5580407 : CollatzResearch.WordTrace tailWord_5580407 prefixEnd_5580407 2865431038714653365648681 := by
  unfold tailWord_5580407
  simp only [CollatzResearch.WordTrace]
  refine ⟨203534164294145971483915475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135689442862763980989276983 203534164294145971483915475)
  ·
    refine ⟨305301246441218957225873213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203534164294145971483915475 305301246441218957225873213)
    ·
      refine ⟨114487967415457108959702455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305301246441218957225873213 114487967415457108959702455)
      ·
        refine ⟨171731951123185663439553683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114487967415457108959702455 171731951123185663439553683)
        ·
          refine ⟨257597926684778495159330525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171731951123185663439553683 257597926684778495159330525)
          ·
            refine ⟨96599222506791935684748947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257597926684778495159330525 96599222506791935684748947)
            ·
              refine ⟨144898833760187903527123421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96599222506791935684748947 144898833760187903527123421)
              ·
                refine ⟨54337062660070463822671283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144898833760187903527123421 54337062660070463822671283)
                ·
                  refine ⟨81505593990105695734006925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54337062660070463822671283 81505593990105695734006925)
                  ·
                    refine ⟨30564597746289635900252597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81505593990105695734006925 30564597746289635900252597)
                    ·
                      refine ⟨2865431038714653365648681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30564597746289635900252597 2865431038714653365648681)
                      ·
                        rfl

theorem cell23_5580407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_5580407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580407 prefixEnd_5580407 := by exact prefixLift 5580407
  have htrace : WordTrace (prefixWord ++ tailWord_5580407) baseStart_5580407 baseEnd_5580407 := by
    simpa [prefixWord, tailWord_5580407, baseEnd_5580407] using wordTrace_append hprefix tailTrace_5580407
  have hstable : (prefixWord ++ tailWord_5580407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580407).length < 2 ^ (prefixWord ++ tailWord_5580407).sum := by decide
  have hdescent : baseEnd_5580407 < baseStart_5580407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580437 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_5580437 : Nat := 118140960795 + 5580437 * 2 ^ 59
def prefixEnd_5580437 : Nat := 4983230072969 + 3 ^ 40 * 5580437 * 2
def baseEnd_5580437 : Nat := 2865446443134288248273543

theorem tailTrace_5580437 : CollatzResearch.WordTrace tailWord_5580437 prefixEnd_5580437 2865446443134288248273543 := by
  unfold tailWord_5580437
  simp only [CollatzResearch.WordTrace]
  refine ⟨203535258484037286607507565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135690172322691524405005043 203535258484037286607507565)
  ·
    refine ⟨76325721931513982477815337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203535258484037286607507565 76325721931513982477815337)
    ·
      refine ⟨57244291448635486858361503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76325721931513982477815337 57244291448635486858361503)
      ·
        refine ⟨85866437172953230287542255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57244291448635486858361503 85866437172953230287542255)
        ·
          refine ⟨128799655759429845431313383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85866437172953230287542255 128799655759429845431313383)
          ·
            refine ⟨193199483639144768146970075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128799655759429845431313383 193199483639144768146970075)
            ·
              refine ⟨289799225458717152220455113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193199483639144768146970075 289799225458717152220455113)
              ·
                refine ⟨217349419094037864165341335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289799225458717152220455113 217349419094037864165341335)
                ·
                  refine ⟨326024128641056796248012003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217349419094037864165341335 326024128641056796248012003)
                  ·
                    refine ⟨489036192961585194372018005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326024128641056796248012003 489036192961585194372018005)
                    ·
                      refine ⟨2865446443134288248273543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 489036192961585194372018005 2865446443134288248273543)
                      ·
                        rfl

theorem cell23_5580437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_5580437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580437 prefixEnd_5580437 := by exact prefixLift 5580437
  have htrace : WordTrace (prefixWord ++ tailWord_5580437) baseStart_5580437 baseEnd_5580437 := by
    simpa [prefixWord, tailWord_5580437, baseEnd_5580437] using wordTrace_append hprefix tailTrace_5580437
  have hstable : (prefixWord ++ tailWord_5580437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580437).length < 2 ^ (prefixWord ++ tailWord_5580437).sum := by decide
  have hdescent : baseEnd_5580437 < baseStart_5580437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580457 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 5, 7]
def baseStart_5580457 : Nat := 118140960795 + 5580457 * 2 ^ 59
def prefixEnd_5580457 : Nat := 4983230072969 + 3 ^ 40 * 5580457 * 2
def baseEnd_5580457 : Nat := 955152237582459390007817

theorem tailTrace_5580457 : CollatzResearch.WordTrace tailWord_5580457 prefixEnd_5580457 955152237582459390007817 := by
  unfold tailWord_5580457
  simp only [CollatzResearch.WordTrace]
  refine ⟨203535987943964830023235625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135690658629309886682157083 203535987943964830023235625)
  ·
    refine ⟨152651990957973622517426719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203535987943964830023235625 152651990957973622517426719)
    ·
      refine ⟨228977986436960433776140079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152651990957973622517426719 228977986436960433776140079)
      ·
        refine ⟨343466979655440650664210119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228977986436960433776140079 343466979655440650664210119)
        ·
          refine ⟨515200469483160975996315179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343466979655440650664210119 515200469483160975996315179)
          ·
            refine ⟨772800704224741463994472769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515200469483160975996315179 772800704224741463994472769)
            ·
              refine ⟨579600528168556097995854577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 772800704224741463994472769 579600528168556097995854577)
              ·
                refine ⟨434700396126417073496890933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 579600528168556097995854577 434700396126417073496890933)
                ·
                  refine ⟨40753162136851600640333525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 434700396126417073496890933 40753162136851600640333525)
                  ·
                    refine ⟨955152237582459390007817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40753162136851600640333525 955152237582459390007817)
                    ·
                      rfl

theorem cell23_5580457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_5580457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580457 prefixEnd_5580457 := by exact prefixLift 5580457
  have htrace : WordTrace (prefixWord ++ tailWord_5580457) baseStart_5580457 baseEnd_5580457 := by
    simpa [prefixWord, tailWord_5580457, baseEnd_5580457] using wordTrace_append hprefix tailTrace_5580457
  have hstable : (prefixWord ++ tailWord_5580457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580457).length < 2 ^ (prefixWord ++ tailWord_5580457).sum := by decide
  have hdescent : baseEnd_5580457 < baseStart_5580457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580474 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_5580474 : Nat := 118140960795 + 5580474 * 2 ^ 59
def prefixEnd_5580474 : Nat := 4983230072969 + 3 ^ 40 * 5580474 * 2
def baseEnd_5580474 : Nat := 955155147306168201170291

theorem tailTrace_5580474 : CollatzResearch.WordTrace tailWord_5580474 prefixEnd_5580474 955155147306168201170291 := by
  unfold tailWord_5580474
  simp only [CollatzResearch.WordTrace]
  refine ⟨50884151996225810481651119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135691071989935494617736317 50884151996225810481651119)
  ·
    refine ⟨76326227994338715722476679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50884151996225810481651119 76326227994338715722476679)
    ·
      refine ⟨114489341991508073583715019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76326227994338715722476679 114489341991508073583715019)
      ·
        refine ⟨171734012987262110375572529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114489341991508073583715019 171734012987262110375572529)
        ·
          refine ⟨128800509740446582781679397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171734012987262110375572529 128800509740446582781679397)
          ·
            refine ⟨24150095576333734271564887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128800509740446582781679397 24150095576333734271564887)
            ·
              refine ⟨36225143364500601407347331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24150095576333734271564887 36225143364500601407347331)
              ·
                refine ⟨54337715046750902111020997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36225143364500601407347331 54337715046750902111020997)
                ·
                  refine ⟨10188321571265794145816437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54337715046750902111020997 10188321571265794145816437)
                  ·
                    refine ⟨955155147306168201170291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10188321571265794145816437 955155147306168201170291)
                    ·
                      rfl

theorem cell23_5580474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_5580474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580474 prefixEnd_5580474 := by exact prefixLift 5580474
  have htrace : WordTrace (prefixWord ++ tailWord_5580474) baseStart_5580474 baseEnd_5580474 := by
    simpa [prefixWord, tailWord_5580474, baseEnd_5580474] using wordTrace_append hprefix tailTrace_5580474
  have hstable : (prefixWord ++ tailWord_5580474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580474).length < 2 ^ (prefixWord ++ tailWord_5580474).sum := by decide
  have hdescent : baseEnd_5580474 < baseStart_5580474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580511 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 4]
def baseStart_5580511 : Nat := 118140960795 + 5580511 * 2 ^ 59
def prefixEnd_5580511 : Nat := 4983230072969 + 3 ^ 40 * 5580511 * 2
def baseEnd_5580511 : Nat := 2865484440702720958748203

theorem tailTrace_5580511 : CollatzResearch.WordTrace tailWord_5580511 prefixEnd_5580511 2865484440702720958748203 := by
  unfold tailWord_5580511
  simp only [CollatzResearch.WordTrace]
  refine ⟨203537957485769197245701387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135691971657179464830467591 203537957485769197245701387)
  ·
    refine ⟨305306936228653795868552081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203537957485769197245701387 305306936228653795868552081)
    ·
      refine ⟨228980202171490346901414061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305306936228653795868552081 228980202171490346901414061)
      ·
        refine ⟨85867575814308880088030273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228980202171490346901414061 85867575814308880088030273)
        ·
          refine ⟨64400681860731660066022705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85867575814308880088030273 64400681860731660066022705)
          ·
            refine ⟨48300511395548745049517029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64400681860731660066022705 48300511395548745049517029)
            ·
              refine ⟨9056345886665389696784443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48300511395548745049517029 9056345886665389696784443)
              ·
                refine ⟨13584518829998084545176665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9056345886665389696784443 13584518829998084545176665)
                ·
                  refine ⟨10188389122498563408882499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13584518829998084545176665 10188389122498563408882499)
                  ·
                    refine ⟨15282583683747845113323749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10188389122498563408882499 15282583683747845113323749)
                    ·
                      refine ⟨2865484440702720958748203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15282583683747845113323749 2865484440702720958748203)
                      ·
                        rfl

theorem cell23_5580511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_5580511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580511 prefixEnd_5580511 := by exact prefixLift 5580511
  have htrace : WordTrace (prefixWord ++ tailWord_5580511) baseStart_5580511 baseEnd_5580511 := by
    simpa [prefixWord, tailWord_5580511, baseEnd_5580511] using wordTrace_append hprefix tailTrace_5580511
  have hstable : (prefixWord ++ tailWord_5580511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580511).length < 2 ^ (prefixWord ++ tailWord_5580511).sum := by decide
  have hdescent : baseEnd_5580511 < baseStart_5580511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580531 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 3]
def baseStart_5580531 : Nat := 118140960795 + 5580531 * 2 ^ 59
def prefixEnd_5580531 : Nat := 4983230072969 + 3 ^ 40 * 5580531 * 2
def baseEnd_5580531 : Nat := 2865494710315810880498111

theorem tailTrace_5580531 : CollatzResearch.WordTrace tailWord_5580531 prefixEnd_5580531 2865494710315810880498111 := by
  unfold tailWord_5580531
  simp only [CollatzResearch.WordTrace]
  refine ⟨203538686945696740661429447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135692457963797827107619631 203538686945696740661429447)
  ·
    refine ⟨305308030418545110992144171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203538686945696740661429447 305308030418545110992144171)
    ·
      refine ⟨457962045627817666488216257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305308030418545110992144171 457962045627817666488216257)
      ·
        refine ⟨343471534220863249866162193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457962045627817666488216257 343471534220863249866162193)
        ·
          refine ⟨257603650665647437399621645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343471534220863249866162193 257603650665647437399621645)
          ·
            refine ⟨96601368999617789024858117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257603650665647437399621645 96601368999617789024858117)
            ·
              refine ⟨18112756687428335442160897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96601368999617789024858117 18112756687428335442160897)
              ·
                refine ⟨13584567515571251581620673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18112756687428335442160897 13584567515571251581620673)
                ·
                  refine ⟨10188425636678438686215505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13584567515571251581620673 10188425636678438686215505)
                  ·
                    refine ⟨7641319227508829014661629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10188425636678438686215505 7641319227508829014661629)
                    ·
                      refine ⟨2865494710315810880498111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7641319227508829014661629 2865494710315810880498111)
                      ·
                        rfl

theorem cell23_5580531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 2, 2, 3].length) (baseStart_5580531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580531 prefixEnd_5580531 := by exact prefixLift 5580531
  have htrace : WordTrace (prefixWord ++ tailWord_5580531) baseStart_5580531 baseEnd_5580531 := by
    simpa [prefixWord, tailWord_5580531, baseEnd_5580531] using wordTrace_append hprefix tailTrace_5580531
  have hstable : (prefixWord ++ tailWord_5580531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580531).length < 2 ^ (prefixWord ++ tailWord_5580531).sum := by decide
  have hdescent : baseEnd_5580531 < baseStart_5580531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580571 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 1, 5, 2]
def baseStart_5580571 : Nat := 118140960795 + 5580571 * 2 ^ 59
def prefixEnd_5580571 : Nat := 4983230072969 + 3 ^ 40 * 5580571 * 2
def baseEnd_5580571 : Nat := 2865515249541990723997927

theorem tailTrace_5580571 : CollatzResearch.WordTrace tailWord_5580571 prefixEnd_5580571 2865515249541990723997927 := by
  unfold tailWord_5580571
  simp only [CollatzResearch.WordTrace]
  refine ⟨203540145865551827492885567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135693430577034551661923711 203540145865551827492885567)
  ·
    refine ⟨305310218798327741239328351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203540145865551827492885567 305310218798327741239328351)
    ·
      refine ⟨457965328197491611858992527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305310218798327741239328351 457965328197491611858992527)
      ·
        refine ⟨686947992296237417788488791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457965328197491611858992527 686947992296237417788488791)
        ·
          refine ⟨1030421988444356126682733187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686947992296237417788488791 1030421988444356126682733187)
          ·
            refine ⟨1545632982666534190024099781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030421988444356126682733187 1545632982666534190024099781)
            ·
              refine ⟨289806184249975160629518709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1545632982666534190024099781 289806184249975160629518709)
              ·
                refine ⟨27169329773435171309017379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 289806184249975160629518709 27169329773435171309017379)
                ·
                  refine ⟨40753994660152756963526069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27169329773435171309017379 40753994660152756963526069)
                  ·
                    refine ⟨3820686999389320965330569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40753994660152756963526069 3820686999389320965330569)
                    ·
                      refine ⟨2865515249541990723997927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820686999389320965330569 2865515249541990723997927)
                      ·
                        rfl

theorem cell23_5580571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 5, 2].length) (baseStart_5580571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580571 prefixEnd_5580571 := by exact prefixLift 5580571
  have htrace : WordTrace (prefixWord ++ tailWord_5580571) baseStart_5580571 baseEnd_5580571 := by
    simpa [prefixWord, tailWord_5580571, baseEnd_5580571] using wordTrace_append hprefix tailTrace_5580571
  have hstable : (prefixWord ++ tailWord_5580571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580571).length < 2 ^ (prefixWord ++ tailWord_5580571).sum := by decide
  have hdescent : baseEnd_5580571 < baseStart_5580571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580578 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_5580578 : Nat := 118140960795 + 5580578 * 2 ^ 59
def prefixEnd_5580578 : Nat := 4983230072969 + 3 ^ 40 * 5580578 * 2
def baseEnd_5580578 : Nat := 2865518843906572196610395

theorem tailTrace_5580578 : CollatzResearch.WordTrace tailWord_5580578 prefixEnd_5580578 2865518843906572196610395 := by
  unfold tailWord_5580578
  simp only [CollatzResearch.WordTrace]
  refine ⟨50885100294131616922097597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135693600784350978458926925 50885100294131616922097597)
  ·
    refine ⟨19081912610299356345786599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50885100294131616922097597 19081912610299356345786599)
    ·
      refine ⟨28622868915449034518679899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19081912610299356345786599 28622868915449034518679899)
      ·
        refine ⟨42934303373173551778019849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28622868915449034518679899 42934303373173551778019849)
        ·
          refine ⟨32200727529880163833514887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42934303373173551778019849 32200727529880163833514887)
          ·
            refine ⟨48301091294820245750272331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32200727529880163833514887 48301091294820245750272331)
            ·
              refine ⟨72451636942230368625408497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48301091294820245750272331 72451636942230368625408497)
              ·
                refine ⟨54338727706672776469056373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72451636942230368625408497 54338727706672776469056373)
                ·
                  refine ⟨5094255722500572793974035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54338727706672776469056373 5094255722500572793974035)
                  ·
                    refine ⟨7641383583750859190961053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5094255722500572793974035 7641383583750859190961053)
                    ·
                      refine ⟨2865518843906572196610395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7641383583750859190961053 2865518843906572196610395)
                      ·
                        rfl

theorem cell23_5580578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_5580578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580578 prefixEnd_5580578 := by exact prefixLift 5580578
  have htrace : WordTrace (prefixWord ++ tailWord_5580578) baseStart_5580578 baseEnd_5580578 := by
    simpa [prefixWord, tailWord_5580578, baseEnd_5580578] using wordTrace_append hprefix tailTrace_5580578
  have hstable : (prefixWord ++ tailWord_5580578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580578).length < 2 ^ (prefixWord ++ tailWord_5580578).sum := by decide
  have hdescent : baseEnd_5580578 < baseStart_5580578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580595 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 3, 1, 3]
def baseStart_5580595 : Nat := 118140960795 + 5580595 * 2 ^ 59
def prefixEnd_5580595 : Nat := 4983230072969 + 3 ^ 40 * 5580595 * 2
def baseEnd_5580595 : Nat := 2865527573077698630097817

theorem tailTrace_5580595 : CollatzResearch.WordTrace tailWord_5580595 prefixEnd_5580595 2865527573077698630097817 := by
  unfold tailWord_5580595
  simp only [CollatzResearch.WordTrace]
  refine ⟨203541021217464879591759239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135694014144976586394506159 203541021217464879591759239)
  ·
    refine ⟨305311531826197319387638859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203541021217464879591759239 305311531826197319387638859)
    ·
      refine ⟨457967297739295979081458289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305311531826197319387638859 457967297739295979081458289)
      ·
        refine ⟨343475473304471984311093717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 457967297739295979081458289 343475473304471984311093717)
        ·
          refine ⟨8050206405573562132291259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 343475473304471984311093717 8050206405573562132291259)
          ·
            refine ⟨12075309608360343198436889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8050206405573562132291259 12075309608360343198436889)
            ·
              refine ⟨9056482206270257398827667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12075309608360343198436889 9056482206270257398827667)
              ·
                refine ⟨13584723309405386098241501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9056482206270257398827667 13584723309405386098241501)
                ·
                  refine ⟨5094271241027019786840563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13584723309405386098241501 5094271241027019786840563)
                  ·
                    refine ⟨7641406861540529680260845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5094271241027019786840563 7641406861540529680260845)
                    ·
                      refine ⟨2865527573077698630097817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7641406861540529680260845 2865527573077698630097817)
                      ·
                        rfl

theorem cell23_5580595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 1, 3].length) (baseStart_5580595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580595 prefixEnd_5580595 := by exact prefixLift 5580595
  have htrace : WordTrace (prefixWord ++ tailWord_5580595) baseStart_5580595 baseEnd_5580595 := by
    simpa [prefixWord, tailWord_5580595, baseEnd_5580595] using wordTrace_append hprefix tailTrace_5580595
  have hstable : (prefixWord ++ tailWord_5580595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580595).length < 2 ^ (prefixWord ++ tailWord_5580595).sum := by decide
  have hdescent : baseEnd_5580595 < baseStart_5580595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580611 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 1, 6]
def baseStart_5580611 : Nat := 118140960795 + 5580611 * 2 ^ 59
def prefixEnd_5580611 : Nat := 4983230072969 + 3 ^ 40 * 5580611 * 2
def baseEnd_5580611 : Nat := 955178596256056855832581

theorem tailTrace_5580611 : CollatzResearch.WordTrace tailWord_5580611 prefixEnd_5580611 955178596256056855832581 := by
  unfold tailWord_5580611
  simp only [CollatzResearch.WordTrace]
  refine ⟨203541604785406914324341687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135694403190271276216227791 203541604785406914324341687)
  ·
    refine ⟨305312407178110371486512531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203541604785406914324341687 305312407178110371486512531)
    ·
      refine ⟨457968610767165557229768797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305312407178110371486512531 457968610767165557229768797)
      ·
        refine ⟨171738229037687083961163299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 457968610767165557229768797 171738229037687083961163299)
        ·
          refine ⟨257607343556530625941744949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171738229037687083961163299 257607343556530625941744949)
          ·
            refine ⟨24150688458424746182038589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 257607343556530625941744949 24150688458424746182038589)
            ·
              refine ⟨9056508171909279818264471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24150688458424746182038589 9056508171909279818264471)
              ·
                refine ⟨13584762257863919727396707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9056508171909279818264471 13584762257863919727396707)
                ·
                  refine ⟨20377143386795879591095061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13584762257863919727396707 20377143386795879591095061)
                  ·
                    refine ⟨955178596256056855832581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20377143386795879591095061 955178596256056855832581)
                    ·
                      rfl

theorem cell23_5580611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 6].length) (baseStart_5580611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580611 prefixEnd_5580611 := by exact prefixLift 5580611
  have htrace : WordTrace (prefixWord ++ tailWord_5580611) baseStart_5580611 baseEnd_5580611 := by
    simpa [prefixWord, tailWord_5580611, baseEnd_5580611] using wordTrace_append hprefix tailTrace_5580611
  have hstable : (prefixWord ++ tailWord_5580611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580611).length < 2 ^ (prefixWord ++ tailWord_5580611).sum := by decide
  have hdescent : baseEnd_5580611 < baseStart_5580611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580618 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_5580618 : Nat := 118140960795 + 5580618 * 2 ^ 59
def prefixEnd_5580618 : Nat := 4983230072969 + 3 ^ 40 * 5580618 * 2
def baseEnd_5580618 : Nat := 2865539383132752040110211

theorem tailTrace_5580618 : CollatzResearch.WordTrace tailWord_5580618 prefixEnd_5580618 2865539383132752040110211 := by
  unfold tailWord_5580618
  simp only [CollatzResearch.WordTrace]
  refine ⟨50885465024095388629961627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135694573397587703013231005 50885465024095388629961627)
  ·
    refine ⟨76328197536143082944942441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50885465024095388629961627 76328197536143082944942441)
    ·
      refine ⟨57246148152107312208706831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76328197536143082944942441 57246148152107312208706831)
      ·
        refine ⟨85869222228160968313060247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57246148152107312208706831 85869222228160968313060247)
        ·
          refine ⟨128803833342241452469590371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85869222228160968313060247 128803833342241452469590371)
          ·
            refine ⟨193205750013362178704385557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128803833342241452469590371 193205750013362178704385557)
            ·
              refine ⟨9056519531876352126768073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 193205750013362178704385557 9056519531876352126768073)
              ·
                refine ⟨6792389648907264095076055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9056519531876352126768073 6792389648907264095076055)
                ·
                  refine ⟨10188584473360896142614083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6792389648907264095076055 10188584473360896142614083)
                  ·
                    refine ⟨15282876710041344213921125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10188584473360896142614083 15282876710041344213921125)
                    ·
                      refine ⟨2865539383132752040110211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15282876710041344213921125 2865539383132752040110211)
                      ·
                        rfl

theorem cell23_5580618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_5580618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580618 prefixEnd_5580618 := by exact prefixLift 5580618
  have htrace : WordTrace (prefixWord ++ tailWord_5580618) baseStart_5580618 baseEnd_5580618 := by
    simpa [prefixWord, tailWord_5580618, baseEnd_5580618] using wordTrace_append hprefix tailTrace_5580618
  have hstable : (prefixWord ++ tailWord_5580618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580618).length < 2 ^ (prefixWord ++ tailWord_5580618).sum := by decide
  have hdescent : baseEnd_5580618 < baseStart_5580618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580628 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_5580628 : Nat := 118140960795 + 5580628 * 2 ^ 59
def prefixEnd_5580628 : Nat := 4983230072969 + 3 ^ 40 * 5580628 * 2
def baseEnd_5580628 : Nat := 955181505979765666995055

theorem tailTrace_5580628 : CollatzResearch.WordTrace tailWord_5580628 prefixEnd_5580628 955181505979765666995055 := by
  unfold tailWord_5580628
  simp only [CollatzResearch.WordTrace]
  refine ⟨101771112413172663113855269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135694816550896884151807025 101771112413172663113855269)
  ·
    refine ⟨19082083577469874333847863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101771112413172663113855269 19082083577469874333847863)
    ·
      refine ⟨28623125366204811500771795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19082083577469874333847863 28623125366204811500771795)
      ·
        refine ⟨42934688049307217251157693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28623125366204811500771795 42934688049307217251157693)
        ·
          refine ⟨16100508018490206469184135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42934688049307217251157693 16100508018490206469184135)
          ·
            refine ⟨24150762027735309703776203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16100508018490206469184135 24150762027735309703776203)
            ·
              refine ⟨36226143041602964555664305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24150762027735309703776203 36226143041602964555664305)
              ·
                refine ⟨27169607281202223416748229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36226143041602964555664305 27169607281202223416748229)
                ·
                  refine ⟨5094301365225416890640293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27169607281202223416748229 5094301365225416890640293)
                  ·
                    refine ⟨955181505979765666995055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5094301365225416890640293 955181505979765666995055)
                    ·
                      rfl

theorem cell23_5580628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_5580628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580628 prefixEnd_5580628 := by exact prefixLift 5580628
  have htrace : WordTrace (prefixWord ++ tailWord_5580628) baseStart_5580628 baseEnd_5580628 := by
    simpa [prefixWord, tailWord_5580628, baseEnd_5580628] using wordTrace_append hprefix tailTrace_5580628
  have hstable : (prefixWord ++ tailWord_5580628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580628).length < 2 ^ (prefixWord ++ tailWord_5580628).sum := by decide
  have hdescent : baseEnd_5580628 < baseStart_5580628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580652 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 3, 2, 2]
def baseStart_5580652 : Nat := 118140960795 + 5580652 * 2 ^ 59
def prefixEnd_5580652 : Nat := 4983230072969 + 3 ^ 40 * 5580652 * 2
def baseEnd_5580652 : Nat := 2865556841475004907085055

theorem tailTrace_5580652 : CollatzResearch.WordTrace tailWord_5580652 prefixEnd_5580652 2865556841475004907085055 := by
  unfold tailWord_5580652
  simp only [CollatzResearch.WordTrace]
  refine ⟨101771550089129189163292105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135695400118838918884389473 101771550089129189163292105)
  ·
    refine ⟨76328662566846891872469079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101771550089129189163292105 76328662566846891872469079)
    ·
      refine ⟨114492993850270337808703619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76328662566846891872469079 114492993850270337808703619)
      ·
        refine ⟨171739490775405506713055429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114492993850270337808703619 171739490775405506713055429)
        ·
          refine ⟨32201154520388532508697893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171739490775405506713055429 32201154520388532508697893)
          ·
            refine ⟨6037716472572849845380855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32201154520388532508697893 6037716472572849845380855)
            ·
              refine ⟨9056574708859274768071283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6037716472572849845380855 9056574708859274768071283)
              ·
                refine ⟨13584862063288912152106925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9056574708859274768071283 13584862063288912152106925)
                ·
                  refine ⟨5094323273733342057040097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13584862063288912152106925 5094323273733342057040097)
                  ·
                    refine ⟨3820742455300006542780073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5094323273733342057040097 3820742455300006542780073)
                    ·
                      refine ⟨2865556841475004907085055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820742455300006542780073 2865556841475004907085055)
                      ·
                        rfl

theorem cell23_5580652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 2, 2].length) (baseStart_5580652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580652 prefixEnd_5580652 := by exact prefixLift 5580652
  have htrace : WordTrace (prefixWord ++ tailWord_5580652) baseStart_5580652 baseEnd_5580652 := by
    simpa [prefixWord, tailWord_5580652, baseEnd_5580652] using wordTrace_append hprefix tailTrace_5580652
  have hstable : (prefixWord ++ tailWord_5580652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580652).length < 2 ^ (prefixWord ++ tailWord_5580652).sum := by decide
  have hdescent : baseEnd_5580652 < baseStart_5580652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580661 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5580661 : Nat := 118140960795 + 5580661 * 2 ^ 59
def prefixEnd_5580661 : Nat := 4983230072969 + 3 ^ 40 * 5580661 * 2
def baseEnd_5580661 : Nat := 2865561462800895371872513

theorem tailTrace_5580661 : CollatzResearch.WordTrace tailWord_5580661 prefixEnd_5580661 2865561462800895371872513 := by
  unfold tailWord_5580661
  simp only [CollatzResearch.WordTrace]
  refine ⟨203543428435225772863661837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135695618956817181909107891 203543428435225772863661837)
  ·
    refine ⟨76328785663209664823873189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203543428435225772863661837 76328785663209664823873189)
    ·
      refine ⟨14311647311851812154476223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76328785663209664823873189 14311647311851812154476223)
      ·
        refine ⟨21467470967777718231714335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14311647311851812154476223 21467470967777718231714335)
        ·
          refine ⟨32201206451666577347571503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21467470967777718231714335 32201206451666577347571503)
          ·
            refine ⟨48301809677499866021357255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32201206451666577347571503 48301809677499866021357255)
            ·
              refine ⟨72452714516249799032035883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48301809677499866021357255 72452714516249799032035883)
              ·
                refine ⟨108679071774374698548053825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72452714516249799032035883 108679071774374698548053825)
                ·
                  refine ⟨81509303830781023911040369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108679071774374698548053825 81509303830781023911040369)
                  ·
                    refine ⟨61131977873085767933280277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81509303830781023911040369 61131977873085767933280277)
                    ·
                      refine ⟨2865561462800895371872513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61131977873085767933280277 2865561462800895371872513)
                      ·
                        rfl

theorem cell23_5580661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5580661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580661 prefixEnd_5580661 := by exact prefixLift 5580661
  have htrace : WordTrace (prefixWord ++ tailWord_5580661) baseStart_5580661 baseEnd_5580661 := by
    simpa [prefixWord, tailWord_5580661, baseEnd_5580661] using wordTrace_append hprefix tailTrace_5580661
  have hstable : (prefixWord ++ tailWord_5580661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580661).length < 2 ^ (prefixWord ++ tailWord_5580661).sum := by decide
  have hdescent : baseEnd_5580661 < baseStart_5580661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580662 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_5580662 : Nat := 118140960795 + 5580662 * 2 ^ 59
def prefixEnd_5580662 : Nat := 4983230072969 + 3 ^ 40 * 5580662 * 2
def baseEnd_5580662 : Nat := 955187325427183289320003

theorem tailTrace_5580662 : CollatzResearch.WordTrace tailWord_5580662 prefixEnd_5580662 955187325427183289320003 := by
  unfold tailWord_5580662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12721466556763884377153015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135695643272148100022965493 12721466556763884377153015)
  ·
    refine ⟨19082199835145826565729523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12721466556763884377153015 19082199835145826565729523)
    ·
      refine ⟨28623299752718739848594285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19082199835145826565729523 28623299752718739848594285)
      ·
        refine ⟨10733737407269527443222857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28623299752718739848594285 10733737407269527443222857)
        ·
          refine ⟨8050303055452145582417143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10733737407269527443222857 8050303055452145582417143)
          ·
            refine ⟨12075454583178218373625715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8050303055452145582417143 12075454583178218373625715)
            ·
              refine ⟨18113181874767327560438573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12075454583178218373625715 18113181874767327560438573)
              ·
                refine ⟨6792443203037747835164465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18113181874767327560438573 6792443203037747835164465)
                ·
                  refine ⟨5094332402278310876373349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6792443203037747835164465 5094332402278310876373349)
                  ·
                    refine ⟨955187325427183289320003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5094332402278310876373349 955187325427183289320003)
                    ·
                      rfl

theorem cell23_5580662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_5580662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580662 prefixEnd_5580662 := by exact prefixLift 5580662
  have htrace : WordTrace (prefixWord ++ tailWord_5580662) baseStart_5580662 baseEnd_5580662 := by
    simpa [prefixWord, tailWord_5580662, baseEnd_5580662] using wordTrace_append hprefix tailTrace_5580662
  have hstable : (prefixWord ++ tailWord_5580662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580662).length < 2 ^ (prefixWord ++ tailWord_5580662).sum := by decide
  have hdescent : baseEnd_5580662 < baseStart_5580662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580703 : List Nat := [1, 1, 2, 5, 4, 1, 2, 2, 1, 2, 2]
def baseStart_5580703 : Nat := 118140960795 + 5580703 * 2 ^ 59
def prefixEnd_5580703 : Nat := 4983230072969 + 3 ^ 40 * 5580703 * 2
def baseEnd_5580703 : Nat := 2865583028988384207547321

theorem tailTrace_5580703 : CollatzResearch.WordTrace tailWord_5580703 prefixEnd_5580703 2865583028988384207547321 := by
  unfold tailWord_5580703
  simp only [CollatzResearch.WordTrace]
  refine ⟨203544960301073614036690763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135696640200715742691127175 203544960301073614036690763)
  ·
    refine ⟨305317440451610421055036145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203544960301073614036690763 305317440451610421055036145)
    ·
      refine ⟨228988080338707815791277109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305317440451610421055036145 228988080338707815791277109)
      ·
        refine ⟨21467632531753857730432229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228988080338707815791277109 21467632531753857730432229)
        ·
          refine ⟨4025181099703848324456043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21467632531753857730432229 4025181099703848324456043)
          ·
            refine ⟨6037771649555772486684065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025181099703848324456043 6037771649555772486684065)
            ·
              refine ⟨4528328737166829365013049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6037771649555772486684065 4528328737166829365013049)
              ·
                refine ⟨3396246552875122023759787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4528328737166829365013049 3396246552875122023759787)
                ·
                  refine ⟨5094369829312683035639681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396246552875122023759787 5094369829312683035639681)
                  ·
                    refine ⟨3820777371984512276729761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5094369829312683035639681 3820777371984512276729761)
                    ·
                      refine ⟨2865583028988384207547321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820777371984512276729761 2865583028988384207547321)
                      ·
                        rfl

theorem cell23_5580703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_5580703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580703 prefixEnd_5580703 := by exact prefixLift 5580703
  have htrace : WordTrace (prefixWord ++ tailWord_5580703) baseStart_5580703 baseEnd_5580703 := by
    simpa [prefixWord, tailWord_5580703, baseEnd_5580703] using wordTrace_append hprefix tailTrace_5580703
  have hstable : (prefixWord ++ tailWord_5580703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580703).length < 2 ^ (prefixWord ++ tailWord_5580703).sum := by decide
  have hdescent : baseEnd_5580703 < baseStart_5580703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580725 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_5580725 : Nat := 118140960795 + 5580725 * 2 ^ 59
def prefixEnd_5580725 : Nat := 4983230072969 + 3 ^ 40 * 5580725 * 2
def baseEnd_5580725 : Nat := 2865594325562783121472219

theorem tailTrace_5580725 : CollatzResearch.WordTrace tailWord_5580725 prefixEnd_5580725 2865594325562783121472219 := by
  unfold tailWord_5580725
  simp only [CollatzResearch.WordTrace]
  refine ⟨203545762706993911793991629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135697175137995941195994419 203545762706993911793991629)
  ·
    refine ⟨76329661015122716922746861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203545762706993911793991629 76329661015122716922746861)
    ·
      refine ⟨28623622880671018846030073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76329661015122716922746861 28623622880671018846030073)
      ·
        refine ⟨21467717160503264134522555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28623622880671018846030073 21467717160503264134522555)
        ·
          refine ⟨32201575740754896201783833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21467717160503264134522555 32201575740754896201783833)
          ·
            refine ⟨24151181805566172151337875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32201575740754896201783833 24151181805566172151337875)
            ·
              refine ⟨36226772708349258227006813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24151181805566172151337875 36226772708349258227006813)
              ·
                refine ⟨13585039765630971835127555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36226772708349258227006813 13585039765630971835127555)
                ·
                  refine ⟨20377559648446457752691333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13585039765630971835127555 20377559648446457752691333)
                  ·
                    refine ⟨3820792434083710828629625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20377559648446457752691333 3820792434083710828629625)
                    ·
                      refine ⟨2865594325562783121472219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820792434083710828629625 2865594325562783121472219)
                      ·
                        rfl

theorem cell23_5580725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_5580725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580725 prefixEnd_5580725 := by exact prefixLift 5580725
  have htrace : WordTrace (prefixWord ++ tailWord_5580725) baseStart_5580725 baseEnd_5580725 := by
    simpa [prefixWord, tailWord_5580725, baseEnd_5580725] using wordTrace_append hprefix tailTrace_5580725
  have hstable : (prefixWord ++ tailWord_5580725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580725).length < 2 ^ (prefixWord ++ tailWord_5580725).sum := by decide
  have hdescent : baseEnd_5580725 < baseStart_5580725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580765 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 7]
def baseStart_5580765 : Nat := 118140960795 + 5580765 * 2 ^ 59
def prefixEnd_5580765 : Nat := 4983230072969 + 3 ^ 40 * 5580765 * 2
def baseEnd_5580765 : Nat := 318401651643218107219115

theorem tailTrace_5580765 : CollatzResearch.WordTrace tailWord_5580765 prefixEnd_5580765 318401651643218107219115 := by
  unfold tailWord_5580765
  simp only [CollatzResearch.WordTrace]
  refine ⟨203547221626848998625447749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135698147751232665750298499 203547221626848998625447749)
  ·
    refine ⟨38165104055034187242271453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203547221626848998625447749 38165104055034187242271453)
    ·
      refine ⟨14311914020637820215851795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38165104055034187242271453 14311914020637820215851795)
      ·
        refine ⟨21467871030956730323777693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14311914020637820215851795 21467871030956730323777693)
        ·
          refine ⟨8050451636608773871416635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21467871030956730323777693 8050451636608773871416635)
          ·
            refine ⟨12075677454913160807124953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8050451636608773871416635 12075677454913160807124953)
            ·
              refine ⟨9056758091184870605343715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12075677454913160807124953 9056758091184870605343715)
              ·
                refine ⟨13585137136777305908015573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9056758091184870605343715 13585137136777305908015573)
                ·
                  refine ⟨318401651643218107219115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13585137136777305908015573 318401651643218107219115)
                  ·
                    rfl

theorem cell23_5580765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_5580765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580765 prefixEnd_5580765 := by exact prefixLift 5580765
  have htrace : WordTrace (prefixWord ++ tailWord_5580765) baseStart_5580765 baseEnd_5580765 := by
    simpa [prefixWord, tailWord_5580765, baseEnd_5580765] using wordTrace_append hprefix tailTrace_5580765
  have hstable : (prefixWord ++ tailWord_5580765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580765).length < 2 ^ (prefixWord ++ tailWord_5580765).sum := by decide
  have hdescent : baseEnd_5580765 < baseStart_5580765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580768 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 1, 7, 2]
def baseStart_5580768 : Nat := 118140960795 + 5580768 * 2 ^ 59
def prefixEnd_5580768 : Nat := 4983230072969 + 3 ^ 40 * 5580768 * 2
def baseEnd_5580768 : Nat := 2865616405230926453234521

theorem tailTrace_5580768 : CollatzResearch.WordTrace tailWord_5580768 prefixEnd_5580768 2865616405230926453234521 := by
  unfold tailWord_5580768
  simp only [CollatzResearch.WordTrace]
  refine ⟨101773665522919065068903479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135698220697225420091871305 101773665522919065068903479)
  ·
    refine ⟨152660498284378597603355219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101773665522919065068903479 152660498284378597603355219)
    ·
      refine ⟨228990747426567896405032829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152660498284378597603355219 228990747426567896405032829)
      ·
        refine ⟨85871530284962961151887311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228990747426567896405032829 85871530284962961151887311)
        ·
          refine ⟨128807295427444441727830967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85871530284962961151887311 128807295427444441727830967)
          ·
            refine ⟨193210943141166662591746451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128807295427444441727830967 193210943141166662591746451)
            ·
              refine ⟨289816414711749993887619677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193210943141166662591746451 289816414711749993887619677)
              ·
                refine ⟨108681155516906247707857379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289816414711749993887619677 108681155516906247707857379)
                ·
                  refine ⟨163021733275359371561786069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108681155516906247707857379 163021733275359371561786069)
                  ·
                    refine ⟨3820821873641235270979361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 163021733275359371561786069 3820821873641235270979361)
                    ·
                      refine ⟨2865616405230926453234521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820821873641235270979361 2865616405230926453234521)
                      ·
                        rfl

theorem cell23_5580768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_5580768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580768 prefixEnd_5580768 := by exact prefixLift 5580768
  have htrace : WordTrace (prefixWord ++ tailWord_5580768) baseStart_5580768 baseEnd_5580768 := by
    simpa [prefixWord, tailWord_5580768, baseEnd_5580768] using wordTrace_append hprefix tailTrace_5580768
  have hstable : (prefixWord ++ tailWord_5580768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580768).length < 2 ^ (prefixWord ++ tailWord_5580768).sum := by decide
  have hdescent : baseEnd_5580768 < baseStart_5580768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580841 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_5580841 : Nat := 118140960795 + 5580841 * 2 ^ 59
def prefixEnd_5580841 : Nat := 4983230072969 + 3 ^ 40 * 5580841 * 2
def baseEnd_5580841 : Nat := 2865653889318704667621685

theorem tailTrace_5580841 : CollatzResearch.WordTrace tailWord_5580841 prefixEnd_5580841 2865653889318704667621685 := by
  unfold tailWord_5580841
  simp only [CollatzResearch.WordTrace]
  refine ⟨203549993574573663605214377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135699995716382442403476251 203549993574573663605214377)
  ·
    refine ⟨152662495180930247703910783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203549993574573663605214377 152662495180930247703910783)
    ·
      refine ⟨228993742771395371555866175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152662495180930247703910783 228993742771395371555866175)
      ·
        refine ⟨343490614157093057333799263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228993742771395371555866175 343490614157093057333799263)
        ·
          refine ⟨515235921235639586000698895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343490614157093057333799263 515235921235639586000698895)
          ·
            refine ⟨772853881853459379001048343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515235921235639586000698895 772853881853459379001048343)
            ·
              refine ⟨1159280822780189068501572515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772853881853459379001048343 1159280822780189068501572515)
              ·
                refine ⟨1738921234170283602752358773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159280822780189068501572515 1738921234170283602752358773)
                ·
                  refine ⟨163023865703464087758033635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1738921234170283602752358773 163023865703464087758033635)
                  ·
                    refine ⟨244535798555196131637050453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 163023865703464087758033635 244535798555196131637050453)
                    ·
                      refine ⟨2865653889318704667621685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 244535798555196131637050453 2865653889318704667621685)
                      ·
                        rfl

theorem cell23_5580841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_5580841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580841 prefixEnd_5580841 := by exact prefixLift 5580841
  have htrace : WordTrace (prefixWord ++ tailWord_5580841) baseStart_5580841 baseEnd_5580841 := by
    simpa [prefixWord, tailWord_5580841, baseEnd_5580841] using wordTrace_append hprefix tailTrace_5580841
  have hstable : (prefixWord ++ tailWord_5580841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580841).length < 2 ^ (prefixWord ++ tailWord_5580841).sum := by decide
  have hdescent : baseEnd_5580841 < baseStart_5580841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580905 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 4]
def baseStart_5580905 : Nat := 118140960795 + 5580905 * 2 ^ 59
def prefixEnd_5580905 : Nat := 4983230072969 + 3 ^ 40 * 5580905 * 2
def baseEnd_5580905 : Nat := 2865686752080592417221391

theorem tailTrace_5580905 : CollatzResearch.WordTrace tailWord_5580905 prefixEnd_5580905 2865686752080592417221391 := by
  unfold tailWord_5580905
  simp only [CollatzResearch.WordTrace]
  refine ⟨203552327846341802535544169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135701551897561201690362779 203552327846341802535544169)
  ·
    refine ⟨152664245884756351901658127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203552327846341802535544169 152664245884756351901658127)
    ·
      refine ⟨228996368827134527852487191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152664245884756351901658127 228996368827134527852487191)
      ·
        refine ⟨343494553240701791778730787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228996368827134527852487191 343494553240701791778730787)
        ·
          refine ⟨515241829861052687668096181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343494553240701791778730787 515241829861052687668096181)
          ·
            refine ⟨48303921549473689468884017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 515241829861052687668096181 48303921549473689468884017)
            ·
              refine ⟨36227941162105267101663013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48303921549473689468884017 36227941162105267101663013)
              ·
                refine ⟨6792738967894737581561815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36227941162105267101663013 6792738967894737581561815)
                ·
                  refine ⟨10189108451842106372342723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6792738967894737581561815 10189108451842106372342723)
                  ·
                    refine ⟨15283662677763159558514085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10189108451842106372342723 15283662677763159558514085)
                    ·
                      refine ⟨2865686752080592417221391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15283662677763159558514085 2865686752080592417221391)
                      ·
                        rfl

theorem cell23_5580905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 1, 4].length) (baseStart_5580905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580905 prefixEnd_5580905 := by exact prefixLift 5580905
  have htrace : WordTrace (prefixWord ++ tailWord_5580905) baseStart_5580905 baseEnd_5580905 := by
    simpa [prefixWord, tailWord_5580905, baseEnd_5580905] using wordTrace_append hprefix tailTrace_5580905
  have hstable : (prefixWord ++ tailWord_5580905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580905).length < 2 ^ (prefixWord ++ tailWord_5580905).sum := by decide
  have hdescent : baseEnd_5580905 < baseStart_5580905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580942 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_5580942 : Nat := 118140960795 + 5580942 * 2 ^ 59
def prefixEnd_5580942 : Nat := 4983230072969 + 3 ^ 40 * 5580942 * 2
def baseEnd_5580942 : Nat := 2865705750864808772458721

theorem tailTrace_5580942 : CollatzResearch.WordTrace tailWord_5580942 prefixEnd_5580942 2865705750864808772458721 := by
  unfold tailWord_5580942
  simp only [CollatzResearch.WordTrace]
  refine ⟨25444209668400969731830135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135702451564805171903094053 25444209668400969731830135)
  ·
    refine ⟨38166314502601454597745203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25444209668400969731830135 38166314502601454597745203)
    ·
      refine ⟨57249471753902181896617805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38166314502601454597745203 57249471753902181896617805)
      ·
        refine ⟨21468551907713318211231677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57249471753902181896617805 21468551907713318211231677)
        ·
          refine ⟨8050706965392494329211879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21468551907713318211231677 8050706965392494329211879)
          ·
            refine ⟨12076060448088741493817819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8050706965392494329211879 12076060448088741493817819)
            ·
              refine ⟨18114090672133112240726729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12076060448088741493817819 18114090672133112240726729)
              ·
                refine ⟨13585568004099834180545047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18114090672133112240726729 13585568004099834180545047)
                ·
                  refine ⟨20378352006149751270817571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13585568004099834180545047 20378352006149751270817571)
                  ·
                    refine ⟨30567528009224626906226357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20378352006149751270817571 30567528009224626906226357)
                    ·
                      refine ⟨2865705750864808772458721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30567528009224626906226357 2865705750864808772458721)
                      ·
                        rfl

theorem cell23_5580942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_5580942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580942 prefixEnd_5580942 := by exact prefixLift 5580942
  have htrace : WordTrace (prefixWord ++ tailWord_5580942) baseStart_5580942 baseEnd_5580942 := by
    simpa [prefixWord, tailWord_5580942, baseEnd_5580942] using wordTrace_append hprefix tailTrace_5580942
  have hstable : (prefixWord ++ tailWord_5580942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580942).length < 2 ^ (prefixWord ++ tailWord_5580942).sum := by decide
  have hdescent : baseEnd_5580942 < baseStart_5580942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580959 : List Nat := [1, 1, 2, 6, 1, 2, 2, 2, 1, 2, 3]
def baseStart_5580959 : Nat := 118140960795 + 5580959 * 2 ^ 59
def prefixEnd_5580959 : Nat := 4983230072969 + 3 ^ 40 * 5580959 * 2
def baseEnd_5580959 : Nat := 2865714480035935205946143

theorem tailTrace_5580959 : CollatzResearch.WordTrace tailWord_5580959 prefixEnd_5580959 2865714480035935205946143 := by
  unfold tailWord_5580959
  simp only [CollatzResearch.WordTrace]
  refine ⟨203554297388146169758009931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135702864925430779838673287 203554297388146169758009931)
  ·
    refine ⟨305331446082219254637014897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203554297388146169758009931 305331446082219254637014897)
    ·
      refine ⟨228998584561664440977761173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305331446082219254637014897 228998584561664440977761173)
      ·
        refine ⟨10734308651328020670832555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 228998584561664440977761173 10734308651328020670832555)
        ·
          refine ⟨16101462976992031006248833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10734308651328020670832555 16101462976992031006248833)
          ·
            refine ⟨12076097232744023254686625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16101462976992031006248833 12076097232744023254686625)
            ·
              refine ⟨9057072924558017441014969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12076097232744023254686625 9057072924558017441014969)
              ·
                refine ⟨6792804693418513080761227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9057072924558017441014969 6792804693418513080761227)
                ·
                  refine ⟨10189207040127769621141841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6792804693418513080761227 10189207040127769621141841)
                  ·
                    refine ⟨7641905280095827215856381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10189207040127769621141841 7641905280095827215856381)
                    ·
                      refine ⟨2865714480035935205946143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7641905280095827215856381 2865714480035935205946143)
                      ·
                        rfl

theorem cell23_5580959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_5580959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580959 prefixEnd_5580959 := by exact prefixLift 5580959
  have htrace : WordTrace (prefixWord ++ tailWord_5580959) baseStart_5580959 baseEnd_5580959 := by
    simpa [prefixWord, tailWord_5580959, baseEnd_5580959] using wordTrace_append hprefix tailTrace_5580959
  have hstable : (prefixWord ++ tailWord_5580959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580959).length < 2 ^ (prefixWord ++ tailWord_5580959).sum := by decide
  have hdescent : baseEnd_5580959 < baseStart_5580959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580962 : List Nat := [3, 3, 1, 3, 1, 1, 4, 7]
def baseStart_5580962 : Nat := 118140960795 + 5580962 * 2 ^ 59
def prefixEnd_5580962 : Nat := 4983230072969 + 3 ^ 40 * 5580962 * 2
def baseEnd_5580962 : Nat := 106137630388070322007727

theorem tailTrace_5580962 : CollatzResearch.WordTrace tailWord_5580962 prefixEnd_5580962 106137630388070322007727 := by
  unfold tailWord_5580962
  simp only [CollatzResearch.WordTrace]
  refine ⟨50888601701783825317592285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135702937871423534180246093 50888601701783825317592285)
  ·
    refine ⟨19083225638168934494097107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50888601701783825317592285 19083225638168934494097107)
    ·
      refine ⟨28624838457253401741145661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19083225638168934494097107 28624838457253401741145661)
      ·
        refine ⟨10734314421470025652929623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28624838457253401741145661 10734314421470025652929623)
        ·
          refine ⟨16101471632205038479394435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10734314421470025652929623 16101471632205038479394435)
          ·
            refine ⟨24152207448307557719091653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16101471632205038479394435 24152207448307557719091653)
            ·
              refine ⟨4528538896557667072329685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24152207448307557719091653 4528538896557667072329685)
              ·
                refine ⟨106137630388070322007727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4528538896557667072329685 106137630388070322007727)
                ·
                  rfl

theorem cell23_5580962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 7].length) (baseStart_5580962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580962 prefixEnd_5580962 := by exact prefixLift 5580962
  have htrace : WordTrace (prefixWord ++ tailWord_5580962) baseStart_5580962 baseEnd_5580962 := by
    simpa [prefixWord, tailWord_5580962, baseEnd_5580962] using wordTrace_append hprefix tailTrace_5580962
  have hstable : (prefixWord ++ tailWord_5580962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580962).length < 2 ^ (prefixWord ++ tailWord_5580962).sum := by decide
  have hdescent : baseEnd_5580962 < baseStart_5580962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580973 : List Nat := [1, 5, 2, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_5580973 : Nat := 118140960795 + 5580973 * 2 ^ 59
def prefixEnd_5580973 : Nat := 4983230072969 + 3 ^ 40 * 5580973 * 2
def baseEnd_5580973 : Nat := 2865721668765098151171079

theorem tailTrace_5580973 : CollatzResearch.WordTrace tailWord_5580973 prefixEnd_5580973 2865721668765098151171079 := by
  unfold tailWord_5580973
  simp only [CollatzResearch.WordTrace]
  refine ⟨203554808010095450149019573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135703205340063633432679715 203554808010095450149019573)
  ·
    refine ⟨19083263250946448451470585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203554808010095450149019573 19083263250946448451470585)
    ·
      refine ⟨14312447438209836338602939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19083263250946448451470585 14312447438209836338602939)
      ·
        refine ⟨21468671157314754507904409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14312447438209836338602939 21468671157314754507904409)
        ·
          refine ⟨16101503367986065880928307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21468671157314754507904409 16101503367986065880928307)
          ·
            refine ⟨24152255051979098821392461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16101503367986065880928307 24152255051979098821392461)
            ·
              refine ⟨9057095644492162058022173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24152255051979098821392461 9057095644492162058022173)
              ·
                refine ⟨3396410866684560771758315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9057095644492162058022173 3396410866684560771758315)
                ·
                  refine ⟨5094616300026841157637473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396410866684560771758315 5094616300026841157637473)
                  ·
                    refine ⟨3820962225020130868228105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5094616300026841157637473 3820962225020130868228105)
                    ·
                      refine ⟨2865721668765098151171079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820962225020130868228105 2865721668765098151171079)
                      ·
                        rfl

theorem cell23_5580973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_5580973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580973 prefixEnd_5580973 := by exact prefixLift 5580973
  have htrace : WordTrace (prefixWord ++ tailWord_5580973) baseStart_5580973 baseEnd_5580973 := by
    simpa [prefixWord, tailWord_5580973, baseEnd_5580973] using wordTrace_append hprefix tailTrace_5580973
  have hstable : (prefixWord ++ tailWord_5580973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580973).length < 2 ^ (prefixWord ++ tailWord_5580973).sum := by decide
  have hdescent : baseEnd_5580973 < baseStart_5580973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5580990 : List Nat := [4, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_5580990 : Nat := 118140960795 + 5580990 * 2 ^ 59
def prefixEnd_5580990 : Nat := 4983230072969 + 3 ^ 40 * 5580990 * 2
def baseEnd_5580990 : Nat := 2865730397936224584658501

theorem tailTrace_5580990 : CollatzResearch.WordTrace tailWord_5580990 prefixEnd_5580990 2865730397936224584658501 := by
  unfold tailWord_5580990
  simp only [CollatzResearch.WordTrace]
  refine ⟨25444428506379232756548553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135703618700689241368258949 25444428506379232756548553)
  ·
    refine ⟨19083321379784424567411415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25444428506379232756548553 19083321379784424567411415)
    ·
      refine ⟨28624982069676636851117123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19083321379784424567411415 28624982069676636851117123)
      ·
        refine ⟨42937473104514955276675685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28624982069676636851117123 42937473104514955276675685)
        ·
          refine ⟨8050776207096554114376691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42937473104514955276675685 8050776207096554114376691)
          ·
            refine ⟨12076164310644831171565037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8050776207096554114376691 12076164310644831171565037)
            ·
              refine ⟨4528561616491811689336889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12076164310644831171565037 4528561616491811689336889)
              ·
                refine ⟨3396421212368858767002667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4528561616491811689336889 3396421212368858767002667)
                ·
                  refine ⟨5094631818553288150504001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396421212368858767002667 5094631818553288150504001)
                  ·
                    refine ⟨3820973863914966112878001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5094631818553288150504001 3820973863914966112878001)
                    ·
                      refine ⟨2865730397936224584658501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820973863914966112878001 2865730397936224584658501)
                      ·
                        rfl

theorem cell23_5580990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_5580990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5580990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5580990 prefixEnd_5580990 := by exact prefixLift 5580990
  have htrace : WordTrace (prefixWord ++ tailWord_5580990) baseStart_5580990 baseEnd_5580990 := by
    simpa [prefixWord, tailWord_5580990, baseEnd_5580990] using wordTrace_append hprefix tailTrace_5580990
  have hstable : (prefixWord ++ tailWord_5580990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5580990).length < 2 ^ (prefixWord ++ tailWord_5580990).sum := by decide
  have hdescent : baseEnd_5580990 < baseStart_5580990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5580990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581006 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3]
def baseStart_5581006 : Nat := 118140960795 + 5581006 * 2 ^ 59
def prefixEnd_5581006 : Nat := 4983230072969 + 3 ^ 40 * 5581006 * 2
def baseEnd_5581006 : Nat := 2865738613626696522058427

theorem tailTrace_5581006 : CollatzResearch.WordTrace tailWord_5581006 prefixEnd_5581006 2865738613626696522058427 := by
  unfold tailWord_5581006
  simp only [CollatzResearch.WordTrace]
  refine ⟨25444501452371987098121359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135704007745983931189980581 25444501452371987098121359)
  ·
    refine ⟨38166752178557980647182039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25444501452371987098121359 38166752178557980647182039)
    ·
      refine ⟨57250128267836970970773059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38166752178557980647182039 57250128267836970970773059)
      ·
        refine ⟨85875192401755456456159589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57250128267836970970773059 85875192401755456456159589)
        ·
          refine ⟨16101598575329148085529923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85875192401755456456159589 16101598575329148085529923)
          ·
            refine ⟨24152397862993722128294885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16101598575329148085529923 24152397862993722128294885)
            ·
              refine ⟨4528574599311322899055291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24152397862993722128294885 4528574599311322899055291)
              ·
                refine ⟨6792861898966984348582937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528574599311322899055291 6792861898966984348582937)
                ·
                  refine ⟨5094646424225238261437203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6792861898966984348582937 5094646424225238261437203)
                  ·
                    refine ⟨7641969636337857392155805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5094646424225238261437203 7641969636337857392155805)
                    ·
                      refine ⟨2865738613626696522058427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7641969636337857392155805 2865738613626696522058427)
                      ·
                        rfl

theorem cell23_5581006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_5581006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581006 prefixEnd_5581006 := by exact prefixLift 5581006
  have htrace : WordTrace (prefixWord ++ tailWord_5581006) baseStart_5581006 baseEnd_5581006 := by
    simpa [prefixWord, tailWord_5581006, baseEnd_5581006] using wordTrace_append hprefix tailTrace_5581006
  have hstable : (prefixWord ++ tailWord_5581006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581006).length < 2 ^ (prefixWord ++ tailWord_5581006).sum := by decide
  have hdescent : baseEnd_5581006 < baseStart_5581006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581008 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_5581008 : Nat := 118140960795 + 5581008 * 2 ^ 59
def prefixEnd_5581008 : Nat := 4983230072969 + 3 ^ 40 * 5581008 * 2
def baseEnd_5581008 : Nat := 2865739640588005514233417

theorem tailTrace_5581008 : CollatzResearch.WordTrace tailWord_5581008 prefixEnd_5581008 2865739640588005514233417 := by
  unfold tailWord_5581008
  simp only [CollatzResearch.WordTrace]
  refine ⟨101778042282484325563271839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135704056376645767417695785 101778042282484325563271839)
  ·
    refine ⟨152667063423726488344907759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101778042282484325563271839 152667063423726488344907759)
    ·
      refine ⟨229000595135589732517361639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152667063423726488344907759 229000595135589732517361639)
      ·
        refine ⟨343500892703384598776042459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229000595135589732517361639 343500892703384598776042459)
        ·
          refine ⟨515251339055076898164063689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343500892703384598776042459 515251339055076898164063689)
          ·
            refine ⟨386438504291307673623047767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515251339055076898164063689 386438504291307673623047767)
            ·
              refine ⟨579657756436961510434571651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386438504291307673623047767 579657756436961510434571651)
              ·
                refine ⟨869486634655442265651857477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579657756436961510434571651 869486634655442265651857477)
                ·
                  refine ⟨163028743997895424809723277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 869486634655442265651857477 163028743997895424809723277)
                  ·
                    refine ⟨61135778999210784303646229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163028743997895424809723277 61135778999210784303646229)
                    ·
                      refine ⟨2865739640588005514233417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61135778999210784303646229 2865739640588005514233417)
                      ·
                        rfl

theorem cell23_5581008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_5581008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581008 prefixEnd_5581008 := by exact prefixLift 5581008
  have htrace : WordTrace (prefixWord ++ tailWord_5581008) baseStart_5581008 baseEnd_5581008 := by
    simpa [prefixWord, tailWord_5581008, baseEnd_5581008] using wordTrace_append hprefix tailTrace_5581008
  have hstable : (prefixWord ++ tailWord_5581008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581008).length < 2 ^ (prefixWord ++ tailWord_5581008).sum := by decide
  have hdescent : baseEnd_5581008 < baseStart_5581008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581016 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 1, 3, 2]
def baseStart_5581016 : Nat := 118140960795 + 5581016 * 2 ^ 59
def prefixEnd_5581016 : Nat := 4983230072969 + 3 ^ 40 * 5581016 * 2
def baseEnd_5581016 : Nat := 2865743748433241482933381

theorem tailTrace_5581016 : CollatzResearch.WordTrace tailWord_5581016 prefixEnd_5581016 2865743748433241482933381 := by
  unfold tailWord_5581016
  simp only [CollatzResearch.WordTrace]
  refine ⟨101778188174469834246417451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135704250899293112328556601 101778188174469834246417451)
  ·
    refine ⟨152667282261704751369626177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101778188174469834246417451 152667282261704751369626177)
    ·
      refine ⟨114500461696278563527219633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152667282261704751369626177 114500461696278563527219633)
      ·
        refine ⟨85875346272208922645414725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114500461696278563527219633 85875346272208922645414725)
        ·
          refine ⟨16101627426039172996015261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85875346272208922645414725 16101627426039172996015261)
          ·
            refine ⟨6038110284764689873505723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16101627426039172996015261 6038110284764689873505723)
            ·
              refine ⟨9057165427147034810258585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6038110284764689873505723 9057165427147034810258585)
              ·
                refine ⟨6792874070360276107693939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9057165427147034810258585 6792874070360276107693939)
                ·
                  refine ⟨10189311105540414161540909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6792874070360276107693939 10189311105540414161540909)
                  ·
                    refine ⟨3820991664577655310577841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10189311105540414161540909 3820991664577655310577841)
                    ·
                      refine ⟨2865743748433241482933381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3820991664577655310577841 2865743748433241482933381)
                      ·
                        rfl

theorem cell23_5581016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_5581016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581016 prefixEnd_5581016 := by exact prefixLift 5581016
  have htrace : WordTrace (prefixWord ++ tailWord_5581016) baseStart_5581016 baseEnd_5581016 := by
    simpa [prefixWord, tailWord_5581016, baseEnd_5581016] using wordTrace_append hprefix tailTrace_5581016
  have hstable : (prefixWord ++ tailWord_5581016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581016).length < 2 ^ (prefixWord ++ tailWord_5581016).sum := by decide
  have hdescent : baseEnd_5581016 < baseStart_5581016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581029 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 1, 4, 2]
def baseStart_5581029 : Nat := 118140960795 + 5581029 * 2 ^ 59
def prefixEnd_5581029 : Nat := 4983230072969 + 3 ^ 40 * 5581029 * 2
def baseEnd_5581029 : Nat := 2865750423681749932070821

theorem tailTrace_5581029 : CollatzResearch.WordTrace tailWord_5581029 prefixEnd_5581029 2865750423681749932070821 := by
  unfold tailWord_5581029
  simp only [CollatzResearch.WordTrace]
  refine ⟨203556850497892571713058141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135704566998595047808705427 203556850497892571713058141)
  ·
    refine ⟨76333818936709714392396803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203556850497892571713058141 76333818936709714392396803)
    ·
      refine ⟨114500728405064571588595205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76333818936709714392396803 114500728405064571588595205)
      ·
        refine ⟨21468886575949607172861601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114500728405064571588595205 21468886575949607172861601)
        ·
          refine ⟨16101664931962205379646201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21468886575949607172861601 16101664931962205379646201)
          ·
            refine ⟨12076248698971654034734651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16101664931962205379646201 12076248698971654034734651)
            ·
              refine ⟨18114373048457481052101977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12076248698971654034734651 18114373048457481052101977)
              ·
                refine ⟨13585779786343110789076483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18114373048457481052101977 13585779786343110789076483)
                ·
                  refine ⟨20378669679514666183614725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13585779786343110789076483 20378669679514666183614725)
                  ·
                    refine ⟨3821000564908999909427761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20378669679514666183614725 3821000564908999909427761)
                    ·
                      refine ⟨2865750423681749932070821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3821000564908999909427761 2865750423681749932070821)
                      ·
                        rfl

theorem cell23_5581029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_5581029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581029 prefixEnd_5581029 := by exact prefixLift 5581029
  have htrace : WordTrace (prefixWord ++ tailWord_5581029) baseStart_5581029 baseEnd_5581029 := by
    simpa [prefixWord, tailWord_5581029, baseEnd_5581029] using wordTrace_append hprefix tailTrace_5581029
  have hstable : (prefixWord ++ tailWord_5581029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581029).length < 2 ^ (prefixWord ++ tailWord_5581029).sum := by decide
  have hdescent : baseEnd_5581029 < baseStart_5581029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581046 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2]
def baseStart_5581046 : Nat := 118140960795 + 5581046 * 2 ^ 59
def prefixEnd_5581046 : Nat := 4983230072969 + 3 ^ 40 * 5581046 * 2
def baseEnd_5581046 : Nat := 2865759152852876365558243

theorem tailTrace_5581046 : CollatzResearch.WordTrace tailWord_5581046 prefixEnd_5581046 2865759152852876365558243 := by
  unfold tailWord_5581046
  simp only [CollatzResearch.WordTrace]
  refine ⟨12722341908676936476026687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 135704980359220655744284661 12722341908676936476026687)
  ·
    refine ⟨19083512863015404714040031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12722341908676936476026687 19083512863015404714040031)
    ·
      refine ⟨28625269294523107071060047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19083512863015404714040031 28625269294523107071060047)
      ·
        refine ⟨42937903941784660606590071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28625269294523107071060047 42937903941784660606590071)
        ·
          refine ⟨64406855912676990909885107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42937903941784660606590071 64406855912676990909885107)
          ·
            refine ⟨96610283869015486364827661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64406855912676990909885107 96610283869015486364827661)
            ·
              refine ⟨36228856450880807386810373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96610283869015486364827661 36228856450880807386810373)
              ·
                refine ⟨6792910584540151385026945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36228856450880807386810373 6792910584540151385026945)
                ·
                  refine ⟨5094682938405113538770209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6792910584540151385026945 5094682938405113538770209)
                  ·
                    refine ⟨3821012203803835154077657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5094682938405113538770209 3821012203803835154077657)
                    ·
                      refine ⟨2865759152852876365558243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3821012203803835154077657 2865759152852876365558243)
                      ·
                        rfl

theorem cell23_5581046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_5581046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581046 prefixEnd_5581046 := by exact prefixLift 5581046
  have htrace : WordTrace (prefixWord ++ tailWord_5581046) baseStart_5581046 baseEnd_5581046 := by
    simpa [prefixWord, tailWord_5581046, baseEnd_5581046] using wordTrace_append hprefix tailTrace_5581046
  have hstable : (prefixWord ++ tailWord_5581046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581046).length < 2 ^ (prefixWord ++ tailWord_5581046).sum := by decide
  have hdescent : baseEnd_5581046 < baseStart_5581046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581082 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 1, 7]
def baseStart_5581082 : Nat := 118140960795 + 5581082 * 2 ^ 59
def prefixEnd_5581082 : Nat := 4983230072969 + 3 ^ 40 * 5581082 * 2
def baseEnd_5581082 : Nat := 955259212718812741569359

theorem tailTrace_5581082 : CollatzResearch.WordTrace tailWord_5581082 prefixEnd_5581082 955259212718812741569359 := by
  unfold tailWord_5581082
  simp only [CollatzResearch.WordTrace]
  refine ⟨50889695891675140441184375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135705855711133707843158333 50889695891675140441184375)
  ·
    refine ⟨76334543837512710661776563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50889695891675140441184375 76334543837512710661776563)
    ·
      refine ⟨114501815756269065992664845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76334543837512710661776563 114501815756269065992664845)
      ·
        refine ⟨42938180908600899747249317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114501815756269065992664845 42938180908600899747249317)
        ·
          refine ⟨8050908920362668702609247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42938180908600899747249317 8050908920362668702609247)
          ·
            refine ⟨12076363380544003053913871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8050908920362668702609247 12076363380544003053913871)
            ·
              refine ⟨18114545070816004580870807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12076363380544003053913871 18114545070816004580870807)
              ·
                refine ⟨27171817606224006871306211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18114545070816004580870807 27171817606224006871306211)
                ·
                  refine ⟨40757726409336010306959317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27171817606224006871306211 40757726409336010306959317)
                  ·
                    refine ⟨955259212718812741569359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40757726409336010306959317 955259212718812741569359)
                    ·
                      rfl

theorem cell23_5581082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_5581082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581082 prefixEnd_5581082 := by exact prefixLift 5581082
  have htrace : WordTrace (prefixWord ++ tailWord_5581082) baseStart_5581082 baseEnd_5581082 := by
    simpa [prefixWord, tailWord_5581082, baseEnd_5581082] using wordTrace_append hprefix tailTrace_5581082
  have hstable : (prefixWord ++ tailWord_5581082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581082).length < 2 ^ (prefixWord ++ tailWord_5581082).sum := by decide
  have hdescent : baseEnd_5581082 < baseStart_5581082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581086 : List Nat := [4, 3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_5581086 : Nat := 118140960795 + 5581086 * 2 ^ 59
def prefixEnd_5581086 : Nat := 4983230072969 + 3 ^ 40 * 5581086 * 2
def baseEnd_5581086 : Nat := 318419965786561801006451

theorem tailTrace_5581086 : CollatzResearch.WordTrace tailWord_5581086 prefixEnd_5581086 318419965786561801006451 := by
  unfold tailWord_5581086
  simp only [CollatzResearch.WordTrace]
  refine ⟨25444866182335758805985389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135705952972457380298588741 25444866182335758805985389)
  ·
    refine ⟨9541824818375909552244521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25444866182335758805985389 9541824818375909552244521)
    ·
      refine ⟨7156368613781932164183391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9541824818375909552244521 7156368613781932164183391)
      ·
        refine ⟨10734552920672898246275087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7156368613781932164183391 10734552920672898246275087)
        ·
          refine ⟨16101829381009347369412631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10734552920672898246275087 16101829381009347369412631)
          ·
            refine ⟨24152744071514021054118947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16101829381009347369412631 24152744071514021054118947)
            ·
              refine ⟨36229116107271031581178421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24152744071514021054118947 36229116107271031581178421)
              ·
                refine ⟨3396479635056659210735477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36229116107271031581178421 3396479635056659210735477)
                ·
                  refine ⟨318419965786561801006451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3396479635056659210735477 318419965786561801006451)
                  ·
                    rfl

theorem cell23_5581086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_5581086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581086 prefixEnd_5581086 := by exact prefixLift 5581086
  have htrace : WordTrace (prefixWord ++ tailWord_5581086) baseStart_5581086 baseEnd_5581086 := by
    simpa [prefixWord, tailWord_5581086, baseEnd_5581086] using wordTrace_append hprefix tailTrace_5581086
  have hstable : (prefixWord ++ tailWord_5581086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581086).length < 2 ^ (prefixWord ++ tailWord_5581086).sum := by decide
  have hdescent : baseEnd_5581086 < baseStart_5581086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581112 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 3, 4]
def baseStart_5581112 : Nat := 118140960795 + 5581112 * 2 ^ 59
def prefixEnd_5581112 : Nat := 4983230072969 + 3 ^ 40 * 5581112 * 2
def baseEnd_5581112 : Nat := 955264347525357702444313

theorem tailTrace_5581112 : CollatzResearch.WordTrace tailWord_5581112 prefixEnd_5581112 955264347525357702444313 := by
  unfold tailWord_5581112
  simp only [CollatzResearch.WordTrace]
  refine ⟨101779938878295938444164795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135706585171061251258886393 101779938878295938444164795)
  ·
    refine ⟨152669908317443907666247193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101779938878295938444164795 152669908317443907666247193)
    ·
      refine ⟨114502431238082930749685395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152669908317443907666247193 114502431238082930749685395)
      ·
        refine ⟨171753646857124396124528093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114502431238082930749685395 171753646857124396124528093)
        ·
          refine ⟨64407617571421648546698035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171753646857124396124528093 64407617571421648546698035)
          ·
            refine ⟨96611426357132472820047053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64407617571421648546698035 96611426357132472820047053)
            ·
              refine ⟨36229284883924677307517645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96611426357132472820047053 36229284883924677307517645)
              ·
                refine ⟨13585981831471753990319117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36229284883924677307517645 13585981831471753990319117)
                ·
                  refine ⟨5094743186801907746369669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13585981831471753990319117 5094743186801907746369669)
                  ·
                    refine ⟨955264347525357702444313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5094743186801907746369669 955264347525357702444313)
                    ·
                      rfl

theorem cell23_5581112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_5581112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581112 prefixEnd_5581112 := by exact prefixLift 5581112
  have htrace : WordTrace (prefixWord ++ tailWord_5581112) baseStart_5581112 baseEnd_5581112 := by
    simpa [prefixWord, tailWord_5581112, baseEnd_5581112] using wordTrace_append hprefix tailTrace_5581112
  have hstable : (prefixWord ++ tailWord_5581112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581112).length < 2 ^ (prefixWord ++ tailWord_5581112).sum := by decide
  have hdescent : baseEnd_5581112 < baseStart_5581112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581150 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_5581150 : Nat := 118140960795 + 5581150 * 2 ^ 59
def prefixEnd_5581150 : Nat := 4983230072969 + 3 ^ 40 * 5581150 * 2
def baseEnd_5581150 : Nat := 955270851613647986219255

theorem tailTrace_5581150 : CollatzResearch.WordTrace tailWord_5581150 prefixEnd_5581150 955270851613647986219255 := by
  unfold tailWord_5581150
  simp only [CollatzResearch.WordTrace]
  refine ⟨25445157966306776172276613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135707509153636139585475269 25445157966306776172276613)
  ·
    refine ⟨4770967118682520532301865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25445157966306776172276613 4770967118682520532301865)
    ·
      refine ⟨3578225339011890399226399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4770967118682520532301865 3578225339011890399226399)
      ·
        refine ⟨5367338008517835598839599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3578225339011890399226399 5367338008517835598839599)
        ·
          refine ⟨8051007012776753398259399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5367338008517835598839599 8051007012776753398259399)
          ·
            refine ⟨12076510519165130097389099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8051007012776753398259399 12076510519165130097389099)
            ·
              refine ⟨18114765778747695146083649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12076510519165130097389099 18114765778747695146083649)
              ·
                refine ⟨13586074334060771359562737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18114765778747695146083649 13586074334060771359562737)
                ·
                  refine ⟨10189555750545578519672053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13586074334060771359562737 10189555750545578519672053)
                  ·
                    refine ⟨955270851613647986219255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10189555750545578519672053 955270851613647986219255)
                    ·
                      rfl

theorem cell23_5581150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_5581150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581150 prefixEnd_5581150 := by exact prefixLift 5581150
  have htrace : WordTrace (prefixWord ++ tailWord_5581150) baseStart_5581150 baseEnd_5581150 := by
    simpa [prefixWord, tailWord_5581150, baseEnd_5581150] using wordTrace_append hprefix tailTrace_5581150
  have hstable : (prefixWord ++ tailWord_5581150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581150).length < 2 ^ (prefixWord ++ tailWord_5581150).sum := by decide
  have hdescent : baseEnd_5581150 < baseStart_5581150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581196 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 2, 3, 2]
def baseStart_5581196 : Nat := 118140960795 + 5581196 * 2 ^ 59
def prefixEnd_5581196 : Nat := 4983230072969 + 3 ^ 40 * 5581196 * 2
def baseEnd_5581196 : Nat := 2865836174951050778682553

theorem tailTrace_5581196 : CollatzResearch.WordTrace tailWord_5581196 prefixEnd_5581196 2865836174951050778682553 := by
  unfold tailWord_5581196
  simp only [CollatzResearch.WordTrace]
  refine ⟨101781470744143779617193721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135708627658858372822924961 101781470744143779617193721)
  ·
    refine ⟨76336103058107834712895291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101781470744143779617193721 76336103058107834712895291)
    ·
      refine ⟨114504154587161752069342937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76336103058107834712895291 114504154587161752069342937)
      ·
        refine ⟨85878115940371314052007203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114504154587161752069342937 85878115940371314052007203)
        ·
          refine ⟨128817173910556971078010805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85878115940371314052007203 128817173910556971078010805)
          ·
            refine ⟨12076610054114716038563513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 128817173910556971078010805 12076610054114716038563513)
            ·
              refine ⟨9057457540586037028922635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12076610054114716038563513 9057457540586037028922635)
              ·
                refine ⟨13586186310879055543383953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9057457540586037028922635 13586186310879055543383953)
                ·
                  refine ⟨10189639733159291657537965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13586186310879055543383953 10189639733159291657537965)
                  ·
                    refine ⟨3821114899934734371576737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10189639733159291657537965 3821114899934734371576737)
                    ·
                      refine ⟨2865836174951050778682553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3821114899934734371576737 2865836174951050778682553)
                      ·
                        rfl

theorem cell23_5581196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_5581196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581196 prefixEnd_5581196 := by exact prefixLift 5581196
  have htrace : WordTrace (prefixWord ++ tailWord_5581196) baseStart_5581196 baseEnd_5581196 := by
    simpa [prefixWord, tailWord_5581196, baseEnd_5581196] using wordTrace_append hprefix tailTrace_5581196
  have hstable : (prefixWord ++ tailWord_5581196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581196).length < 2 ^ (prefixWord ++ tailWord_5581196).sum := by decide
  have hdescent : baseEnd_5581196 < baseStart_5581196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581219 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 2, 4]
def baseStart_5581219 : Nat := 118140960795 + 5581219 * 2 ^ 59
def prefixEnd_5581219 : Nat := 4983230072969 + 3 ^ 40 * 5581219 * 2
def baseEnd_5581219 : Nat := 955282661668701396231649

theorem tailTrace_5581219 : CollatzResearch.WordTrace tailWord_5581219 prefixEnd_5581219 955282661668701396231649 := by
  unfold tailWord_5581219
  simp only [CollatzResearch.WordTrace]
  refine ⟨203563780367204234162474711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135709186911469489441649807 203563780367204234162474711)
  ·
    refine ⟨305345670550806351243712067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203563780367204234162474711 305345670550806351243712067)
    ·
      refine ⟨458018505826209526865568101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305345670550806351243712067 458018505826209526865568101)
      ·
        refine ⟨85878469842414286287294019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 458018505826209526865568101 85878469842414286287294019)
        ·
          refine ⟨128817704763621429430941029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85878469842414286287294019 128817704763621429430941029)
          ·
            refine ⟨24153319643179018018301443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128817704763621429430941029 24153319643179018018301443)
            ·
              refine ⟨36229979464768527027452165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24153319643179018018301443 36229979464768527027452165)
              ·
                refine ⟨6793121149644098817647281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36229979464768527027452165 6793121149644098817647281)
                ·
                  refine ⟨5094840862233074113235461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6793121149644098817647281 5094840862233074113235461)
                  ·
                    refine ⟨955282661668701396231649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5094840862233074113235461 955282661668701396231649)
                    ·
                      rfl

theorem cell23_5581219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 4].length) (baseStart_5581219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581219 prefixEnd_5581219 := by exact prefixLift 5581219
  have htrace : WordTrace (prefixWord ++ tailWord_5581219) baseStart_5581219 baseEnd_5581219 := by
    simpa [prefixWord, tailWord_5581219, baseEnd_5581219] using wordTrace_append hprefix tailTrace_5581219
  have hstable : (prefixWord ++ tailWord_5581219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581219).length < 2 ^ (prefixWord ++ tailWord_5581219).sum := by decide
  have hdescent : baseEnd_5581219 < baseStart_5581219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581239 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 4]
def baseStart_5581239 : Nat := 118140960795 + 5581239 * 2 ^ 59
def prefixEnd_5581239 : Nat := 4983230072969 + 3 ^ 40 * 5581239 * 2
def baseEnd_5581239 : Nat := 2865858254619194110444855

theorem tailTrace_5581239 : CollatzResearch.WordTrace tailWord_5581239 prefixEnd_5581239 2865858254619194110444855 := by
  unfold tailWord_5581239
  simp only [CollatzResearch.WordTrace]
  refine ⟨203564509827131777578202771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135709673218087851718801847 203564509827131777578202771)
  ·
    refine ⟨305346764740697666367304157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203564509827131777578202771 305346764740697666367304157)
    ·
      refine ⟨114505036777761624887739059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305346764740697666367304157 114505036777761624887739059)
      ·
        refine ⟨171757555166642437331608589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114505036777761624887739059 171757555166642437331608589)
        ·
          refine ⟨64409083187490913999353221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171757555166642437331608589 64409083187490913999353221)
          ·
            refine ⟨12076703097654546374878729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64409083187490913999353221 12076703097654546374878729)
            ·
              refine ⟨9057527323240909781159047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12076703097654546374878729 9057527323240909781159047)
              ·
                refine ⟨13586290984861364671738571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9057527323240909781159047 13586290984861364671738571)
                ·
                  refine ⟨20379436477292047007607857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13586290984861364671738571 20379436477292047007607857)
                  ·
                    refine ⟨15284577357969035255705893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20379436477292047007607857 15284577357969035255705893)
                    ·
                      refine ⟨2865858254619194110444855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15284577357969035255705893 2865858254619194110444855)
                      ·
                        rfl

theorem cell23_5581239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_5581239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581239 prefixEnd_5581239 := by exact prefixLift 5581239
  have htrace : WordTrace (prefixWord ++ tailWord_5581239) baseStart_5581239 baseEnd_5581239 := by
    simpa [prefixWord, tailWord_5581239, baseEnd_5581239] using wordTrace_append hprefix tailTrace_5581239
  have hstable : (prefixWord ++ tailWord_5581239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581239).length < 2 ^ (prefixWord ++ tailWord_5581239).sum := by decide
  have hdescent : baseEnd_5581239 < baseStart_5581239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581259 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 4, 1, 3]
def baseStart_5581259 : Nat := 118140960795 + 5581259 * 2 ^ 59
def prefixEnd_5581259 : Nat := 4983230072969 + 3 ^ 40 * 5581259 * 2
def baseEnd_5581259 : Nat := 2865868524232284032194763

theorem tailTrace_5581259 : CollatzResearch.WordTrace tailWord_5581259 prefixEnd_5581259 2865868524232284032194763 := by
  unfold tailWord_5581259
  simp only [CollatzResearch.WordTrace]
  refine ⟨203565239287059320993930831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135710159524706213995953887 203565239287059320993930831)
  ·
    refine ⟨305347858930588981490896247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203565239287059320993930831 305347858930588981490896247)
    ·
      refine ⟨458021788395883472236344371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305347858930588981490896247 458021788395883472236344371)
      ·
        refine ⟨687032682593825208354516557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458021788395883472236344371 687032682593825208354516557)
        ·
          refine ⟨257637255972684453132943709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 687032682593825208354516557 257637255972684453132943709)
          ·
            refine ⟨96613970989756669924853891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 257637255972684453132943709 96613970989756669924853891)
            ·
              refine ⟨144920956484635004887280837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96613970989756669924853891 144920956484635004887280837)
              ·
                refine ⟨27172679340869063416365157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 144920956484635004887280837 27172679340869063416365157)
                ·
                  refine ⟨5094877376412949390568467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27172679340869063416365157 5094877376412949390568467)
                  ·
                    refine ⟨7642316064619424085852701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5094877376412949390568467 7642316064619424085852701)
                    ·
                      refine ⟨2865868524232284032194763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7642316064619424085852701 2865868524232284032194763)
                      ·
                        rfl

theorem cell23_5581259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 4, 1, 3].length) (baseStart_5581259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581259 prefixEnd_5581259 := by exact prefixLift 5581259
  have htrace : WordTrace (prefixWord ++ tailWord_5581259) baseStart_5581259 baseEnd_5581259 := by
    simpa [prefixWord, tailWord_5581259, baseEnd_5581259] using wordTrace_append hprefix tailTrace_5581259
  have hstable : (prefixWord ++ tailWord_5581259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581259).length < 2 ^ (prefixWord ++ tailWord_5581259).sum := by decide
  have hdescent : baseEnd_5581259 < baseStart_5581259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581260 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 1, 1, 4]
def baseStart_5581260 : Nat := 118140960795 + 5581260 * 2 ^ 59
def prefixEnd_5581260 : Nat := 4983230072969 + 3 ^ 40 * 5581260 * 2
def baseEnd_5581260 : Nat := 2865869037712938528282259

theorem tailTrace_5581260 : CollatzResearch.WordTrace tailWord_5581260 prefixEnd_5581260 2865869037712938528282259 := by
  unfold tailWord_5581260
  simp only [CollatzResearch.WordTrace]
  refine ⟨101782637880027849082358617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135710183840037132109811489 101782637880027849082358617)
  ·
    refine ⟨76336978410020886811768963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101782637880027849082358617 76336978410020886811768963)
    ·
      refine ⟨114505467615031330217653445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76336978410020886811768963 114505467615031330217653445)
      ·
        refine ⟨21469775177818374415810021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114505467615031330217653445 21469775177818374415810021)
        ·
          refine ⟨4025582845840945202964379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21469775177818374415810021 4025582845840945202964379)
          ·
            refine ⟨6038374268761417804446569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025582845840945202964379 6038374268761417804446569)
            ·
              refine ⟨4528780701571063353334927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6038374268761417804446569 4528780701571063353334927)
              ·
                refine ⟨6793171052356595030002391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528780701571063353334927 6793171052356595030002391)
                ·
                  refine ⟨10189756578534892545003587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6793171052356595030002391 10189756578534892545003587)
                  ·
                    refine ⟨15284634867802338817505381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10189756578534892545003587 15284634867802338817505381)
                    ·
                      refine ⟨2865869037712938528282259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15284634867802338817505381 2865869037712938528282259)
                      ·
                        rfl

theorem cell23_5581260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_5581260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581260 prefixEnd_5581260 := by exact prefixLift 5581260
  have htrace : WordTrace (prefixWord ++ tailWord_5581260) baseStart_5581260 baseEnd_5581260 := by
    simpa [prefixWord, tailWord_5581260, baseEnd_5581260] using wordTrace_append hprefix tailTrace_5581260
  have hstable : (prefixWord ++ tailWord_5581260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581260).length < 2 ^ (prefixWord ++ tailWord_5581260).sum := by decide
  have hdescent : baseEnd_5581260 < baseStart_5581260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581292 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_5581292 : Nat := 118140960795 + 5581292 * 2 ^ 59
def prefixEnd_5581292 : Nat := 4983230072969 + 3 ^ 40 * 5581292 * 2
def baseEnd_5581292 : Nat := 955295156364627467694037

theorem tailTrace_5581292 : CollatzResearch.WordTrace tailWord_5581292 prefixEnd_5581292 955295156364627467694037 := by
  unfold tailWord_5581292
  simp only [CollatzResearch.WordTrace]
  refine ⟨101783221447969883814941065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135710961930626511753254753 101783221447969883814941065)
  ·
    refine ⟨76337416085977412861205799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101783221447969883814941065 76337416085977412861205799)
    ·
      refine ⟨114506124128966119291808699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76337416085977412861205799 114506124128966119291808699)
      ·
        refine ⟨171759186193449178937713049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114506124128966119291808699 171759186193449178937713049)
        ·
          refine ⟨128819389645086884203284787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171759186193449178937713049 128819389645086884203284787)
          ·
            refine ⟨193229084467630326304927181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128819389645086884203284787 193229084467630326304927181)
            ·
              refine ⟨72460906675361372364347693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193229084467630326304927181 72460906675361372364347693)
              ·
                refine ⟨27172840003260514636630385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72460906675361372364347693 27172840003260514636630385)
                ·
                  refine ⟨20379630002445385977472789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27172840003260514636630385 20379630002445385977472789)
                  ·
                    refine ⟨955295156364627467694037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20379630002445385977472789 955295156364627467694037)
                    ·
                      rfl

theorem cell23_5581292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_5581292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581292 prefixEnd_5581292 := by exact prefixLift 5581292
  have htrace : WordTrace (prefixWord ++ tailWord_5581292) baseStart_5581292 baseEnd_5581292 := by
    simpa [prefixWord, tailWord_5581292, baseEnd_5581292] using wordTrace_append hprefix tailTrace_5581292
  have hstable : (prefixWord ++ tailWord_5581292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581292).length < 2 ^ (prefixWord ++ tailWord_5581292).sum := by decide
  have hdescent : baseEnd_5581292 < baseStart_5581292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581293 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_5581293 : Nat := 118140960795 + 5581293 * 2 ^ 59
def prefixEnd_5581293 : Nat := 4983230072969 + 3 ^ 40 * 5581293 * 2
def baseEnd_5581293 : Nat := 2865885982574536899169607

theorem tailTrace_5581293 : CollatzResearch.WordTrace tailWord_5581293 prefixEnd_5581293 2865885982574536899169607 := by
  unfold tailWord_5581293
  simp only [CollatzResearch.WordTrace]
  refine ⟨203566479368936144800668533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135710986245957429867112355 203566479368936144800668533)
  ·
    refine ⟨19084357440837763575062675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 203566479368936144800668533 19084357440837763575062675)
    ·
      refine ⟨28626536161256645362594013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19084357440837763575062675 28626536161256645362594013)
      ·
        refine ⟨10734951060471242010972755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28626536161256645362594013 10734951060471242010972755)
        ·
          refine ⟨16102426590706863016459133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10734951060471242010972755 16102426590706863016459133)
          ·
            refine ⟨6038409971515073631172175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16102426590706863016459133 6038409971515073631172175)
            ·
              refine ⟨9057614957272610446758263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6038409971515073631172175 9057614957272610446758263)
              ·
                refine ⟨13586422435908915670137395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9057614957272610446758263 13586422435908915670137395)
                ·
                  refine ⟨20379633653863373505206093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13586422435908915670137395 20379633653863373505206093)
                  ·
                    refine ⟨7642362620198765064452285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20379633653863373505206093 7642362620198765064452285)
                    ·
                      refine ⟨2865885982574536899169607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7642362620198765064452285 2865885982574536899169607)
                      ·
                        rfl

theorem cell23_5581293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_5581293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581293 prefixEnd_5581293 := by exact prefixLift 5581293
  have htrace : WordTrace (prefixWord ++ tailWord_5581293) baseStart_5581293 baseEnd_5581293 := by
    simpa [prefixWord, tailWord_5581293, baseEnd_5581293] using wordTrace_append hprefix tailTrace_5581293
  have hstable : (prefixWord ++ tailWord_5581293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581293).length < 2 ^ (prefixWord ++ tailWord_5581293).sum := by decide
  have hdescent : baseEnd_5581293 < baseStart_5581293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581333 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 2, 2, 2]
def baseStart_5581333 : Nat := 118140960795 + 5581333 * 2 ^ 59
def prefixEnd_5581333 : Nat := 4983230072969 + 3 ^ 40 * 5581333 * 2
def baseEnd_5581333 : Nat := 2865906521800716742669423

theorem tailTrace_5581333 : CollatzResearch.WordTrace tailWord_5581333 prefixEnd_5581333 2865906521800716742669423 := by
  unfold tailWord_5581333
  simp only [CollatzResearch.WordTrace]
  refine ⟨203567938288791231632124653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135711958859194154421416435 203567938288791231632124653)
  ·
    refine ⟨76337976858296711862046745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203567938288791231632124653 76337976858296711862046745)
    ·
      refine ⟨57253482643722533896535059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76337976858296711862046745 57253482643722533896535059)
      ·
        refine ⟨85880223965583800844802589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57253482643722533896535059 85880223965583800844802589)
        ·
          refine ⟨32205083987093925316800971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85880223965583800844802589 32205083987093925316800971)
          ·
            refine ⟨48307625980640887975201457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32205083987093925316800971 48307625980640887975201457)
            ·
              refine ⟨36230719485480665981401093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48307625980640887975201457 36230719485480665981401093)
              ·
                refine ⟨6793259903527624871512705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36230719485480665981401093 6793259903527624871512705)
                ·
                  refine ⟨5094944927645718653634529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6793259903527624871512705 5094944927645718653634529)
                  ·
                    refine ⟨3821208695734288990225897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5094944927645718653634529 3821208695734288990225897)
                    ·
                      refine ⟨2865906521800716742669423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3821208695734288990225897 2865906521800716742669423)
                      ·
                        rfl

theorem cell23_5581333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_5581333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581333 prefixEnd_5581333 := by exact prefixLift 5581333
  have htrace : WordTrace (prefixWord ++ tailWord_5581333) baseStart_5581333 baseEnd_5581333 := by
    simpa [prefixWord, tailWord_5581333, baseEnd_5581333] using wordTrace_append hprefix tailTrace_5581333
  have hstable : (prefixWord ++ tailWord_5581333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581333).length < 2 ^ (prefixWord ++ tailWord_5581333).sum := by decide
  have hdescent : baseEnd_5581333 < baseStart_5581333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581349 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 2, 3, 3]
def baseStart_5581349 : Nat := 118140960795 + 5581349 * 2 ^ 59
def prefixEnd_5581349 : Nat := 4983230072969 + 3 ^ 40 * 5581349 * 2
def baseEnd_5581349 : Nat := 2865914737491188680069349

theorem tailTrace_5581349 : CollatzResearch.WordTrace tailWord_5581349 prefixEnd_5581349 2865914737491188680069349 := by
  unfold tailWord_5581349
  simp only [CollatzResearch.WordTrace]
  refine ⟨203568521856733266364707101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135712347904488844243138067 203568521856733266364707101)
  ·
    refine ⟨76338195696274974886765163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203568521856733266364707101 76338195696274974886765163)
    ·
      refine ⟨114507293544412462330147745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76338195696274974886765163 114507293544412462330147745)
      ·
        refine ⟨85880470158309346747610809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114507293544412462330147745 85880470158309346747610809)
        ·
          refine ⟨64410352618732010060708107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85880470158309346747610809 64410352618732010060708107)
          ·
            refine ⟨96615528928098015091062161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64410352618732010060708107 96615528928098015091062161)
            ·
              refine ⟨72461646696073511318296621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96615528928098015091062161 72461646696073511318296621)
              ·
                refine ⟨27173117511027566744361233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72461646696073511318296621 27173117511027566744361233)
                ·
                  refine ⟨20379838133270675058270925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27173117511027566744361233 20379838133270675058270925)
                  ·
                    refine ⟨7642439299976503146851597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20379838133270675058270925 7642439299976503146851597)
                    ·
                      refine ⟨2865914737491188680069349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7642439299976503146851597 2865914737491188680069349)
                      ·
                        rfl

theorem cell23_5581349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_5581349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581349 prefixEnd_5581349 := by exact prefixLift 5581349
  have htrace : WordTrace (prefixWord ++ tailWord_5581349) baseStart_5581349 baseEnd_5581349 := by
    simpa [prefixWord, tailWord_5581349, baseEnd_5581349] using wordTrace_append hprefix tailTrace_5581349
  have hstable : (prefixWord ++ tailWord_5581349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581349).length < 2 ^ (prefixWord ++ tailWord_5581349).sum := by decide
  have hdescent : baseEnd_5581349 < baseStart_5581349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581433 : List Nat := [1, 2, 1, 3, 3, 2, 1, 5, 1, 4]
def baseStart_5581433 : Nat := 118140960795 + 5581433 * 2 ^ 59
def prefixEnd_5581433 : Nat := 4983230072969 + 3 ^ 40 * 5581433 * 2
def baseEnd_5581433 : Nat := 955319289955388783806321

theorem tailTrace_5581433 : CollatzResearch.WordTrace tailWord_5581433 prefixEnd_5581433 955319289955388783806321 := by
  unfold tailWord_5581433
  simp only [CollatzResearch.WordTrace]
  refine ⟨203571585588428948710764953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135714390392285965807176635 203571585588428948710764953)
  ·
    refine ⟨152678689191321711533073715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203571585588428948710764953 152678689191321711533073715)
    ·
      refine ⟨229018033786982567299610573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152678689191321711533073715 229018033786982567299610573)
      ·
        refine ⟨85881762670118462737353965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229018033786982567299610573 85881762670118462737353965)
        ·
          refine ⟨32205661001294423526507737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85881762670118462737353965 32205661001294423526507737)
          ·
            refine ⟨24154245750970817644880803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32205661001294423526507737 24154245750970817644880803)
            ·
              refine ⟨36231368626456226467321205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24154245750970817644880803 36231368626456226467321205)
              ·
                refine ⟨3396690808730271231311363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36231368626456226467321205 3396690808730271231311363)
                ·
                  refine ⟨5095036213095406846967045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396690808730271231311363 5095036213095406846967045)
                  ·
                    refine ⟨955319289955388783806321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5095036213095406846967045 955319289955388783806321)
                    ·
                      rfl

theorem cell23_5581433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 1, 4].length) (baseStart_5581433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581433 prefixEnd_5581433 := by exact prefixLift 5581433
  have htrace : WordTrace (prefixWord ++ tailWord_5581433) baseStart_5581433 baseEnd_5581433 := by
    simpa [prefixWord, tailWord_5581433, baseEnd_5581433] using wordTrace_append hprefix tailTrace_5581433
  have hstable : (prefixWord ++ tailWord_5581433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581433).length < 2 ^ (prefixWord ++ tailWord_5581433).sum := by decide
  have hdescent : baseEnd_5581433 < baseStart_5581433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581469 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_5581469 : Nat := 118140960795 + 5581469 * 2 ^ 59
def prefixEnd_5581469 : Nat := 4983230072969 + 3 ^ 40 * 5581469 * 2
def baseEnd_5581469 : Nat := 2865976355169728210568797

theorem tailTrace_5581469 : CollatzResearch.WordTrace tailWord_5581469 prefixEnd_5581469 2865976355169728210568797 := by
  unfold tailWord_5581469
  simp only [CollatzResearch.WordTrace]
  refine ⟨203572898616298526859075461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135715265744199017906050307 203572898616298526859075461)
  ·
    refine ⟨38169918490555973786076649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 203572898616298526859075461 38169918490555973786076649)
    ·
      refine ⟨28627438867916980339557487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38169918490555973786076649 28627438867916980339557487)
      ·
        refine ⟨42941158301875470509336231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28627438867916980339557487 42941158301875470509336231)
        ·
          refine ⟨64411737452813205764004347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42941158301875470509336231 64411737452813205764004347)
          ·
            refine ⟨96617606179219808646006521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64411737452813205764004347 96617606179219808646006521)
            ·
              refine ⟨72463204634414856484504891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96617606179219808646006521 72463204634414856484504891)
              ·
                refine ⟨108694806951622284726757337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72463204634414856484504891 108694806951622284726757337)
                ·
                  refine ⟨81521105213716713545068003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108694806951622284726757337 81521105213716713545068003)
                  ·
                    refine ⟨122281657820575070317602005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81521105213716713545068003 122281657820575070317602005)
                    ·
                      refine ⟨2865976355169728210568797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122281657820575070317602005 2865976355169728210568797)
                      ·
                        rfl

theorem cell23_5581469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_5581469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581469 prefixEnd_5581469 := by exact prefixLift 5581469
  have htrace : WordTrace (prefixWord ++ tailWord_5581469) baseStart_5581469 baseEnd_5581469 := by
    simpa [prefixWord, tailWord_5581469, baseEnd_5581469] using wordTrace_append hprefix tailTrace_5581469
  have hstable : (prefixWord ++ tailWord_5581469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581469).length < 2 ^ (prefixWord ++ tailWord_5581469).sum := by decide
  have hdescent : baseEnd_5581469 < baseStart_5581469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581493 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 1, 5]
def baseStart_5581493 : Nat := 118140960795 + 5581493 * 2 ^ 59
def prefixEnd_5581493 : Nat := 4983230072969 + 3 ^ 40 * 5581493 * 2
def baseEnd_5581493 : Nat := 955329559568478705556229

theorem tailTrace_5581493 : CollatzResearch.WordTrace tailWord_5581493 prefixEnd_5581493 955329559568478705556229 := by
  unfold tailWord_5581493
  simp only [CollatzResearch.WordTrace]
  refine ⟨203573773968211578957949133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135715849312141052638632755 203573773968211578957949133)
  ·
    refine ⟨76340165238079342109230925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203573773968211578957949133 76340165238079342109230925)
    ·
      refine ⟨28627561964279753290961597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76340165238079342109230925 28627561964279753290961597)
      ·
        refine ⟨10735335736604907484110599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28627561964279753290961597 10735335736604907484110599)
        ·
          refine ⟨16103003604907361226165899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10735335736604907484110599 16103003604907361226165899)
          ·
            refine ⟨24154505407361041839248849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16103003604907361226165899 24154505407361041839248849)
            ·
              refine ⟨18115879055520781379436637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24154505407361041839248849 18115879055520781379436637)
              ·
                refine ⟨6793454645820293017288739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18115879055520781379436637 6793454645820293017288739)
                ·
                  refine ⟨10190181968730439525933109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6793454645820293017288739 10190181968730439525933109)
                  ·
                    refine ⟨955329559568478705556229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10190181968730439525933109 955329559568478705556229)
                    ·
                      rfl

theorem cell23_5581493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_5581493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581493 prefixEnd_5581493 := by exact prefixLift 5581493
  have htrace : WordTrace (prefixWord ++ tailWord_5581493) baseStart_5581493 baseEnd_5581493 := by
    simpa [prefixWord, tailWord_5581493, baseEnd_5581493] using wordTrace_append hprefix tailTrace_5581493
  have hstable : (prefixWord ++ tailWord_5581493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581493).length < 2 ^ (prefixWord ++ tailWord_5581493).sum := by decide
  have hdescent : baseEnd_5581493 < baseStart_5581493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581509 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_5581509 : Nat := 118140960795 + 5581509 * 2 ^ 59
def prefixEnd_5581509 : Nat := 4983230072969 + 3 ^ 40 * 5581509 * 2
def baseEnd_5581509 : Nat := 2865996894395908054068613

theorem tailTrace_5581509 : CollatzResearch.WordTrace tailWord_5581509 prefixEnd_5581509 2865996894395908054068613 := by
  unfold tailWord_5581509
  simp only [CollatzResearch.WordTrace]
  refine ⟨203574357536153613690531581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135716238357435742460354387 203574357536153613690531581)
  ·
    refine ⟨76340384076057605133949343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203574357536153613690531581 76340384076057605133949343)
    ·
      refine ⟨114510576114086407700924015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76340384076057605133949343 114510576114086407700924015)
      ·
        refine ⟨171765864171129611551386023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114510576114086407700924015 171765864171129611551386023)
        ·
          refine ⟨257648796256694417327079035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171765864171129611551386023 257648796256694417327079035)
          ·
            refine ⟨386473194385041625990618553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257648796256694417327079035 386473194385041625990618553)
            ·
              refine ⟨289854895788781219492963915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386473194385041625990618553 289854895788781219492963915)
              ·
                refine ⟨434782343683171829239445873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289854895788781219492963915 434782343683171829239445873)
                ·
                  refine ⟨326086757762378871929584405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 434782343683171829239445873 326086757762378871929584405)
                  ·
                    refine ⟨15285316770111509621699269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 326086757762378871929584405 15285316770111509621699269)
                    ·
                      refine ⟨2865996894395908054068613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15285316770111509621699269 2865996894395908054068613)
                      ·
                        rfl

theorem cell23_5581509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_5581509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581509 prefixEnd_5581509 := by exact prefixLift 5581509
  have htrace : WordTrace (prefixWord ++ tailWord_5581509) baseStart_5581509 baseEnd_5581509 := by
    simpa [prefixWord, tailWord_5581509, baseEnd_5581509] using wordTrace_append hprefix tailTrace_5581509
  have hstable : (prefixWord ++ tailWord_5581509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581509).length < 2 ^ (prefixWord ++ tailWord_5581509).sum := by decide
  have hdescent : baseEnd_5581509 < baseStart_5581509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581564 : List Nat := [2, 2, 2, 1, 3, 2, 4, 2, 1, 2, 2]
def baseStart_5581564 : Nat := 118140960795 + 5581564 * 2 ^ 59
def prefixEnd_5581564 : Nat := 4983230072969 + 3 ^ 40 * 5581564 * 2
def baseEnd_5581564 : Nat := 2866025135831905338880861

theorem tailTrace_5581564 : CollatzResearch.WordTrace tailWord_5581564 prefixEnd_5581564 2866025135831905338880861 := by
  unfold tailWord_5581564
  simp only [CollatzResearch.WordTrace]
  refine ⟨101788181775477179041891873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135717575700636238722522497 101788181775477179041891873)
  ·
    refine ⟨76341136331607884281418905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101788181775477179041891873 76341136331607884281418905)
    ·
      refine ⟨57255852248705913211064179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76341136331607884281418905 57255852248705913211064179)
      ·
        refine ⟨85883778373058869816596269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57255852248705913211064179 85883778373058869816596269)
        ·
          refine ⟨32206416889897076181223601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85883778373058869816596269 32206416889897076181223601)
          ·
            refine ⟨24154812667422807135917701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32206416889897076181223601 24154812667422807135917701)
            ·
              refine ⟨4529027375141776337984569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24154812667422807135917701 4529027375141776337984569)
              ·
                refine ⟨3396770531356332253488427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4529027375141776337984569 3396770531356332253488427)
                ·
                  refine ⟨5095155797034498380232641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3396770531356332253488427 5095155797034498380232641)
                  ·
                    refine ⟨3821366847775873785174481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5095155797034498380232641 3821366847775873785174481)
                    ·
                      refine ⟨2866025135831905338880861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3821366847775873785174481 2866025135831905338880861)
                      ·
                        rfl

theorem cell23_5581564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_5581564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581564 prefixEnd_5581564 := by exact prefixLift 5581564
  have htrace : WordTrace (prefixWord ++ tailWord_5581564) baseStart_5581564 baseEnd_5581564 := by
    simpa [prefixWord, tailWord_5581564, baseEnd_5581564] using wordTrace_append hprefix tailTrace_5581564
  have hstable : (prefixWord ++ tailWord_5581564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581564).length < 2 ^ (prefixWord ++ tailWord_5581564).sum := by decide
  have hdescent : baseEnd_5581564 < baseStart_5581564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581614 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_5581614 : Nat := 118140960795 + 5581614 * 2 ^ 59
def prefixEnd_5581614 : Nat := 4983230072969 + 3 ^ 40 * 5581614 * 2
def baseEnd_5581614 : Nat := 2866050809864630143255631

theorem tailTrace_5581614 : CollatzResearch.WordTrace tailWord_5581614 prefixEnd_5581614 2866050809864630143255631 := by
  unfold tailWord_5581614
  simp only [CollatzResearch.WordTrace]
  refine ⟨25447273400096652077887987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135718791467182144415402597 25447273400096652077887987)
  ·
    refine ⟨38170910100144978116831981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25447273400096652077887987 38170910100144978116831981)
    ·
      refine ⟨14314091287554366793811993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38170910100144978116831981 14314091287554366793811993)
      ·
        refine ⟨10735568465665775095358995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14314091287554366793811993 10735568465665775095358995)
        ·
          refine ⟨16103352698498662643038493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10735568465665775095358995 16103352698498662643038493)
          ·
            refine ⟨6038757261936998491139435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16103352698498662643038493 6038757261936998491139435)
            ·
              refine ⟨9058135892905497736709153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6038757261936998491139435 9058135892905497736709153)
              ·
                refine ⟨6793601919679123302531865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9058135892905497736709153 6793601919679123302531865)
                ·
                  refine ⟨5095201439759342476898899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6793601919679123302531865 5095201439759342476898899)
                  ·
                    refine ⟨7642802159639013715348349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5095201439759342476898899 7642802159639013715348349)
                    ·
                      refine ⟨2866050809864630143255631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7642802159639013715348349 2866050809864630143255631)
                      ·
                        rfl

theorem cell23_5581614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_5581614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581614 prefixEnd_5581614 := by exact prefixLift 5581614
  have htrace : WordTrace (prefixWord ++ tailWord_5581614) baseStart_5581614 baseEnd_5581614 := by
    simpa [prefixWord, tailWord_5581614, baseEnd_5581614] using wordTrace_append hprefix tailTrace_5581614
  have hstable : (prefixWord ++ tailWord_5581614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581614).length < 2 ^ (prefixWord ++ tailWord_5581614).sum := by decide
  have hdescent : baseEnd_5581614 < baseStart_5581614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581656 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 6, 5]
def baseStart_5581656 : Nat := 118140960795 + 5581656 * 2 ^ 59
def prefixEnd_5581656 : Nat := 4983230072969 + 3 ^ 40 * 5581656 * 2
def baseEnd_5581656 : Nat := 955357458684039659643479

theorem tailTrace_5581656 : CollatzResearch.WordTrace tailWord_5581656 prefixEnd_5581656 955357458684039659643479 := by
  unfold tailWord_5581656
  simp only [CollatzResearch.WordTrace]
  refine ⟨101789859533310528898066411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135719812711080705197421881 101789859533310528898066411)
  ·
    refine ⟨152684789299965793347099617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101789859533310528898066411 152684789299965793347099617)
    ·
      refine ⟨114513591974974345010324713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152684789299965793347099617 114513591974974345010324713)
      ·
        refine ⟨85885193981230758757743535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114513591974974345010324713 85885193981230758757743535)
        ·
          refine ⟨128827790971846138136615303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85885193981230758757743535 128827790971846138136615303)
          ·
            refine ⟨193241686457769207204922955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128827790971846138136615303 193241686457769207204922955)
            ·
              refine ⟨289862529686653810807384433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193241686457769207204922955 289862529686653810807384433)
              ·
                refine ⟨217396897264990358105538325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289862529686653810807384433 217396897264990358105538325)
                ·
                  refine ⟨10190479559296423036197109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 217396897264990358105538325 10190479559296423036197109)
                  ·
                    refine ⟨955357458684039659643479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10190479559296423036197109 955357458684039659643479)
                    ·
                      rfl

theorem cell23_5581656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_5581656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581656 prefixEnd_5581656 := by exact prefixLift 5581656
  have htrace : WordTrace (prefixWord ++ tailWord_5581656) baseStart_5581656 baseEnd_5581656 := by
    simpa [prefixWord, tailWord_5581656, baseEnd_5581656] using wordTrace_append hprefix tailTrace_5581656
  have hstable : (prefixWord ++ tailWord_5581656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581656).length < 2 ^ (prefixWord ++ tailWord_5581656).sum := by decide
  have hdescent : baseEnd_5581656 < baseStart_5581656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581760 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 5, 1, 3]
def baseStart_5581760 : Nat := 118140960795 + 5581760 * 2 ^ 59
def prefixEnd_5581760 : Nat := 4983230072969 + 3 ^ 40 * 5581760 * 2
def baseEnd_5581760 : Nat := 2866125778040186572029959

theorem tailTrace_5581760 : CollatzResearch.WordTrace tailWord_5581760 prefixEnd_5581760 2866125778040186572029959 := by
  unfold tailWord_5581760
  simp only [CollatzResearch.WordTrace]
  refine ⟨101791756129122141778959367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135722341505496189038612489 101791756129122141778959367)
  ·
    refine ⟨152687634193683212668439051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101791756129122141778959367 152687634193683212668439051)
    ·
      refine ⟨229031451290524819002658577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152687634193683212668439051 229031451290524819002658577)
      ·
        refine ⟨171773588467893614251993933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 229031451290524819002658577 171773588467893614251993933)
        ·
          refine ⟨64415095675460105344497725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171773588467893614251993933 64415095675460105344497725)
          ·
            refine ⟨24155660878297539504186647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64415095675460105344497725 24155660878297539504186647)
            ·
              refine ⟨36233491317446309256279971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24155660878297539504186647 36233491317446309256279971)
              ·
                refine ⟨54350236976169463884419957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36233491317446309256279971 54350236976169463884419957)
                ·
                  refine ⟨5095334716515887239164371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54350236976169463884419957 5095334716515887239164371)
                  ·
                    refine ⟨7643002074773830858746557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5095334716515887239164371 7643002074773830858746557)
                    ·
                      refine ⟨2866125778040186572029959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7643002074773830858746557 2866125778040186572029959)
                      ·
                        rfl

theorem cell23_5581760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_5581760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581760 prefixEnd_5581760 := by exact prefixLift 5581760
  have htrace : WordTrace (prefixWord ++ tailWord_5581760) baseStart_5581760 baseEnd_5581760 := by
    simpa [prefixWord, tailWord_5581760, baseEnd_5581760] using wordTrace_append hprefix tailTrace_5581760
  have hstable : (prefixWord ++ tailWord_5581760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581760).length < 2 ^ (prefixWord ++ tailWord_5581760).sum := by decide
  have hdescent : baseEnd_5581760 < baseStart_5581760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581783 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_5581783 : Nat := 118140960795 + 5581783 * 2 ^ 59
def prefixEnd_5581783 : Nat := 4983230072969 + 3 ^ 40 * 5581783 * 2
def baseEnd_5581783 : Nat := 2866137588095239982042353

theorem tailTrace_5581783 : CollatzResearch.WordTrace tailWord_5581783 prefixEnd_5581783 2866137588095239982042353 := by
  unfold tailWord_5581783
  simp only [CollatzResearch.WordTrace]
  refine ⟨203584351137160958486006003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135722900758107305657337335 203584351137160958486006003)
  ·
    refine ⟨305376526705741437729009005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203584351137160958486006003 305376526705741437729009005)
    ·
      refine ⟨114516197514653039148378377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 305376526705741437729009005 114516197514653039148378377)
      ·
        refine ⟨85887148135989779361283783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114516197514653039148378377 85887148135989779361283783)
        ·
          refine ⟨128830722203984669041925675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85887148135989779361283783 128830722203984669041925675)
          ·
            refine ⟨193246083305977003562888513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128830722203984669041925675 193246083305977003562888513)
            ·
              refine ⟨144934562479482752672166385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193246083305977003562888513 144934562479482752672166385)
              ·
                refine ⟨108700921859612064504124789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144934562479482752672166385 108700921859612064504124789)
                ·
                  refine ⟨10190711424338631047261699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108700921859612064504124789 10190711424338631047261699)
                  ·
                    refine ⟨15286067136507946570892549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10190711424338631047261699 15286067136507946570892549)
                    ·
                      refine ⟨2866137588095239982042353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15286067136507946570892549 2866137588095239982042353)
                      ·
                        rfl

theorem cell23_5581783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_5581783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581783 prefixEnd_5581783 := by exact prefixLift 5581783
  have htrace : WordTrace (prefixWord ++ tailWord_5581783) baseStart_5581783 baseEnd_5581783 := by
    simpa [prefixWord, tailWord_5581783, baseEnd_5581783] using wordTrace_append hprefix tailTrace_5581783
  have hstable : (prefixWord ++ tailWord_5581783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581783).length < 2 ^ (prefixWord ++ tailWord_5581783).sum := by decide
  have hdescent : baseEnd_5581783 < baseStart_5581783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581794 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_5581794 : Nat := 118140960795 + 5581794 * 2 ^ 59
def prefixEnd_5581794 : Nat := 4983230072969 + 3 ^ 40 * 5581794 * 2
def baseEnd_5581794 : Nat := 2866143236382439439004803

theorem tailTrace_5581794 : CollatzResearch.WordTrace tailWord_5581794 prefixEnd_5581794 2866143236382439439004803 := by
  unfold tailWord_5581794
  simp only [CollatzResearch.WordTrace]
  refine ⟨50896188085030276841164109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135723168226747404909770957 50896188085030276841164109)
  ·
    refine ⟨19086070531886353815436541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50896188085030276841164109 19086070531886353815436541)
    ·
      refine ⟨7157276449457382680788703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19086070531886353815436541 7157276449457382680788703)
      ·
        refine ⟨10735914674186074021183055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7157276449457382680788703 10735914674186074021183055)
        ·
          refine ⟨16103872011279111031774583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10735914674186074021183055 16103872011279111031774583)
          ·
            refine ⟨24155808016918666547661875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16103872011279111031774583 24155808016918666547661875)
            ·
              refine ⟨36233712025377999821492813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24155808016918666547661875 36233712025377999821492813)
              ·
                refine ⟨13587642009516749933059805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36233712025377999821492813 13587642009516749933059805)
                ·
                  refine ⟨5095365753568781224897427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13587642009516749933059805 5095365753568781224897427)
                  ·
                    refine ⟨7643048630353171837346141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5095365753568781224897427 7643048630353171837346141)
                    ·
                      refine ⟨2866143236382439439004803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7643048630353171837346141 2866143236382439439004803)
                      ·
                        rfl

theorem cell23_5581794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_5581794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581794 prefixEnd_5581794 := by exact prefixLift 5581794
  have htrace : WordTrace (prefixWord ++ tailWord_5581794) baseStart_5581794 baseEnd_5581794 := by
    simpa [prefixWord, tailWord_5581794, baseEnd_5581794] using wordTrace_append hprefix tailTrace_5581794
  have hstable : (prefixWord ++ tailWord_5581794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581794).length < 2 ^ (prefixWord ++ tailWord_5581794).sum := by decide
  have hdescent : baseEnd_5581794 < baseStart_5581794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581817 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 3, 2, 2]
def baseStart_5581817 : Nat := 118140960795 + 5581817 * 2 ^ 59
def prefixEnd_5581817 : Nat := 4983230072969 + 3 ^ 40 * 5581817 * 2
def baseEnd_5581817 : Nat := 2866155046437492849017197

theorem tailTrace_5581817 : CollatzResearch.WordTrace tailWord_5581817 prefixEnd_5581817 2866155046437492849017197 := by
  unfold tailWord_5581817
  simp only [CollatzResearch.WordTrace]
  refine ⟨203585591219037782292743705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135723727479358521528495803 203585591219037782292743705)
  ·
    refine ⟨152689193414278336719557779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 203585591219037782292743705 152689193414278336719557779)
    ·
      refine ⟨229033790121417505079336669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152689193414278336719557779 229033790121417505079336669)
      ·
        refine ⟨85887671295531564404751251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229033790121417505079336669 85887671295531564404751251)
        ·
          refine ⟨128831506943297346607126877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85887671295531564404751251 128831506943297346607126877)
          ·
            refine ⟨48311815103736504977672579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128831506943297346607126877 48311815103736504977672579)
            ·
              refine ⟨72467722655604757466508869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48311815103736504977672579 72467722655604757466508869)
              ·
                refine ⟨13587697997925892024970413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72467722655604757466508869 13587697997925892024970413)
                ·
                  refine ⟨5095386749222209509363905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13587697997925892024970413 5095386749222209509363905)
                  ·
                    refine ⟨3821540061916657132022929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5095386749222209509363905 3821540061916657132022929)
                    ·
                      refine ⟨2866155046437492849017197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3821540061916657132022929 2866155046437492849017197)
                      ·
                        rfl

theorem cell23_5581817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_5581817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581817 prefixEnd_5581817 := by exact prefixLift 5581817
  have htrace : WordTrace (prefixWord ++ tailWord_5581817) baseStart_5581817 baseEnd_5581817 := by
    simpa [prefixWord, tailWord_5581817, baseEnd_5581817] using wordTrace_append hprefix tailTrace_5581817
  have hstable : (prefixWord ++ tailWord_5581817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581817).length < 2 ^ (prefixWord ++ tailWord_5581817).sum := by decide
  have hdescent : baseEnd_5581817 < baseStart_5581817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581867 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 2, 1, 3]
def baseStart_5581867 : Nat := 118140960795 + 5581867 * 2 ^ 59
def prefixEnd_5581867 : Nat := 4983230072969 + 3 ^ 40 * 5581867 * 2
def baseEnd_5581867 : Nat := 2866180720470217653391967

theorem tailTrace_5581867 : CollatzResearch.WordTrace tailWord_5581867 prefixEnd_5581867 2866180720470217653391967 := by
  unfold tailWord_5581867
  simp only [CollatzResearch.WordTrace]
  refine ⟨203587414868856640832063855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135724943245904427221375903 203587414868856640832063855)
  ·
    refine ⟨305381122303284961248095783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 203587414868856640832063855 305381122303284961248095783)
    ·
      refine ⟨458071683454927441872143675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305381122303284961248095783 458071683454927441872143675)
      ·
        refine ⟨687107525182391162808215513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458071683454927441872143675 687107525182391162808215513)
        ·
          refine ⟨515330643886793372106161635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 687107525182391162808215513 515330643886793372106161635)
          ·
            refine ⟨772995965830190058159242453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515330643886793372106161635 772995965830190058159242453)
            ·
              refine ⟨18117092949145079488107245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 772995965830190058159242453 18117092949145079488107245)
              ·
                refine ⟨6793909855929404808040217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18117092949145079488107245 6793909855929404808040217)
                ·
                  refine ⟨5095432391947053606030163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6793909855929404808040217 5095432391947053606030163)
                  ·
                    refine ⟨7643148587920580409045245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5095432391947053606030163 7643148587920580409045245)
                    ·
                      refine ⟨2866180720470217653391967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7643148587920580409045245 2866180720470217653391967)
                      ·
                        rfl

theorem cell23_5581867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 1, 3].length) (baseStart_5581867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581867 prefixEnd_5581867 := by exact prefixLift 5581867
  have htrace : WordTrace (prefixWord ++ tailWord_5581867) baseStart_5581867 baseEnd_5581867 := by
    simpa [prefixWord, tailWord_5581867, baseEnd_5581867] using wordTrace_append hprefix tailTrace_5581867
  have hstable : (prefixWord ++ tailWord_5581867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581867).length < 2 ^ (prefixWord ++ tailWord_5581867).sum := by decide
  have hdescent : baseEnd_5581867 < baseStart_5581867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581901 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_5581901 : Nat := 118140960795 + 5581901 * 2 ^ 59
def prefixEnd_5581901 : Nat := 4983230072969 + 3 ^ 40 * 5581901 * 2
def baseEnd_5581901 : Nat := 2866198178812470520366811

theorem tailTrace_5581901 : CollatzResearch.WordTrace tailWord_5581901 prefixEnd_5581901 2866198178812470520366811 := by
  unfold tailWord_5581901
  simp only [CollatzResearch.WordTrace]
  refine ⟨203588654950733464638801557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 135725769967155643092534371 203588654950733464638801557)
  ·
    refine ⟨9543218200815631154943823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 203588654950733464638801557 9543218200815631154943823)
    ·
      refine ⟨14314827301223446732415735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9543218200815631154943823 14314827301223446732415735)
      ·
        refine ⟨21472240951835170098623603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14314827301223446732415735 21472240951835170098623603)
        ·
          refine ⟨32208361427752755147935405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21472240951835170098623603 32208361427752755147935405)
          ·
            refine ⟨12078135535407283180475777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32208361427752755147935405 12078135535407283180475777)
            ·
              refine ⟨9058601651555462385356833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12078135535407283180475777 9058601651555462385356833)
              ·
                refine ⟨6793951238666596789017625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9058601651555462385356833 6793951238666596789017625)
                ·
                  refine ⟨5095463428999947591763219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6793951238666596789017625 5095463428999947591763219)
                  ·
                    refine ⟨7643195143499921387644829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5095463428999947591763219 7643195143499921387644829)
                    ·
                      refine ⟨2866198178812470520366811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7643195143499921387644829 2866198178812470520366811)
                      ·
                        rfl

theorem cell23_5581901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_5581901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581901 prefixEnd_5581901 := by exact prefixLift 5581901
  have htrace : WordTrace (prefixWord ++ tailWord_5581901) baseStart_5581901 baseEnd_5581901 := by
    simpa [prefixWord, tailWord_5581901, baseEnd_5581901] using wordTrace_append hprefix tailTrace_5581901
  have hstable : (prefixWord ++ tailWord_5581901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581901).length < 2 ^ (prefixWord ++ tailWord_5581901).sum := by decide
  have hdescent : baseEnd_5581901 < baseStart_5581901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581918 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_5581918 : Nat := 118140960795 + 5581918 * 2 ^ 59
def prefixEnd_5581918 : Nat := 4983230072969 + 3 ^ 40 * 5581918 * 2
def baseEnd_5581918 : Nat := 2866206907983596953854233

theorem tailTrace_5581918 : CollatzResearch.WordTrace tailWord_5581918 prefixEnd_5581918 2866206907983596953854233 := by
  unfold tailWord_5581918
  simp only [CollatzResearch.WordTrace]
  refine ⟨25448659373958984567771301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135726183327781251028113605 25448659373958984567771301)
  ·
    refine ⟨4771623632617309606457119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25448659373958984567771301 4771623632617309606457119)
    ·
      refine ⟨7157435448925964409685679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4771623632617309606457119 7157435448925964409685679)
      ·
        refine ⟨10736153173388946614528519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7157435448925964409685679 10736153173388946614528519)
        ·
          refine ⟨16104229760083419921792779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10736153173388946614528519 16104229760083419921792779)
          ·
            refine ⟨24156344640125129882689169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16104229760083419921792779 24156344640125129882689169)
            ·
              refine ⟨18117258480093847412016877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24156344640125129882689169 18117258480093847412016877)
              ·
                refine ⟨6793971930035192779506329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18117258480093847412016877 6793971930035192779506329)
                ·
                  refine ⟨5095478947526394584629747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6793971930035192779506329 5095478947526394584629747)
                  ·
                    refine ⟨7643218421289591876944621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5095478947526394584629747 7643218421289591876944621)
                    ·
                      refine ⟨2866206907983596953854233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7643218421289591876944621 2866206907983596953854233)
                      ·
                        rfl

theorem cell23_5581918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_5581918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581918 prefixEnd_5581918 := by exact prefixLift 5581918
  have htrace : WordTrace (prefixWord ++ tailWord_5581918) baseStart_5581918 baseEnd_5581918 := by
    simpa [prefixWord, tailWord_5581918, baseEnd_5581918] using wordTrace_append hprefix tailTrace_5581918
  have hstable : (prefixWord ++ tailWord_5581918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581918).length < 2 ^ (prefixWord ++ tailWord_5581918).sum := by decide
  have hdescent : baseEnd_5581918 < baseStart_5581918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581920 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 4]
def baseStart_5581920 : Nat := 118140960795 + 5581920 * 2 ^ 59
def prefixEnd_5581920 : Nat := 4983230072969 + 3 ^ 40 * 5581920 * 2
def baseEnd_5581920 : Nat := 2866207934944905946029223

theorem tailTrace_5581920 : CollatzResearch.WordTrace tailWord_5581920 prefixEnd_5581920 2866207934944905946029223 := by
  unfold tailWord_5581920
  simp only [CollatzResearch.WordTrace]
  refine ⟨101794673968832315441871607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135726231958443087255828809 101794673968832315441871607)
  ·
    refine ⟨152692010953248473162807411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101794673968832315441871607 152692010953248473162807411)
    ·
      refine ⟨229038016429872709744211117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152692010953248473162807411 229038016429872709744211117)
      ·
        refine ⟨85889256161202266154079169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 229038016429872709744211117 85889256161202266154079169)
        ·
          refine ⟨64416942120901699615559377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85889256161202266154079169 64416942120901699615559377)
          ·
            refine ⟨48312706590676274711669533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64416942120901699615559377 48312706590676274711669533)
            ·
              refine ⟨18117264971503603016876075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48312706590676274711669533 18117264971503603016876075)
              ·
                refine ⟨27175897457255404525314113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18117264971503603016876075 27175897457255404525314113)
                ·
                  refine ⟨20381923092941553393985585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27175897457255404525314113 20381923092941553393985585)
                  ·
                    refine ⟨15286442319706165045489189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20381923092941553393985585 15286442319706165045489189)
                    ·
                      refine ⟨2866207934944905946029223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15286442319706165045489189 2866207934944905946029223)
                      ·
                        rfl

theorem cell23_5581920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_5581920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581920 prefixEnd_5581920 := by exact prefixLift 5581920
  have htrace : WordTrace (prefixWord ++ tailWord_5581920) baseStart_5581920 baseEnd_5581920 := by
    simpa [prefixWord, tailWord_5581920, baseEnd_5581920] using wordTrace_append hprefix tailTrace_5581920
  have hstable : (prefixWord ++ tailWord_5581920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581920).length < 2 ^ (prefixWord ++ tailWord_5581920).sum := by decide
  have hdescent : baseEnd_5581920 < baseStart_5581920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5581930 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 9]
def baseStart_5581930 : Nat := 118140960795 + 5581930 * 2 ^ 59
def prefixEnd_5581930 : Nat := 4983230072969 + 3 ^ 40 * 5581930 * 2
def baseEnd_5581930 : Nat := 318468118861272322989353

theorem tailTrace_5581930 : CollatzResearch.WordTrace tailWord_5581930 prefixEnd_5581930 318468118861272322989353 := by
  unfold tailWord_5581930
  simp only [CollatzResearch.WordTrace]
  refine ⟨50897428166907100647901811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 135726475111752268394404829 50897428166907100647901811)
  ·
    refine ⟨76346142250360650971852717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50897428166907100647901811 76346142250360650971852717)
    ·
      refine ⟨28629803343885244114444769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76346142250360650971852717 28629803343885244114444769)
      ·
        refine ⟨21472352507913933085833577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28629803343885244114444769 21472352507913933085833577)
        ·
          refine ⟨16104264380935449814375183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21472352507913933085833577 16104264380935449814375183)
          ·
            refine ⟨24156396571403174721562775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16104264380935449814375183 24156396571403174721562775)
            ·
              refine ⟨36234594857104762082344163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24156396571403174721562775 36234594857104762082344163)
              ·
                refine ⟨54351892285657143123516245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36234594857104762082344163 54351892285657143123516245)
                ·
                  refine ⟨318468118861272322989353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54351892285657143123516245 318468118861272322989353)
                  ·
                    rfl

theorem cell23_5581930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_5581930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5581930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5581930 prefixEnd_5581930 := by exact prefixLift 5581930
  have htrace : WordTrace (prefixWord ++ tailWord_5581930) baseStart_5581930 baseEnd_5581930 := by
    simpa [prefixWord, tailWord_5581930, baseEnd_5581930] using wordTrace_append hprefix tailTrace_5581930
  have hstable : (prefixWord ++ tailWord_5581930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5581930).length < 2 ^ (prefixWord ++ tailWord_5581930).sum := by decide
  have hdescent : baseEnd_5581930 < baseStart_5581930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5581930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582014 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_5582014 : Nat := 118140960795 + 5582014 * 2 ^ 59
def prefixEnd_5582014 : Nat := 4983230072969 + 3 ^ 40 * 5582014 * 2
def baseEnd_5582014 : Nat := 2866256202126428578253791

theorem tailTrace_5582014 : CollatzResearch.WordTrace tailWord_5582014 prefixEnd_5582014 2866256202126428578253791 := by
  unfold tailWord_5582014
  simp only [CollatzResearch.WordTrace]
  refine ⟨25449097049915510617208137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 135728517599549389958443397 25449097049915510617208137)
  ·
    refine ⟨19086822787436632962906103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25449097049915510617208137 19086822787436632962906103)
    ·
      refine ⟨28630234181154949444359155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19086822787436632962906103 28630234181154949444359155)
      ·
        refine ⟨42945351271732424166538733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28630234181154949444359155 42945351271732424166538733)
        ·
          refine ⟨16104506726899659062452025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42945351271732424166538733 16104506726899659062452025)
          ·
            refine ⟨12078380045174744296839019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16104506726899659062452025 12078380045174744296839019)
            ·
              refine ⟨18117570067762116445258529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12078380045174744296839019 18117570067762116445258529)
              ·
                refine ⟨13588177550821587333943897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18117570067762116445258529 13588177550821587333943897)
                ·
                  refine ⟨10191133163116190500457923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13588177550821587333943897 10191133163116190500457923)
                  ·
                    refine ⟨15286699744674285750686885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10191133163116190500457923 15286699744674285750686885)
                    ·
                      refine ⟨2866256202126428578253791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15286699744674285750686885 2866256202126428578253791)
                      ·
                        rfl

theorem cell23_5582014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_5582014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582014 prefixEnd_5582014 := by exact prefixLift 5582014
  have htrace : WordTrace (prefixWord ++ tailWord_5582014) baseStart_5582014 baseEnd_5582014 := by
    simpa [prefixWord, tailWord_5582014, baseEnd_5582014] using wordTrace_append hprefix tailTrace_5582014
  have hstable : (prefixWord ++ tailWord_5582014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582014).length < 2 ^ (prefixWord ++ tailWord_5582014).sum := by decide
  have hdescent : baseEnd_5582014 < baseStart_5582014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5582024 : List Nat := [2, 1, 3, 1, 2, 1, 2, 6, 1, 4]
def baseStart_5582024 : Nat := 118140960795 + 5582024 * 2 ^ 59
def prefixEnd_5582024 : Nat := 4983230072969 + 3 ^ 40 * 5582024 * 2
def baseEnd_5582024 : Nat := 955420445644324513042915

theorem tailTrace_5582024 : CollatzResearch.WordTrace tailWord_5582024 prefixEnd_5582024 955420445644324513042915 := by
  unfold tailWord_5582024
  simp only [CollatzResearch.WordTrace]
  refine ⟨101796570564643928322764563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 135728760752858571097019417 101796570564643928322764563)
  ·
    refine ⟨152694855846965892484146845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101796570564643928322764563 152694855846965892484146845)
    ·
      refine ⟨57260570942612209681555067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152694855846965892484146845 57260570942612209681555067)
      ·
        refine ⟨85890856413918314522332601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57260570942612209681555067 85890856413918314522332601)
        ·
          refine ⟨64418142310438735891749451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85890856413918314522332601 64418142310438735891749451)
          ·
            refine ⟨96627213465658103837624177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64418142310438735891749451 96627213465658103837624177)
            ·
              refine ⟨72470410099243577878218133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96627213465658103837624177 72470410099243577878218133)
              ·
                refine ⟨3397050473402042713041475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72470410099243577878218133 3397050473402042713041475)
                ·
                  refine ⟨5095575710103064069562213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3397050473402042713041475 5095575710103064069562213)
                  ·
                    refine ⟨955420445644324513042915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5095575710103064069562213 955420445644324513042915)
                    ·
                      rfl

theorem cell23_5582024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_5582024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5582024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5582024 prefixEnd_5582024 := by exact prefixLift 5582024
  have htrace : WordTrace (prefixWord ++ tailWord_5582024) baseStart_5582024 baseEnd_5582024 := by
    simpa [prefixWord, tailWord_5582024, baseEnd_5582024] using wordTrace_append hprefix tailTrace_5582024
  have hstable : (prefixWord ++ tailWord_5582024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5582024).length < 2 ^ (prefixWord ++ tailWord_5582024).sum := by decide
  have hdescent : baseEnd_5582024 < baseStart_5582024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5582024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
