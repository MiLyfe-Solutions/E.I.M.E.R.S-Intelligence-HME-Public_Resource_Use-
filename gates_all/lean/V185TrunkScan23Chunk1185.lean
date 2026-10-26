import V185TrunkScan23Chunk1184

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7021037 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7021037 : Nat := 118140960795 + 7021037 * 2 ^ 59
def prefixEnd_7021037 : Nat := 4983230072969 + 3 ^ 40 * 7021037 * 2
def baseEnd_7021037 : Nat := 3605166674001351894148345

theorem tailTrace_7021037 : CollatzResearch.WordTrace tailWord_7021037 prefixEnd_7021037 3605166674001351894148345 := by
  unfold tailWord_7021037
  simp only [CollatzResearch.WordTrace]
  refine ⟨256078257064989521499669365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170718838043326347666446243 256078257064989521499669365)
  ·
    refine ⟨24007336599842767640594003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256078257064989521499669365 24007336599842767640594003)
    ·
      refine ⟨36011004899764151460891005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24007336599842767640594003 36011004899764151460891005)
      ·
        refine ⟨13504126837411556797834127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36011004899764151460891005 13504126837411556797834127)
        ·
          refine ⟨20256190256117335196751191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13504126837411556797834127 20256190256117335196751191)
          ·
            refine ⟨30384285384176002795126787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20256190256117335196751191 30384285384176002795126787)
            ·
              refine ⟨45576428076264004192690181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30384285384176002795126787 45576428076264004192690181)
              ·
                refine ⟨8545580264299500786129409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45576428076264004192690181 8545580264299500786129409)
                ·
                  refine ⟨6409185198224625589597057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8545580264299500786129409 6409185198224625589597057)
                  ·
                    refine ⟨4806888898668469192197793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6409185198224625589597057 4806888898668469192197793)
                    ·
                      refine ⟨3605166674001351894148345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4806888898668469192197793 3605166674001351894148345)
                      ·
                        rfl

theorem cell23_7021037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7021037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021037 prefixEnd_7021037 := by exact prefixLift 7021037
  have htrace : WordTrace (prefixWord ++ tailWord_7021037) baseStart_7021037 baseEnd_7021037 := by
    simpa [prefixWord, tailWord_7021037, baseEnd_7021037] using wordTrace_append hprefix tailTrace_7021037
  have hstable : (prefixWord ++ tailWord_7021037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021037).length < 2 ^ (prefixWord ++ tailWord_7021037).sum := by decide
  have hdescent : baseEnd_7021037 < baseStart_7021037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021039 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 3, 7]
def baseStart_7021039 : Nat := 118140960795 + 7021039 * 2 ^ 59
def prefixEnd_7021039 : Nat := 4983230072969 + 3 ^ 40 * 7021039 * 2
def baseEnd_7021039 : Nat := 1201722566987553628774445

theorem tailTrace_7021039 : CollatzResearch.WordTrace tailWord_7021039 prefixEnd_7021039 1201722566987553628774445 := by
  unfold tailWord_7021039
  simp only [CollatzResearch.WordTrace]
  refine ⟨256078330010982275841242171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170718886673988183894161447 256078330010982275841242171)
  ·
    refine ⟨384117495016473413761863257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256078330010982275841242171 384117495016473413761863257)
    ·
      refine ⟨288088121262355060321397443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384117495016473413761863257 288088121262355060321397443)
      ·
        refine ⟨432132181893532590482096165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288088121262355060321397443 432132181893532590482096165)
        ·
          refine ⟨81024784105037360715393031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432132181893532590482096165 81024784105037360715393031)
          ·
            refine ⟨121537176157556041073089547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81024784105037360715393031 121537176157556041073089547)
            ·
              refine ⟨182305764236334061609634321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121537176157556041073089547 182305764236334061609634321)
              ·
                refine ⟨136729323177250546207225741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182305764236334061609634321 136729323177250546207225741)
                ·
                  refine ⟨51273496191468954827709653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136729323177250546207225741 51273496191468954827709653)
                  ·
                    refine ⟨1201722566987553628774445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51273496191468954827709653 1201722566987553628774445)
                    ·
                      rfl

theorem cell23_7021039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_7021039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021039 prefixEnd_7021039 := by exact prefixLift 7021039
  have htrace : WordTrace (prefixWord ++ tailWord_7021039) baseStart_7021039 baseEnd_7021039 := by
    simpa [prefixWord, tailWord_7021039, baseEnd_7021039] using wordTrace_append hprefix tailTrace_7021039
  have hstable : (prefixWord ++ tailWord_7021039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021039).length < 2 ^ (prefixWord ++ tailWord_7021039).sum := by decide
  have hdescent : baseEnd_7021039 < baseStart_7021039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021093 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 2, 4, 2]
def baseStart_7021093 : Nat := 118140960795 + 7021093 * 2 ^ 59
def prefixEnd_7021093 : Nat := 4983230072969 + 3 ^ 40 * 7021093 * 2
def baseEnd_7021093 : Nat := 3605195428918003675048087

theorem tailTrace_7021093 : CollatzResearch.WordTrace tailWord_7021093 prefixEnd_7021093 3605195428918003675048087 := by
  unfold tailWord_7021093
  simp only [CollatzResearch.WordTrace]
  refine ⟨256080299552786643063707933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170720199701857762042471955 256080299552786643063707933)
  ·
    refine ⟨96030112332294991148890475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256080299552786643063707933 96030112332294991148890475)
    ·
      refine ⟨144045168498442486723335713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96030112332294991148890475 144045168498442486723335713)
      ·
        refine ⟨108033876373831865042501785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144045168498442486723335713 108033876373831865042501785)
        ·
          refine ⟨81025407280373898781876339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108033876373831865042501785 81025407280373898781876339)
          ·
            refine ⟨121538110920560848172814509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81025407280373898781876339 121538110920560848172814509)
            ·
              refine ⟨45576791595210318064805441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121538110920560848172814509 45576791595210318064805441)
              ·
                refine ⟨34182593696407738548604081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45576791595210318064805441 34182593696407738548604081)
                ·
                  refine ⟨25636945272305803911453061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34182593696407738548604081 25636945272305803911453061)
                  ·
                    refine ⟨4806927238557338233397449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25636945272305803911453061 4806927238557338233397449)
                    ·
                      refine ⟨3605195428918003675048087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4806927238557338233397449 3605195428918003675048087)
                      ·
                        rfl

theorem cell23_7021093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_7021093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021093 prefixEnd_7021093 := by exact prefixLift 7021093
  have htrace : WordTrace (prefixWord ++ tailWord_7021093) baseStart_7021093 baseEnd_7021093 := by
    simpa [prefixWord, tailWord_7021093, baseEnd_7021093] using wordTrace_append hprefix tailTrace_7021093
  have hstable : (prefixWord ++ tailWord_7021093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021093).length < 2 ^ (prefixWord ++ tailWord_7021093).sum := by decide
  have hdescent : baseEnd_7021093 < baseStart_7021093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021133 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 8]
def baseStart_7021133 : Nat := 118140960795 + 7021133 * 2 ^ 59
def prefixEnd_7021133 : Nat := 4983230072969 + 3 ^ 40 * 7021133 * 2
def baseEnd_7021133 : Nat := 400579552016020390949767

theorem tailTrace_7021133 : CollatzResearch.WordTrace tailWord_7021133 prefixEnd_7021133 400579552016020390949767 := by
  unfold tailWord_7021133
  simp only [CollatzResearch.WordTrace]
  refine ⟨256081758472641729895164053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170721172315094486596776035 256081758472641729895164053)
  ·
    refine ⟨12003832428405081088835815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 256081758472641729895164053 12003832428405081088835815)
    ·
      refine ⟨18005748642607621633253723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12003832428405081088835815 18005748642607621633253723)
      ·
        refine ⟨27008622963911432449880585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18005748642607621633253723 27008622963911432449880585)
        ·
          refine ⟨20256467222933574337410439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27008622963911432449880585 20256467222933574337410439)
          ·
            refine ⟨30384700834400361506115659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20256467222933574337410439 30384700834400361506115659)
            ·
              refine ⟨45577051251600542259173489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30384700834400361506115659 45577051251600542259173489)
              ·
                refine ⟨34182788438700406694380117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45577051251600542259173489 34182788438700406694380117)
                ·
                  refine ⟨400579552016020390949767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34182788438700406694380117 400579552016020390949767)
                  ·
                    rfl

theorem cell23_7021133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_7021133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021133 prefixEnd_7021133 := by exact prefixLift 7021133
  have htrace : WordTrace (prefixWord ++ tailWord_7021133) baseStart_7021133 baseEnd_7021133 := by
    simpa [prefixWord, tailWord_7021133, baseEnd_7021133] using wordTrace_append hprefix tailTrace_7021133
  have hstable : (prefixWord ++ tailWord_7021133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021133).length < 2 ^ (prefixWord ++ tailWord_7021133).sum := by decide
  have hdescent : baseEnd_7021133 < baseStart_7021133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021137 : List Nat := [1, 2, 2, 1, 3, 5, 1, 3, 1, 4]
def baseStart_7021137 : Nat := 118140960795 + 7021137 * 2 ^ 59
def prefixEnd_7021137 : Nat := 4983230072969 + 3 ^ 40 * 7021137 * 2
def baseEnd_7021137 : Nat := 1201739340688933834299295

theorem tailTrace_7021137 : CollatzResearch.WordTrace tailWord_7021137 prefixEnd_7021137 1201739340688933834299295 := by
  unfold tailWord_7021137
  simp only [CollatzResearch.WordTrace]
  refine ⟨256081904364627238578309665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170721269576418159052206443 256081904364627238578309665)
  ·
    refine ⟨192061428273470428933732249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256081904364627238578309665 192061428273470428933732249)
    ·
      refine ⟨144046071205102821700299187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192061428273470428933732249 144046071205102821700299187)
      ·
        refine ⟨216069106807654232550448781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144046071205102821700299187 216069106807654232550448781)
        ·
          refine ⟨81025915052870337206418293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216069106807654232550448781 81025915052870337206418293)
          ·
            refine ⟨7596179536206594113101715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81025915052870337206418293 7596179536206594113101715)
            ·
              refine ⟨11394269304309891169652573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7596179536206594113101715 11394269304309891169652573)
              ·
                refine ⟨4272850989116209188619715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11394269304309891169652573 4272850989116209188619715)
                ·
                  refine ⟨6409276483674313782929573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4272850989116209188619715 6409276483674313782929573)
                  ·
                    refine ⟨1201739340688933834299295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6409276483674313782929573 1201739340688933834299295)
                    ·
                      rfl

theorem cell23_7021137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_7021137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021137 prefixEnd_7021137 := by exact prefixLift 7021137
  have htrace : WordTrace (prefixWord ++ tailWord_7021137) baseStart_7021137 baseEnd_7021137 := by
    simpa [prefixWord, tailWord_7021137, baseEnd_7021137] using wordTrace_append hprefix tailTrace_7021137
  have hstable : (prefixWord ++ tailWord_7021137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021137).length < 2 ^ (prefixWord ++ tailWord_7021137).sum := by decide
  have hdescent : baseEnd_7021137 < baseStart_7021137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021146 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_7021146 : Nat := 118140960795 + 7021146 * 2 ^ 59
def prefixEnd_7021146 : Nat := 4983230072969 + 3 ^ 40 * 7021146 * 2
def baseEnd_7021146 : Nat := 1201740881130897322561781

theorem tailTrace_7021146 : CollatzResearch.WordTrace tailWord_7021146 prefixEnd_7021146 1201740881130897322561781 := by
  unfold tailWord_7021146
  simp only [CollatzResearch.WordTrace]
  refine ⟨64020558155398658278846823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170721488414396422076924861 64020558155398658278846823)
  ·
    refine ⟨96030837233097987418270235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64020558155398658278846823 96030837233097987418270235)
    ·
      refine ⟨144046255849646981127405353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96030837233097987418270235 144046255849646981127405353)
      ·
        refine ⟨108034691887235235845554015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144046255849646981127405353 108034691887235235845554015)
        ·
          refine ⟨162052037830852853768331023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108034691887235235845554015 162052037830852853768331023)
          ·
            refine ⟨243078056746279280652496535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162052037830852853768331023 243078056746279280652496535)
            ·
              refine ⟨364617085119418920978744803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243078056746279280652496535 364617085119418920978744803)
              ·
                refine ⟨546925627679128381468117205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364617085119418920978744803 546925627679128381468117205)
                ·
                  refine ⟨12818569398729571440658997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 546925627679128381468117205 12818569398729571440658997)
                  ·
                    refine ⟨1201740881130897322561781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12818569398729571440658997 1201740881130897322561781)
                    ·
                      rfl

theorem cell23_7021146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_7021146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021146 prefixEnd_7021146 := by exact prefixLift 7021146
  have htrace : WordTrace (prefixWord ++ tailWord_7021146) baseStart_7021146 baseEnd_7021146 := by
    simpa [prefixWord, tailWord_7021146, baseEnd_7021146] using wordTrace_append hprefix tailTrace_7021146
  have hstable : (prefixWord ++ tailWord_7021146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021146).length < 2 ^ (prefixWord ++ tailWord_7021146).sum := by decide
  have hdescent : baseEnd_7021146 < baseStart_7021146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021154 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 3, 4]
def baseStart_7021154 : Nat := 118140960795 + 7021154 * 2 ^ 59
def prefixEnd_7021154 : Nat := 4983230072969 + 3 ^ 40 * 7021154 * 2
def baseEnd_7021154 : Nat := 1201742250412642645461769

theorem tailTrace_7021154 : CollatzResearch.WordTrace tailWord_7021154 prefixEnd_7021154 1201742250412642645461769 := by
  unfold tailWord_7021154
  simp only [CollatzResearch.WordTrace]
  refine ⟨64020631101391412620419629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170721682937043766987785677 64020631101391412620419629)
  ·
    refine ⟨24007736663021779732657361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64020631101391412620419629 24007736663021779732657361)
    ·
      refine ⟨18005802497266334799493021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24007736663021779732657361 18005802497266334799493021)
      ·
        refine ⟨6752175936474875549809883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18005802497266334799493021 6752175936474875549809883)
        ·
          refine ⟨10128263904712313324714825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752175936474875549809883 10128263904712313324714825)
          ·
            refine ⟨7596197928534234993536119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10128263904712313324714825 7596197928534234993536119)
            ·
              refine ⟨11394296892801352490304179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7596197928534234993536119 11394296892801352490304179)
              ·
                refine ⟨17091445339202028735456269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11394296892801352490304179 17091445339202028735456269)
                ·
                  refine ⟨6409292002200760775796101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17091445339202028735456269 6409292002200760775796101)
                  ·
                    refine ⟨1201742250412642645461769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6409292002200760775796101 1201742250412642645461769)
                    ·
                      rfl

theorem cell23_7021154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_7021154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021154 prefixEnd_7021154 := by exact prefixLift 7021154
  have htrace : WordTrace (prefixWord ++ tailWord_7021154) baseStart_7021154 baseEnd_7021154 := by
    simpa [prefixWord, tailWord_7021154, baseEnd_7021154] using wordTrace_append hprefix tailTrace_7021154
  have hstable : (prefixWord ++ tailWord_7021154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021154).length < 2 ^ (prefixWord ++ tailWord_7021154).sum := by decide
  have hdescent : baseEnd_7021154 < baseStart_7021154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021183 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 4]
def baseStart_7021183 : Nat := 118140960795 + 7021183 * 2 ^ 59
def prefixEnd_7021183 : Nat := 4983230072969 + 3 ^ 40 * 7021183 * 2
def baseEnd_7021183 : Nat := 3605241642176908322922673

theorem tailTrace_7021183 : CollatzResearch.WordTrace tailWord_7021183 prefixEnd_7021183 3605241642176908322922673 := by
  unfold tailWord_7021183
  simp only [CollatzResearch.WordTrace]
  refine ⟨256083582122460588434484203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170722388081640392289656135 256083582122460588434484203)
  ·
    refine ⟨384125373183690882651726305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256083582122460588434484203 384125373183690882651726305)
    ·
      refine ⟨288094029887768161988794729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384125373183690882651726305 288094029887768161988794729)
      ·
        refine ⟨216070522415826121491596047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288094029887768161988794729 216070522415826121491596047)
        ·
          refine ⟨324105783623739182237394071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216070522415826121491596047 324105783623739182237394071)
          ·
            refine ⟨486158675435608773356091107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324105783623739182237394071 486158675435608773356091107)
            ·
              refine ⟨729238013153413160034136661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486158675435608773356091107 729238013153413160034136661)
              ·
                refine ⟨8545757966641560469150039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 729238013153413160034136661 8545757966641560469150039)
                ·
                  refine ⟨12818636949962340703725059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8545757966641560469150039 12818636949962340703725059)
                  ·
                    refine ⟨19227955424943511055587589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12818636949962340703725059 19227955424943511055587589)
                    ·
                      refine ⟨3605241642176908322922673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19227955424943511055587589 3605241642176908322922673)
                      ·
                        rfl

theorem cell23_7021183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_7021183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021183 prefixEnd_7021183 := by exact prefixLift 7021183
  have htrace : WordTrace (prefixWord ++ tailWord_7021183) baseStart_7021183 baseEnd_7021183 := by
    simpa [prefixWord, tailWord_7021183, baseEnd_7021183] using wordTrace_append hprefix tailTrace_7021183
  have hstable : (prefixWord ++ tailWord_7021183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021183).length < 2 ^ (prefixWord ++ tailWord_7021183).sum := by decide
  have hdescent : baseEnd_7021183 < baseStart_7021183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021196 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_7021196 : Nat := 118140960795 + 7021196 * 2 ^ 59
def prefixEnd_7021196 : Nat := 4983230072969 + 3 ^ 40 * 7021196 * 2
def baseEnd_7021196 : Nat := 3605248317425416772060113

theorem tailTrace_7021196 : CollatzResearch.WordTrace tailWord_7021196 prefixEnd_7021196 3605248317425416772060113 := by
  unfold tailWord_7021196
  simp only [CollatzResearch.WordTrace]
  refine ⟨128042028135706745827353721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170722704180942327769804961 128042028135706745827353721)
  ·
    refine ⟨96031521101780059370515291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128042028135706745827353721 96031521101780059370515291)
    ·
      refine ⟨144047281652670089055772937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96031521101780059370515291 144047281652670089055772937)
      ·
        refine ⟨108035461239502566791829703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144047281652670089055772937 108035461239502566791829703)
        ·
          refine ⟨162053191859253850187744555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108035461239502566791829703 162053191859253850187744555)
          ·
            refine ⟨243079787788880775281616833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162053191859253850187744555 243079787788880775281616833)
            ·
              refine ⟨182309840841660581461212625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243079787788880775281616833 182309840841660581461212625)
              ·
                refine ⟨136732380631245436095909469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182309840841660581461212625 136732380631245436095909469)
                ·
                  refine ⟨51274642736717038535966051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136732380631245436095909469 51274642736717038535966051)
                  ·
                    refine ⟨76911964105075557803949077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51274642736717038535966051 76911964105075557803949077)
                    ·
                      refine ⟨3605248317425416772060113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76911964105075557803949077 3605248317425416772060113)
                      ·
                        rfl

theorem cell23_7021196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_7021196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021196 prefixEnd_7021196 := by exact prefixLift 7021196
  have htrace : WordTrace (prefixWord ++ tailWord_7021196) baseStart_7021196 baseEnd_7021196 := by
    simpa [prefixWord, tailWord_7021196, baseEnd_7021196] using wordTrace_append hprefix tailTrace_7021196
  have hstable : (prefixWord ++ tailWord_7021196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021196).length < 2 ^ (prefixWord ++ tailWord_7021196).sum := by decide
  have hdescent : baseEnd_7021196 < baseStart_7021196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021238 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_7021238 : Nat := 118140960795 + 7021238 * 2 ^ 59
def prefixEnd_7021238 : Nat := 4983230072969 + 3 ^ 40 * 7021238 * 2
def baseEnd_7021238 : Nat := 3605269883612905607734921

theorem tailTrace_7021238 : CollatzResearch.WordTrace tailWord_7021238 prefixEnd_7021238 3605269883612905607734921 := by
  unfold tailWord_7021238
  simp only [CollatzResearch.WordTrace]
  refine ⟨16005349258578833301733523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170723725424840888551824245 16005349258578833301733523)
  ·
    refine ⟨24008023887868249952600285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16005349258578833301733523 24008023887868249952600285)
    ·
      refine ⟨9003008957950593732225107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24008023887868249952600285 9003008957950593732225107)
      ·
        refine ⟨13504513436925890598337661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9003008957950593732225107 13504513436925890598337661)
        ·
          refine ⟨5064192538847208974376623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13504513436925890598337661 5064192538847208974376623)
          ·
            refine ⟨7596288808270813461564935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5064192538847208974376623 7596288808270813461564935)
            ·
              refine ⟨11394433212406220192347403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7596288808270813461564935 11394433212406220192347403)
              ·
                refine ⟨17091649818609330288521105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11394433212406220192347403 17091649818609330288521105)
                ·
                  refine ⟨12818737363956997716390829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17091649818609330288521105 12818737363956997716390829)
                  ·
                    refine ⟨4807026511483874143646561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12818737363956997716390829 4807026511483874143646561)
                    ·
                      refine ⟨3605269883612905607734921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807026511483874143646561 3605269883612905607734921)
                      ·
                        rfl

theorem cell23_7021238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_7021238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021238 prefixEnd_7021238 := by exact prefixLift 7021238
  have htrace : WordTrace (prefixWord ++ tailWord_7021238) baseStart_7021238 baseEnd_7021238 := by
    simpa [prefixWord, tailWord_7021238, baseEnd_7021238] using wordTrace_append hprefix tailTrace_7021238
  have hstable : (prefixWord ++ tailWord_7021238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021238).length < 2 ^ (prefixWord ++ tailWord_7021238).sum := by decide
  have hdescent : baseEnd_7021238 < baseStart_7021238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021261 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_7021261 : Nat := 118140960795 + 7021261 * 2 ^ 59
def prefixEnd_7021261 : Nat := 4983230072969 + 3 ^ 40 * 7021261 * 2
def baseEnd_7021261 : Nat := 1201760564555986339249105

theorem tailTrace_7021261 : CollatzResearch.WordTrace tailWord_7021261 prefixEnd_7021261 1201760564555986339249105 := by
  unfold tailWord_7021261
  simp only [CollatzResearch.WordTrace]
  refine ⟨256086427016178007755823637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170724284677452005170549091 256086427016178007755823637)
  ·
    refine ⟨12004051266383344113554233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 256086427016178007755823637 12004051266383344113554233)
    ·
      refine ⟨9003038449787508085165675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12004051266383344113554233 9003038449787508085165675)
      ·
        refine ⟨13504557674681262127748513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9003038449787508085165675 13504557674681262127748513)
        ·
          refine ⟨10128418256010946595811385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13504557674681262127748513 10128418256010946595811385)
          ·
            refine ⟨7596313692008209946858539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10128418256010946595811385 7596313692008209946858539)
            ·
              refine ⟨11394470538012314920287809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7596313692008209946858539 11394470538012314920287809)
              ·
                refine ⟨8545852903509236190215857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11394470538012314920287809 8545852903509236190215857)
                ·
                  refine ⟨6409389677631927142661893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8545852903509236190215857 6409389677631927142661893)
                  ·
                    refine ⟨1201760564555986339249105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6409389677631927142661893 1201760564555986339249105)
                    ·
                      rfl

theorem cell23_7021261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_7021261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021261 prefixEnd_7021261 := by exact prefixLift 7021261
  have htrace : WordTrace (prefixWord ++ tailWord_7021261) baseStart_7021261 baseEnd_7021261 := by
    simpa [prefixWord, tailWord_7021261, baseEnd_7021261] using wordTrace_append hprefix tailTrace_7021261
  have hstable : (prefixWord ++ tailWord_7021261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021261).length < 2 ^ (prefixWord ++ tailWord_7021261).sum := by decide
  have hdescent : baseEnd_7021261 < baseStart_7021261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021284 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 2, 1, 3]
def baseStart_7021284 : Nat := 118140960795 + 7021284 * 2 ^ 59
def prefixEnd_7021284 : Nat := 4983230072969 + 3 ^ 40 * 7021284 * 2
def baseEnd_7021284 : Nat := 3605293503723012427759709

theorem tailTrace_7021284 : CollatzResearch.WordTrace tailWord_7021284 prefixEnd_7021284 3605293503723012427759709 := by
  unfold tailWord_7021284
  simp only [CollatzResearch.WordTrace]
  refine ⟨128043632947547341341955453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170724843930063121789273937 128043632947547341341955453)
  ·
    refine ⟨48016362355330253003233295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128043632947547341341955453 48016362355330253003233295)
    ·
      refine ⟨72024543532995379504849943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48016362355330253003233295 72024543532995379504849943)
      ·
        refine ⟨108036815299493069257274915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72024543532995379504849943 108036815299493069257274915)
        ·
          refine ⟨162055222949239603885912373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108036815299493069257274915 162055222949239603885912373)
          ·
            refine ⟨15192677151491212864304285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162055222949239603885912373 15192677151491212864304285)
            ·
              refine ⟨5697253931809204824114107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15192677151491212864304285 5697253931809204824114107)
              ·
                refine ⟨8545880897713807236171161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697253931809204824114107 8545880897713807236171161)
                ·
                  refine ⟨6409410673285355427128371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8545880897713807236171161 6409410673285355427128371)
                  ·
                    refine ⟨9614116009928033140692557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6409410673285355427128371 9614116009928033140692557)
                    ·
                      refine ⟨3605293503723012427759709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9614116009928033140692557 3605293503723012427759709)
                      ·
                        rfl

theorem cell23_7021284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_7021284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021284 prefixEnd_7021284 := by exact prefixLift 7021284
  have htrace : WordTrace (prefixWord ++ tailWord_7021284) baseStart_7021284 baseEnd_7021284 := by
    simpa [prefixWord, tailWord_7021284, baseEnd_7021284] using wordTrace_append hprefix tailTrace_7021284
  have hstable : (prefixWord ++ tailWord_7021284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021284).length < 2 ^ (prefixWord ++ tailWord_7021284).sum := by decide
  have hdescent : baseEnd_7021284 < baseStart_7021284 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021294 : List Nat := [4, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_7021294 : Nat := 118140960795 + 7021294 * 2 ^ 59
def prefixEnd_7021294 : Nat := 4983230072969 + 3 ^ 40 * 7021294 * 2
def baseEnd_7021294 : Nat := 3605298638529557388634663

theorem tailTrace_7021294 : CollatzResearch.WordTrace tailWord_7021294 prefixEnd_7021294 3605298638529557388634663 := by
  unfold tailWord_7021294
  simp only [CollatzResearch.WordTrace]
  refine ⟨32010953828132306798971867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170725087083372302927849957 32010953828132306798971867)
  ·
    refine ⟨48016430742198460198457801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32010953828132306798971867 48016430742198460198457801)
    ·
      refine ⟨36012323056648845148843351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48016430742198460198457801 36012323056648845148843351)
      ·
        refine ⟨54018484584973267723265027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36012323056648845148843351 54018484584973267723265027)
        ·
          refine ⟨81027726877459901584897541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54018484584973267723265027 81027726877459901584897541)
          ·
            refine ⟨15192698789523731547168289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81027726877459901584897541 15192698789523731547168289)
            ·
              refine ⟨11394524092142798660376217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15192698789523731547168289 11394524092142798660376217)
              ·
                refine ⟨8545893069107098995282163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11394524092142798660376217 8545893069107098995282163)
                ·
                  refine ⟨12818839603660648492923245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8545893069107098995282163 12818839603660648492923245)
                  ·
                    refine ⟨4807064851372743184846217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12818839603660648492923245 4807064851372743184846217)
                    ·
                      refine ⟨3605298638529557388634663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807064851372743184846217 3605298638529557388634663)
                      ·
                        rfl

theorem cell23_7021294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_7021294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021294 prefixEnd_7021294 := by exact prefixLift 7021294
  have htrace : WordTrace (prefixWord ++ tailWord_7021294) baseStart_7021294 baseEnd_7021294 := by
    simpa [prefixWord, tailWord_7021294, baseEnd_7021294] using wordTrace_append hprefix tailTrace_7021294
  have hstable : (prefixWord ++ tailWord_7021294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021294).length < 2 ^ (prefixWord ++ tailWord_7021294).sum := by decide
  have hdescent : baseEnd_7021294 < baseStart_7021294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021310 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_7021310 : Nat := 118140960795 + 7021310 * 2 ^ 59
def prefixEnd_7021310 : Nat := 4983230072969 + 3 ^ 40 * 7021310 * 2
def baseEnd_7021310 : Nat := 3605306854220029326034589

theorem tailTrace_7021310 : CollatzResearch.WordTrace tailWord_7021310 prefixEnd_7021310 3605306854220029326034589 := by
  unfold tailWord_7021310
  simp only [CollatzResearch.WordTrace]
  refine ⟨32011026774125061140544673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170725476128666992749571589 32011026774125061140544673)
  ·
    refine ⟨24008270080593795855408505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32011026774125061140544673 24008270080593795855408505)
    ·
      refine ⟨18006202560445346891556379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24008270080593795855408505 18006202560445346891556379)
      ·
        refine ⟨27009303840668020337334569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18006202560445346891556379 27009303840668020337334569)
        ·
          refine ⟨20256977880501015253000927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27009303840668020337334569 20256977880501015253000927)
          ·
            refine ⟨30385466820751522879501391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20256977880501015253000927 30385466820751522879501391)
            ·
              refine ⟨45578200231127284319252087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30385466820751522879501391 45578200231127284319252087)
              ·
                refine ⟨68367300346690926478878131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45578200231127284319252087 68367300346690926478878131)
                ·
                  refine ⟨102550950520036389718317197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68367300346690926478878131 102550950520036389718317197)
                  ·
                    refine ⟨38456606445013646144368949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102550950520036389718317197 38456606445013646144368949)
                    ·
                      refine ⟨3605306854220029326034589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38456606445013646144368949 3605306854220029326034589)
                      ·
                        rfl

theorem cell23_7021310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_7021310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021310 prefixEnd_7021310 := by exact prefixLift 7021310
  have htrace : WordTrace (prefixWord ++ tailWord_7021310) baseStart_7021310 baseEnd_7021310 := by
    simpa [prefixWord, tailWord_7021310, baseEnd_7021310] using wordTrace_append hprefix tailTrace_7021310
  have hstable : (prefixWord ++ tailWord_7021310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021310).length < 2 ^ (prefixWord ++ tailWord_7021310).sum := by decide
  have hdescent : baseEnd_7021310 < baseStart_7021310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021383 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_7021383 : Nat := 118140960795 + 7021383 * 2 ^ 59
def prefixEnd_7021383 : Nat := 4983230072969 + 3 ^ 40 * 7021383 * 2
def baseEnd_7021383 : Nat := 3605344338307807540421753

theorem tailTrace_7021383 : CollatzResearch.WordTrace tailWord_7021383 prefixEnd_7021383 3605344338307807540421753 := by
  unfold tailWord_7021383
  simp only [CollatzResearch.WordTrace]
  refine ⟨256090876721736022591764803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170727251147824015061176535 256090876721736022591764803)
  ·
    refine ⟨384136315082604033887647205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256090876721736022591764803 384136315082604033887647205)
    ·
      refine ⟨72025559077988256353933851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384136315082604033887647205 72025559077988256353933851)
      ·
        refine ⟨108038338616982384530900777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72025559077988256353933851 108038338616982384530900777)
        ·
          refine ⟨81028753962736788398175583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108038338616982384530900777 81028753962736788398175583)
          ·
            refine ⟨121543130944105182597263375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81028753962736788398175583 121543130944105182597263375)
            ·
              refine ⟨182314696416157773895895063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121543130944105182597263375 182314696416157773895895063)
              ·
                refine ⟨273472044624236660843842595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182314696416157773895895063 273472044624236660843842595)
                ·
                  refine ⟨410208066936354991265763893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273472044624236660843842595 410208066936354991265763893)
                  ·
                    refine ⟨38457006275283280431165365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 410208066936354991265763893 38457006275283280431165365)
                    ·
                      refine ⟨3605344338307807540421753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38457006275283280431165365 3605344338307807540421753)
                      ·
                        rfl

theorem cell23_7021383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_7021383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021383 prefixEnd_7021383 := by exact prefixLift 7021383
  have htrace : WordTrace (prefixWord ++ tailWord_7021383) baseStart_7021383 baseEnd_7021383 := by
    simpa [prefixWord, tailWord_7021383, baseEnd_7021383] using wordTrace_append hprefix tailTrace_7021383
  have hstable : (prefixWord ++ tailWord_7021383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021383).length < 2 ^ (prefixWord ++ tailWord_7021383).sum := by decide
  have hdescent : baseEnd_7021383 < baseStart_7021383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021390 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_7021390 : Nat := 118140960795 + 7021390 * 2 ^ 59
def prefixEnd_7021390 : Nat := 4983230072969 + 3 ^ 40 * 7021390 * 2
def baseEnd_7021390 : Nat := 1201782644224129671011407

theorem tailTrace_7021390 : CollatzResearch.WordTrace tailWord_7021390 prefixEnd_7021390 1201782644224129671011407 := by
  unfold tailWord_7021390
  simp only [CollatzResearch.WordTrace]
  refine ⟨32011391504088832848408703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170727421355140441858179749 32011391504088832848408703)
  ·
    refine ⟨48017087256133249272613055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32011391504088832848408703 48017087256133249272613055)
    ·
      refine ⟨72025630884199873908919583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48017087256133249272613055 72025630884199873908919583)
      ·
        refine ⟨108038446326299810863379375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72025630884199873908919583 108038446326299810863379375)
        ·
          refine ⟨162057669489449716295069063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108038446326299810863379375 162057669489449716295069063)
          ·
            refine ⟨243086504234174574442603595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162057669489449716295069063 243086504234174574442603595)
            ·
              refine ⟨364629756351261861663905393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243086504234174574442603595 364629756351261861663905393)
              ·
                refine ⟨273472317263446396247929045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364629756351261861663905393 273472317263446396247929045)
                ·
                  refine ⟨6409507435862024912060837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 273472317263446396247929045 6409507435862024912060837)
                  ·
                    refine ⟨1201782644224129671011407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6409507435862024912060837 1201782644224129671011407)
                    ·
                      rfl

theorem cell23_7021390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_7021390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021390 prefixEnd_7021390 := by exact prefixLift 7021390
  have htrace : WordTrace (prefixWord ++ tailWord_7021390) baseStart_7021390 baseEnd_7021390 := by
    simpa [prefixWord, tailWord_7021390, baseEnd_7021390] using wordTrace_append hprefix tailTrace_7021390
  have hstable : (prefixWord ++ tailWord_7021390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021390).length < 2 ^ (prefixWord ++ tailWord_7021390).sum := by decide
  have hdescent : baseEnd_7021390 < baseStart_7021390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021397 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 2, 4, 2]
def baseStart_7021397 : Nat := 118140960795 + 7021397 * 2 ^ 59
def prefixEnd_7021397 : Nat := 4983230072969 + 3 ^ 40 * 7021397 * 2
def baseEnd_7021397 : Nat := 3605351527036970485646689

theorem tailTrace_7021397 : CollatzResearch.WordTrace tailWord_7021397 prefixEnd_7021397 3605351527036970485646689 := by
  unfold tailWord_7021397
  simp only [CollatzResearch.WordTrace]
  refine ⟨256091387343685302982774445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170727591562456868655182963 256091387343685302982774445)
  ·
    refine ⟨96034270253881988618540417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256091387343685302982774445 96034270253881988618540417)
    ·
      refine ⟨72025702690411491463905313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96034270253881988618540417 72025702690411491463905313)
      ·
        refine ⟨54019277017808618597928985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72025702690411491463905313 54019277017808618597928985)
        ·
          refine ⟨40514457763356463948446739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54019277017808618597928985 40514457763356463948446739)
          ·
            refine ⟨60771686645034695922670109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40514457763356463948446739 60771686645034695922670109)
            ·
              refine ⟨22789382491888010971001291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60771686645034695922670109 22789382491888010971001291)
              ·
                refine ⟨34184073737832016456501937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22789382491888010971001291 34184073737832016456501937)
                ·
                  refine ⟨25638055303374012342376453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34184073737832016456501937 25638055303374012342376453)
                  ·
                    refine ⟨4807135369382627314195585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25638055303374012342376453 4807135369382627314195585)
                    ·
                      refine ⟨3605351527036970485646689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807135369382627314195585 3605351527036970485646689)
                      ·
                        rfl

theorem cell23_7021397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_7021397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021397 prefixEnd_7021397 := by exact prefixLift 7021397
  have htrace : WordTrace (prefixWord ++ tailWord_7021397) baseStart_7021397 baseEnd_7021397 := by
    simpa [prefixWord, tailWord_7021397, baseEnd_7021397] using wordTrace_append hprefix tailTrace_7021397
  have hstable : (prefixWord ++ tailWord_7021397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021397).length < 2 ^ (prefixWord ++ tailWord_7021397).sum := by decide
  have hdescent : baseEnd_7021397 < baseStart_7021397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021400 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 4, 2, 3]
def baseStart_7021400 : Nat := 118140960795 + 7021400 * 2 ^ 59
def prefixEnd_7021400 : Nat := 4983230072969 + 3 ^ 40 * 7021400 * 2
def baseEnd_7021400 : Nat := 3605353067478933973909175

theorem tailTrace_7021400 : CollatzResearch.WordTrace tailWord_7021400 prefixEnd_7021400 3605353067478933973909175 := by
  unfold tailWord_7021400
  simp only [CollatzResearch.WordTrace]
  refine ⟨128045748381337217247566827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170727664508449622996755769 128045748381337217247566827)
  ·
    refine ⟨192068622572005825871350241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128045748381337217247566827 192068622572005825871350241)
    ·
      refine ⟨144051466929004369403512681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192068622572005825871350241 144051466929004369403512681)
      ·
        refine ⟨108038600196753277052634511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144051466929004369403512681 108038600196753277052634511)
        ·
          refine ⟨162057900295129915578951767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108038600196753277052634511 162057900295129915578951767)
          ·
            refine ⟨243086850442694873368427651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162057900295129915578951767 243086850442694873368427651)
            ·
              refine ⟨364630275664042310052641477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243086850442694873368427651 364630275664042310052641477)
              ·
                refine ⟨68368176687007933134870277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364630275664042310052641477 68368176687007933134870277)
                ·
                  refine ⟨12819033128813987462788177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68368176687007933134870277 12819033128813987462788177)
                  ·
                    refine ⟨9614274846610490597091133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12819033128813987462788177 9614274846610490597091133)
                    ·
                      refine ⟨3605353067478933973909175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9614274846610490597091133 3605353067478933973909175)
                      ·
                        rfl

theorem cell23_7021400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_7021400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021400 prefixEnd_7021400 := by exact prefixLift 7021400
  have htrace : WordTrace (prefixWord ++ tailWord_7021400) baseStart_7021400 baseEnd_7021400 := by
    simpa [prefixWord, tailWord_7021400, baseEnd_7021400] using wordTrace_append hprefix tailTrace_7021400
  have hstable : (prefixWord ++ tailWord_7021400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021400).length < 2 ^ (prefixWord ++ tailWord_7021400).sum := by decide
  have hdescent : baseEnd_7021400 < baseStart_7021400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021423 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_7021423 : Nat := 118140960795 + 7021423 * 2 ^ 59
def prefixEnd_7021423 : Nat := 4983230072969 + 3 ^ 40 * 7021423 * 2
def baseEnd_7021423 : Nat := 3605364877533987383921569

theorem tailTrace_7021423 : CollatzResearch.WordTrace tailWord_7021423 prefixEnd_7021423 3605364877533987383921569 := by
  unfold tailWord_7021423
  simp only [CollatzResearch.WordTrace]
  refine ⟨256092335641591109423220923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170728223761060739615480615 256092335641591109423220923)
  ·
    refine ⟨384138503462386664134831385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256092335641591109423220923 384138503462386664134831385)
    ·
      refine ⟨288103877596789998101123539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384138503462386664134831385 288103877596789998101123539)
      ·
        refine ⟨432155816395184997151685309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288103877596789998101123539 432155816395184997151685309)
        ·
          refine ⟨162058431148194373931881991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432155816395184997151685309 162058431148194373931881991)
          ·
            refine ⟨243087646722291560897822987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162058431148194373931881991 243087646722291560897822987)
            ·
              refine ⟨364631470083437341346734481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243087646722291560897822987 364631470083437341346734481)
              ·
                refine ⟨273473602562578006010050861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364631470083437341346734481 273473602562578006010050861)
                ·
                  refine ⟨102552600960966752253769073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273473602562578006010050861 102552600960966752253769073)
                  ·
                    refine ⟨76914450720725064190326805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102552600960966752253769073 76914450720725064190326805)
                    ·
                      refine ⟨3605364877533987383921569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76914450720725064190326805 3605364877533987383921569)
                      ·
                        rfl

theorem cell23_7021423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_7021423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021423 prefixEnd_7021423 := by exact prefixLift 7021423
  have htrace : WordTrace (prefixWord ++ tailWord_7021423) baseStart_7021423 baseEnd_7021423 := by
    simpa [prefixWord, tailWord_7021423, baseEnd_7021423] using wordTrace_append hprefix tailTrace_7021423
  have hstable : (prefixWord ++ tailWord_7021423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021423).length < 2 ^ (prefixWord ++ tailWord_7021423).sum := by decide
  have hdescent : baseEnd_7021423 < baseStart_7021423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021474 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 1, 5, 2]
def baseStart_7021474 : Nat := 118140960795 + 7021474 * 2 ^ 59
def prefixEnd_7021474 : Nat := 4983230072969 + 3 ^ 40 * 7021474 * 2
def baseEnd_7021474 : Nat := 3605391065047366684383835

theorem tailTrace_7021474 : CollatzResearch.WordTrace tailWord_7021474 prefixEnd_7021474 3605391065047366684383835 := by
  unfold tailWord_7021474
  simp only [CollatzResearch.WordTrace]
  refine ⟨64023548941101586283331869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170729463842937563422218317 64023548941101586283331869)
  ·
    refine ⟨24008830852913094856249451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64023548941101586283331869 24008830852913094856249451)
    ·
      refine ⟨36013246279369642284374177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24008830852913094856249451 36013246279369642284374177)
      ·
        refine ⟨27009934709527231713280633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36013246279369642284374177 27009934709527231713280633)
        ·
          refine ⟨20257451032145423784960475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27009934709527231713280633 20257451032145423784960475)
          ·
            refine ⟨30386176548218135677440713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20257451032145423784960475 30386176548218135677440713)
            ·
              refine ⟨22789632411163601758080535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30386176548218135677440713 22789632411163601758080535)
              ·
                refine ⟨34184448616745402637120803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22789632411163601758080535 34184448616745402637120803)
                ·
                  refine ⟨51276672925118103955681205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34184448616745402637120803 51276672925118103955681205)
                  ·
                    refine ⟨4807188086729822245845113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51276672925118103955681205 4807188086729822245845113)
                    ·
                      refine ⟨3605391065047366684383835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807188086729822245845113 3605391065047366684383835)
                      ·
                        rfl

theorem cell23_7021474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_7021474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021474 prefixEnd_7021474 := by exact prefixLift 7021474
  have htrace : WordTrace (prefixWord ++ tailWord_7021474) baseStart_7021474 baseEnd_7021474 := by
    simpa [prefixWord, tailWord_7021474, baseEnd_7021474] using wordTrace_append hprefix tailTrace_7021474
  have hstable : (prefixWord ++ tailWord_7021474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021474).length < 2 ^ (prefixWord ++ tailWord_7021474).sum := by decide
  have hdescent : baseEnd_7021474 < baseStart_7021474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021497 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 4, 4]
def baseStart_7021497 : Nat := 118140960795 + 7021497 * 2 ^ 59
def prefixEnd_7021497 : Nat := 4983230072969 + 3 ^ 40 * 7021497 * 2
def baseEnd_7021497 : Nat := 1201800958367473364798743

theorem tailTrace_7021497 : CollatzResearch.WordTrace tailWord_7021497 prefixEnd_7021497 1201800958367473364798743 := by
  unfold tailWord_7021497
  simp only [CollatzResearch.WordTrace]
  refine ⟨256095034643323020061414745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170730023095548680040943163 256095034643323020061414745)
  ·
    refine ⟨192071275982492265046061059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256095034643323020061414745 192071275982492265046061059)
    ·
      refine ⟨288106913973738397569091589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192071275982492265046061059 288106913973738397569091589)
      ·
        refine ⟨54020046370075949544204673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288106913973738397569091589 54020046370075949544204673)
        ·
          refine ⟨40515034777556962158153505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54020046370075949544204673 40515034777556962158153505)
          ·
            refine ⟨30386276083167721618615129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40515034777556962158153505 30386276083167721618615129)
            ·
              refine ⟨22789707062375791213961347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30386276083167721618615129 22789707062375791213961347)
              ·
                refine ⟨34184560593563686820942021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22789707062375791213961347 34184560593563686820942021)
                ·
                  refine ⟨6409605111293191278926629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34184560593563686820942021 6409605111293191278926629)
                  ·
                    refine ⟨1201800958367473364798743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6409605111293191278926629 1201800958367473364798743)
                    ·
                      rfl

theorem cell23_7021497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 4].length) (baseStart_7021497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021497 prefixEnd_7021497 := by exact prefixLift 7021497
  have htrace : WordTrace (prefixWord ++ tailWord_7021497) baseStart_7021497 baseEnd_7021497 := by
    simpa [prefixWord, tailWord_7021497, baseEnd_7021497] using wordTrace_append hprefix tailTrace_7021497
  have hstable : (prefixWord ++ tailWord_7021497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021497).length < 2 ^ (prefixWord ++ tailWord_7021497).sum := by decide
  have hdescent : baseEnd_7021497 < baseStart_7021497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021524 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_7021524 : Nat := 118140960795 + 7021524 * 2 ^ 59
def prefixEnd_7021524 : Nat := 4983230072969 + 3 ^ 40 * 7021524 * 2
def baseEnd_7021524 : Nat := 3605416739080091488758605

theorem tailTrace_7021524 : CollatzResearch.WordTrace tailWord_7021524 prefixEnd_7021524 3605416739080091488758605 := by
  unfold tailWord_7021524
  simp only [CollatzResearch.WordTrace]
  refine ⟨128048009707112601836323813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170730679609483469115098417 128048009707112601836323813)
  ·
    refine ⟨24009001820083612844310715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128048009707112601836323813 24009001820083612844310715)
    ·
      refine ⟨36013502730125419266466073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24009001820083612844310715 36013502730125419266466073)
      ·
        refine ⟨27010127047594064449849555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36013502730125419266466073 27010127047594064449849555)
        ·
          refine ⟨40515190571391096674774333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27010127047594064449849555 40515190571391096674774333)
          ·
            refine ⟨15193196464271661253040375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40515190571391096674774333 15193196464271661253040375)
            ·
              refine ⟨22789794696407491879560563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15193196464271661253040375 22789794696407491879560563)
              ·
                refine ⟨34184692044611237819340845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22789794696407491879560563 34184692044611237819340845)
                ·
                  refine ⟨12819259516729214182252817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34184692044611237819340845 12819259516729214182252817)
                  ·
                    refine ⟨9614444637546910636689613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12819259516729214182252817 9614444637546910636689613)
                    ·
                      refine ⟨3605416739080091488758605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9614444637546910636689613 3605416739080091488758605)
                      ·
                        rfl

theorem cell23_7021524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_7021524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021524 prefixEnd_7021524 := by exact prefixLift 7021524
  have htrace : WordTrace (prefixWord ++ tailWord_7021524) baseStart_7021524 baseEnd_7021524 := by
    simpa [prefixWord, tailWord_7021524, baseEnd_7021524] using wordTrace_append hprefix tailTrace_7021524
  have hstable : (prefixWord ++ tailWord_7021524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021524).length < 2 ^ (prefixWord ++ tailWord_7021524).sum := by decide
  have hdescent : baseEnd_7021524 < baseStart_7021524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021538 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7021538 : Nat := 118140960795 + 7021538 * 2 ^ 59
def prefixEnd_7021538 : Nat := 4983230072969 + 3 ^ 40 * 7021538 * 2
def baseEnd_7021538 : Nat := 3605423927809254433983541

theorem tailTrace_7021538 : CollatzResearch.WordTrace tailWord_7021538 prefixEnd_7021538 3605423927809254433983541 := by
  unfold tailWord_7021538
  simp only [CollatzResearch.WordTrace]
  refine ⟨64024132509043621015914317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170731020024116322709104845 64024132509043621015914317)
  ·
    refine ⟨24009049690891357880967869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64024132509043621015914317 24009049690891357880967869)
    ·
      refine ⟨9003393634084259205362951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24009049690891357880967869 9003393634084259205362951)
      ·
        refine ⟨13505090451126388808044427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9003393634084259205362951 13505090451126388808044427)
        ·
          refine ⟨20257635676689583212066641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13505090451126388808044427 20257635676689583212066641)
          ·
            refine ⟨15193226757517187409049981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20257635676689583212066641 15193226757517187409049981)
            ·
              refine ⟨5697460034068945278393743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15193226757517187409049981 5697460034068945278393743)
              ·
                refine ⟨8546190051103417917590615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697460034068945278393743 8546190051103417917590615)
                ·
                  refine ⟨12819285076655126876385923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8546190051103417917590615 12819285076655126876385923)
                  ·
                    refine ⟨19228927614982690314578885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12819285076655126876385923 19228927614982690314578885)
                    ·
                      refine ⟨3605423927809254433983541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19228927614982690314578885 3605423927809254433983541)
                      ·
                        rfl

theorem cell23_7021538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7021538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021538 prefixEnd_7021538 := by exact prefixLift 7021538
  have htrace : WordTrace (prefixWord ++ tailWord_7021538) baseStart_7021538 baseEnd_7021538 := by
    simpa [prefixWord, tailWord_7021538, baseEnd_7021538] using wordTrace_append hprefix tailTrace_7021538
  have hstable : (prefixWord ++ tailWord_7021538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021538).length < 2 ^ (prefixWord ++ tailWord_7021538).sum := by decide
  have hdescent : baseEnd_7021538 < baseStart_7021538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021541 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 5]
def baseStart_7021541 : Nat := 118140960795 + 7021541 * 2 ^ 59
def prefixEnd_7021541 : Nat := 4983230072969 + 3 ^ 40 * 7021541 * 2
def baseEnd_7021541 : Nat := 3605425468251217922246027

theorem tailTrace_7021541 : CollatzResearch.WordTrace tailWord_7021541 prefixEnd_7021541 3605425468251217922246027 := by
  unfold tailWord_7021541
  simp only [CollatzResearch.WordTrace]
  refine ⟨256096639455163615576016477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170731092970109077050677651 256096639455163615576016477)
  ·
    refine ⟨96036239795686355841006179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256096639455163615576016477 96036239795686355841006179)
    ·
      refine ⟨144054359693529533761509269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96036239795686355841006179 144054359693529533761509269)
      ·
        refine ⟨6752548110634196895070747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144054359693529533761509269 6752548110634196895070747)
        ·
          refine ⟨10128822165951295342606121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752548110634196895070747 10128822165951295342606121)
          ·
            refine ⟨7596616624463471506954591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10128822165951295342606121 7596616624463471506954591)
            ·
              refine ⟨11394924936695207260431887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7596616624463471506954591 11394924936695207260431887)
              ·
                refine ⟨17092387405042810890647831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11394924936695207260431887 17092387405042810890647831)
                ·
                  refine ⟨25638581107564216335971747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17092387405042810890647831 25638581107564216335971747)
                  ·
                    refine ⟨38457871661346324503957621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25638581107564216335971747 38457871661346324503957621)
                    ·
                      refine ⟨3605425468251217922246027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38457871661346324503957621 3605425468251217922246027)
                      ·
                        rfl

theorem cell23_7021541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_7021541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021541 prefixEnd_7021541 := by exact prefixLift 7021541
  have htrace : WordTrace (prefixWord ++ tailWord_7021541) baseStart_7021541 baseEnd_7021541 := by
    simpa [prefixWord, tailWord_7021541, baseEnd_7021541] using wordTrace_append hprefix tailTrace_7021541
  have hstable : (prefixWord ++ tailWord_7021541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021541).length < 2 ^ (prefixWord ++ tailWord_7021541).sum := by decide
  have hdescent : baseEnd_7021541 < baseStart_7021541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021564 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 3, 3, 2]
def baseStart_7021564 : Nat := 118140960795 + 7021564 * 2 ^ 59
def prefixEnd_7021564 : Nat := 4983230072969 + 3 ^ 40 * 7021564 * 2
def baseEnd_7021564 : Nat := 3605437278306271332258421

theorem tailTrace_7021564 : CollatzResearch.WordTrace tailWord_7021564 prefixEnd_7021564 3605437278306271332258421 := by
  unfold tailWord_7021564
  simp only [CollatzResearch.WordTrace]
  refine ⟨128048739167040145252051873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170731652222720193669402497 128048739167040145252051873)
  ·
    refine ⟨96036554375280108939038905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128048739167040145252051873 96036554375280108939038905)
    ·
      refine ⟨72027415781460081704279179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96036554375280108939038905 72027415781460081704279179)
      ·
        refine ⟨108041123672190122556418769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72027415781460081704279179 108041123672190122556418769)
        ·
          refine ⟨81030842754142591917314077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108041123672190122556418769 81030842754142591917314077)
          ·
            refine ⟨30386566032803471968992779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81030842754142591917314077 30386566032803471968992779)
            ·
              refine ⟨45579849049205207953489169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30386566032803471968992779 45579849049205207953489169)
              ·
                refine ⟨34184886786903905965116877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45579849049205207953489169 34184886786903905965116877)
                ·
                  refine ⟨12819332545088964736918829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34184886786903905965116877 12819332545088964736918829)
                  ·
                    refine ⟨4807249704408361776344561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12819332545088964736918829 4807249704408361776344561)
                    ·
                      refine ⟨3605437278306271332258421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807249704408361776344561 3605437278306271332258421)
                      ·
                        rfl

theorem cell23_7021564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_7021564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021564 prefixEnd_7021564 := by exact prefixLift 7021564
  have htrace : WordTrace (prefixWord ++ tailWord_7021564) baseStart_7021564 baseEnd_7021564 := by
    simpa [prefixWord, tailWord_7021564, baseEnd_7021564] using wordTrace_append hprefix tailTrace_7021564
  have hstable : (prefixWord ++ tailWord_7021564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021564).length < 2 ^ (prefixWord ++ tailWord_7021564).sum := by decide
  have hdescent : baseEnd_7021564 < baseStart_7021564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021594 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2]
def baseStart_7021594 : Nat := 118140960795 + 7021594 * 2 ^ 59
def prefixEnd_7021594 : Nat := 4983230072969 + 3 ^ 40 * 7021594 * 2
def baseEnd_7021594 : Nat := 3605452682725906214883283

theorem tailTrace_7021594 : CollatzResearch.WordTrace tailWord_7021594 prefixEnd_7021594 3605452682725906214883283 := by
  unfold tailWord_7021594
  simp only [CollatzResearch.WordTrace]
  refine ⟨64024643130992901406923959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170732381682647737085130557 64024643130992901406923959)
  ·
    refine ⟨96036964696489352110385939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64024643130992901406923959 96036964696489352110385939)
    ·
      refine ⟨144055447044734028165578909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96036964696489352110385939 144055447044734028165578909)
      ·
        refine ⟨54020792641775260562092091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144055447044734028165578909 54020792641775260562092091)
        ·
          refine ⟨81031188962662890843138137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54020792641775260562092091 81031188962662890843138137)
          ·
            refine ⟨60773391721997168132353603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81031188962662890843138137 60773391721997168132353603)
            ·
              refine ⟨91160087582995752198530405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60773391721997168132353603 91160087582995752198530405)
              ·
                refine ⟨17092516421811703537224451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91160087582995752198530405 17092516421811703537224451)
                ·
                  refine ⟨25638774632717555305836677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17092516421811703537224451 25638774632717555305836677)
                  ·
                    refine ⟨4807270243634541619844377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25638774632717555305836677 4807270243634541619844377)
                    ·
                      refine ⟨3605452682725906214883283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807270243634541619844377 3605452682725906214883283)
                      ·
                        rfl

theorem cell23_7021594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_7021594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021594 prefixEnd_7021594 := by exact prefixLift 7021594
  have htrace : WordTrace (prefixWord ++ tailWord_7021594) baseStart_7021594 baseEnd_7021594 := by
    simpa [prefixWord, tailWord_7021594, baseEnd_7021594] using wordTrace_append hprefix tailTrace_7021594
  have hstable : (prefixWord ++ tailWord_7021594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021594).length < 2 ^ (prefixWord ++ tailWord_7021594).sum := by decide
  have hdescent : baseEnd_7021594 < baseStart_7021594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021617 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 7]
def baseStart_7021617 : Nat := 118140960795 + 7021617 * 2 ^ 59
def prefixEnd_7021617 : Nat := 4983230072969 + 3 ^ 40 * 7021617 * 2
def baseEnd_7021617 : Nat := 400607165864551069432853

theorem tailTrace_7021617 : CollatzResearch.WordTrace tailWord_7021617 prefixEnd_7021617 400607165864551069432853 := by
  unfold tailWord_7021617
  simp only [CollatzResearch.WordTrace]
  refine ⟨256099411402888280555783105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170732940935258853703855403 256099411402888280555783105)
  ·
    refine ⟨192074558552166210416837329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256099411402888280555783105 192074558552166210416837329)
    ·
      refine ⟨144055918914124657812627997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192074558552166210416837329 144055918914124657812627997)
      ·
        refine ⟨54020969592796746679735499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144055918914124657812627997 54020969592796746679735499)
        ·
          refine ⟨81031454389195120019603249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54020969592796746679735499 81031454389195120019603249)
          ·
            refine ⟨60773590791896340014702437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81031454389195120019603249 60773590791896340014702437)
            ·
              refine ⟨11395048273480563752756707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60773590791896340014702437 11395048273480563752756707)
              ·
                refine ⟨17092572410220845629135061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11395048273480563752756707 17092572410220845629135061)
                ·
                  refine ⟨400607165864551069432853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17092572410220845629135061 400607165864551069432853)
                  ·
                    rfl

theorem cell23_7021617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 7].length) (baseStart_7021617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021617 prefixEnd_7021617 := by exact prefixLift 7021617
  have htrace : WordTrace (prefixWord ++ tailWord_7021617) baseStart_7021617 baseEnd_7021617 := by
    simpa [prefixWord, tailWord_7021617, baseEnd_7021617] using wordTrace_append hprefix tailTrace_7021617
  have hstable : (prefixWord ++ tailWord_7021617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021617).length < 2 ^ (prefixWord ++ tailWord_7021617).sum := by decide
  have hdescent : baseEnd_7021617 < baseStart_7021617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021674 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_7021674 : Nat := 118140960795 + 7021674 * 2 ^ 59
def prefixEnd_7021674 : Nat := 4983230072969 + 3 ^ 40 * 7021674 * 2
def baseEnd_7021674 : Nat := 3605493761178265901882915

theorem tailTrace_7021674 : CollatzResearch.WordTrace tailWord_7021674 prefixEnd_7021674 3605493761178265901882915 := by
  unfold tailWord_7021674
  simp only [CollatzResearch.WordTrace]
  refine ⟨64025372590920444822652019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170734326909121186193738717 64025372590920444822652019)
  ·
    refine ⟨96038058886380667233978029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64025372590920444822652019 96038058886380667233978029)
    ·
      refine ⟨36014272082392750212741761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96038058886380667233978029 36014272082392750212741761)
      ·
        refine ⟨27010704061794562659556321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36014272082392750212741761 27010704061794562659556321)
        ·
          refine ⟨20258028046345921994667241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27010704061794562659556321 20258028046345921994667241)
          ·
            refine ⟨15193521034759441496000431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20258028046345921994667241 15193521034759441496000431)
            ·
              refine ⟨22790281552139162244000647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15193521034759441496000431 22790281552139162244000647)
              ·
                refine ⟨34185422328208743366000971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22790281552139162244000647 34185422328208743366000971)
                ·
                  refine ⟨51278133492313115049001457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34185422328208743366000971 51278133492313115049001457)
                  ·
                    refine ⟨38458600119234836286751093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51278133492313115049001457 38458600119234836286751093)
                    ·
                      refine ⟨3605493761178265901882915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38458600119234836286751093 3605493761178265901882915)
                      ·
                        rfl

theorem cell23_7021674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_7021674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021674 prefixEnd_7021674 := by exact prefixLift 7021674
  have htrace : WordTrace (prefixWord ++ tailWord_7021674) baseStart_7021674 baseEnd_7021674 := by
    simpa [prefixWord, tailWord_7021674, baseEnd_7021674] using wordTrace_append hprefix tailTrace_7021674
  have hstable : (prefixWord ++ tailWord_7021674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021674).length < 2 ^ (prefixWord ++ tailWord_7021674).sum := by decide
  have hdescent : baseEnd_7021674 < baseStart_7021674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021701 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 4]
def baseStart_7021701 : Nat := 118140960795 + 7021701 * 2 ^ 59
def prefixEnd_7021701 : Nat := 4983230072969 + 3 ^ 40 * 7021701 * 2
def baseEnd_7021701 : Nat := 3605507625155937296245291

theorem tailTrace_7021701 : CollatzResearch.WordTrace tailWord_7021701 prefixEnd_7021701 3605507625155937296245291 := by
  unfold tailWord_7021701
  simp only [CollatzResearch.WordTrace]
  refine ⟨256102475134583962901840957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170734983423055975267893971 256102475134583962901840957)
  ·
    refine ⟨96038428175468986088190359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256102475134583962901840957 96038428175468986088190359)
    ·
      refine ⟨144057642263203479132285539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96038428175468986088190359 144057642263203479132285539)
      ·
        refine ⟨216086463394805218698428309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144057642263203479132285539 216086463394805218698428309)
        ·
          refine ⟨10129052971631494626488827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 216086463394805218698428309 10129052971631494626488827)
          ·
            refine ⟨15193579457447241939733241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10129052971631494626488827 15193579457447241939733241)
            ·
              refine ⟨11395184593085431454799931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15193579457447241939733241 11395184593085431454799931)
              ·
                refine ⟨17092776889628147182199897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11395184593085431454799931 17092776889628147182199897)
                ·
                  refine ⟨12819582667221110386649923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17092776889628147182199897 12819582667221110386649923)
                  ·
                    refine ⟨19229374000831665579974885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12819582667221110386649923 19229374000831665579974885)
                    ·
                      refine ⟨3605507625155937296245291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19229374000831665579974885 3605507625155937296245291)
                      ·
                        rfl

theorem cell23_7021701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_7021701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021701 prefixEnd_7021701 := by exact prefixLift 7021701
  have htrace : WordTrace (prefixWord ++ tailWord_7021701) baseStart_7021701 baseEnd_7021701 := by
    simpa [prefixWord, tailWord_7021701, baseEnd_7021701] using wordTrace_append hprefix tailTrace_7021701
  have hstable : (prefixWord ++ tailWord_7021701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021701).length < 2 ^ (prefixWord ++ tailWord_7021701).sum := by decide
  have hdescent : baseEnd_7021701 < baseStart_7021701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021724 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 6]
def baseStart_7021724 : Nat := 118140960795 + 7021724 * 2 ^ 59
def prefixEnd_7021724 : Nat := 4983230072969 + 3 ^ 40 * 7021724 * 2
def baseEnd_7021724 : Nat := 400613270578998967361965

theorem tailTrace_7021724 : CollatzResearch.WordTrace tailWord_7021724 prefixEnd_7021724 400613270578998967361965 := by
  unfold tailWord_7021724
  simp only [CollatzResearch.WordTrace]
  refine ⟨128051657006750318914964113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170735542675667091886618817 128051657006750318914964113)
  ·
    refine ⟨96038742755062739186223085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128051657006750318914964113 96038742755062739186223085)
    ·
      refine ⟨36014528533148527194833657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96038742755062739186223085 36014528533148527194833657)
      ·
        refine ⟨27010896399861395396125243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36014528533148527194833657 27010896399861395396125243)
        ·
          refine ⟨40516344599792093094187865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27010896399861395396125243 40516344599792093094187865)
          ·
            refine ⟨30387258449844069820640899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40516344599792093094187865 30387258449844069820640899)
            ·
              refine ⟨45580887674766104730961349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30387258449844069820640899 45580887674766104730961349)
              ·
                refine ⟨8546416439018644637055253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45580887674766104730961349 8546416439018644637055253)
                ·
                  refine ⟨400613270578998967361965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8546416439018644637055253 400613270578998967361965)
                  ·
                    rfl

theorem cell23_7021724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 6].length) (baseStart_7021724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021724 prefixEnd_7021724 := by exact prefixLift 7021724
  have htrace : WordTrace (prefixWord ++ tailWord_7021724) baseStart_7021724 baseEnd_7021724 := by
    simpa [prefixWord, tailWord_7021724, baseEnd_7021724] using wordTrace_append hprefix tailTrace_7021724
  have hstable : (prefixWord ++ tailWord_7021724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021724).length < 2 ^ (prefixWord ++ tailWord_7021724).sum := by decide
  have hdescent : baseEnd_7021724 < baseStart_7021724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021744 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 3, 5, 2]
def baseStart_7021744 : Nat := 118140960795 + 7021744 * 2 ^ 59
def prefixEnd_7021744 : Nat := 4983230072969 + 3 ^ 40 * 7021744 * 2
def baseEnd_7021744 : Nat := 3605529704824080628007593

theorem tailTrace_7021744 : CollatzResearch.WordTrace tailWord_7021744 prefixEnd_7021744 3605529704824080628007593 := by
  unfold tailWord_7021744
  simp only [CollatzResearch.WordTrace]
  refine ⟨128052021736714090622828143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170736028982285454163770857 128052021736714090622828143)
  ·
    refine ⟨192078032605071135934242215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128052021736714090622828143 192078032605071135934242215)
    ·
      refine ⟨288117048907606703901363323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192078032605071135934242215 288117048907606703901363323)
      ·
        refine ⟨432175573361410055852044985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288117048907606703901363323 432175573361410055852044985)
        ·
          refine ⟨324131680021057541889033739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432175573361410055852044985 324131680021057541889033739)
          ·
            refine ⟨486197520031586312833550609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324131680021057541889033739 486197520031586312833550609)
            ·
              refine ⟨364648140023689734625162957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486197520031586312833550609 364648140023689734625162957)
              ·
                refine ⟨136743052508883650484436109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364648140023689734625162957 136743052508883650484436109)
                ·
                  refine ⟨51278644690831368931663541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136743052508883650484436109 51278644690831368931663541)
                  ·
                    refine ⟨4807372939765440837343457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51278644690831368931663541 4807372939765440837343457)
                    ·
                      refine ⟨3605529704824080628007593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807372939765440837343457 3605529704824080628007593)
                      ·
                        rfl

theorem cell23_7021744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 5, 2].length) (baseStart_7021744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021744 prefixEnd_7021744 := by exact prefixLift 7021744
  have htrace : WordTrace (prefixWord ++ tailWord_7021744) baseStart_7021744 baseEnd_7021744 := by
    simpa [prefixWord, tailWord_7021744, baseEnd_7021744] using wordTrace_append hprefix tailTrace_7021744
  have hstable : (prefixWord ++ tailWord_7021744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021744).length < 2 ^ (prefixWord ++ tailWord_7021744).sum := by decide
  have hdescent : baseEnd_7021744 < baseStart_7021744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021751 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 3, 1, 3]
def baseStart_7021751 : Nat := 118140960795 + 7021751 * 2 ^ 59
def prefixEnd_7021751 : Nat := 4983230072969 + 3 ^ 40 * 7021751 * 2
def baseEnd_7021751 : Nat := 3605533299188662100620061

theorem tailTrace_7021751 : CollatzResearch.WordTrace tailWord_7021751 prefixEnd_7021751 3605533299188662100620061 := by
  unfold tailWord_7021751
  simp only [CollatzResearch.WordTrace]
  refine ⟨256104298784402821441161107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170736199189601880960774071 256104298784402821441161107)
  ·
    refine ⟨384156448176604232161741661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256104298784402821441161107 384156448176604232161741661)
    ·
      refine ⟨144058668066226587060653123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384156448176604232161741661 144058668066226587060653123)
      ·
        refine ⟨216088002099339880590979685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144058668066226587060653123 216088002099339880590979685)
        ·
          refine ⟨40516500393626227610808691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216088002099339880590979685 40516500393626227610808691)
          ·
            refine ⟨60774750590439341416213037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40516500393626227610808691 60774750590439341416213037)
            ·
              refine ⟨22790531471414753031079889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60774750590439341416213037 22790531471414753031079889)
              ·
                refine ⟨17092898603561064773309917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22790531471414753031079889 17092898603561064773309917)
                ·
                  refine ⟨6409836976335399289991219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17092898603561064773309917 6409836976335399289991219)
                  ·
                    refine ⟨9614755464503098934986829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6409836976335399289991219 9614755464503098934986829)
                    ·
                      refine ⟨3605533299188662100620061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9614755464503098934986829 3605533299188662100620061)
                      ·
                        rfl

theorem cell23_7021751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_7021751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021751 prefixEnd_7021751 := by exact prefixLift 7021751
  have htrace : WordTrace (prefixWord ++ tailWord_7021751) baseStart_7021751 baseEnd_7021751 := by
    simpa [prefixWord, tailWord_7021751, baseEnd_7021751] using wordTrace_append hprefix tailTrace_7021751
  have hstable : (prefixWord ++ tailWord_7021751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021751).length < 2 ^ (prefixWord ++ tailWord_7021751).sum := by decide
  have hdescent : baseEnd_7021751 < baseStart_7021751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021754 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 1, 5]
def baseStart_7021754 : Nat := 118140960795 + 7021754 * 2 ^ 59
def prefixEnd_7021754 : Nat := 4983230072969 + 3 ^ 40 * 7021754 * 2
def baseEnd_7021754 : Nat := 1201844946543541862960849

theorem tailTrace_7021754 : CollatzResearch.WordTrace tailWord_7021754 prefixEnd_7021754 1201844946543541862960849 := by
  unfold tailWord_7021754
  simp only [CollatzResearch.WordTrace]
  refine ⟨64026102050847988238380079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170736272135594635302346877 64026102050847988238380079)
  ·
    refine ⟨96039153076271982357570119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64026102050847988238380079 96039153076271982357570119)
    ·
      refine ⟨144058729614407973536355179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96039153076271982357570119 144058729614407973536355179)
      ·
        refine ⟨216088094421611960304532769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144058729614407973536355179 216088094421611960304532769)
        ·
          refine ⟨162066070816208970228399577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216088094421611960304532769 162066070816208970228399577)
          ·
            refine ⟨121549553112156727671299683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162066070816208970228399577 121549553112156727671299683)
            ·
              refine ⟨182324329668235091506949525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121549553112156727671299683 182324329668235091506949525)
              ·
                refine ⟨8546452953198519914388259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182324329668235091506949525 8546452953198519914388259)
                ·
                  refine ⟨12819679429797779871582389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8546452953198519914388259 12819679429797779871582389)
                  ·
                    refine ⟨1201844946543541862960849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12819679429797779871582389 1201844946543541862960849)
                    ·
                      rfl

theorem cell23_7021754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 5].length) (baseStart_7021754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021754 prefixEnd_7021754 := by exact prefixLift 7021754
  have htrace : WordTrace (prefixWord ++ tailWord_7021754) baseStart_7021754 baseEnd_7021754 := by
    simpa [prefixWord, tailWord_7021754, baseEnd_7021754] using wordTrace_append hprefix tailTrace_7021754
  have hstable : (prefixWord ++ tailWord_7021754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021754).length < 2 ^ (prefixWord ++ tailWord_7021754).sum := by decide
  have hdescent : baseEnd_7021754 < baseStart_7021754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021768 : List Nat := [2, 1, 3, 1, 2, 1, 3, 5, 1, 1, 3]
def baseStart_7021768 : Nat := 118140960795 + 7021768 * 2 ^ 59
def prefixEnd_7021768 : Nat := 4983230072969 + 3 ^ 40 * 7021768 * 2
def baseEnd_7021768 : Nat := 3605542028359788534107483

theorem tailTrace_7021768 : CollatzResearch.WordTrace tailWord_7021768 prefixEnd_7021768 3605542028359788534107483 := by
  unfold tailWord_7021768
  simp only [CollatzResearch.WordTrace]
  refine ⟨128052459412670616672264979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170736612550227488896353305 128052459412670616672264979)
  ·
    refine ⟨192078689119005925008397469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128052459412670616672264979 192078689119005925008397469)
    ·
      refine ⟨72029508419627221878149051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192078689119005925008397469 72029508419627221878149051)
      ·
        refine ⟨108044262629440832817223577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72029508419627221878149051 108044262629440832817223577)
        ·
          refine ⟨81033196972080624612917683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108044262629440832817223577 81033196972080624612917683)
          ·
            refine ⟨121549795458120936919376525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81033196972080624612917683 121549795458120936919376525)
            ·
              refine ⟨45581173296795351344766197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121549795458120936919376525 45581173296795351344766197)
              ·
                refine ⟨4273234996574564188571831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45581173296795351344766197 4273234996574564188571831)
                ·
                  refine ⟨6409852494861846282857747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4273234996574564188571831 6409852494861846282857747)
                  ·
                    refine ⟨9614778742292769424286621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6409852494861846282857747 9614778742292769424286621)
                    ·
                      refine ⟨3605542028359788534107483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9614778742292769424286621 3605542028359788534107483)
                      ·
                        rfl

theorem cell23_7021768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_7021768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021768 prefixEnd_7021768 := by exact prefixLift 7021768
  have htrace : WordTrace (prefixWord ++ tailWord_7021768) baseStart_7021768 baseEnd_7021768 := by
    simpa [prefixWord, tailWord_7021768, baseEnd_7021768] using wordTrace_append hprefix tailTrace_7021768
  have hstable : (prefixWord ++ tailWord_7021768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021768).length < 2 ^ (prefixWord ++ tailWord_7021768).sum := by decide
  have hdescent : baseEnd_7021768 < baseStart_7021768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021804 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_7021804 : Nat := 118140960795 + 7021804 * 2 ^ 59
def prefixEnd_7021804 : Nat := 4983230072969 + 3 ^ 40 * 7021804 * 2
def baseEnd_7021804 : Nat := 3605560513663350393257317

theorem tailTrace_7021804 : CollatzResearch.WordTrace tailWord_7021804 prefixEnd_7021804 3605560513663350393257317 := by
  unfold tailWord_7021804
  simp only [CollatzResearch.WordTrace]
  refine ⟨128053115926605405746420233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170737487902140540995226977 128053115926605405746420233)
  ·
    refine ⟨96039836944954054309815175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128053115926605405746420233 96039836944954054309815175)
    ·
      refine ⟨144059755417431081464722763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96039836944954054309815175 144059755417431081464722763)
      ·
        refine ⟨216089633126146622197084145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144059755417431081464722763 216089633126146622197084145)
        ·
          refine ⟨162067224844609966647813109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216089633126146622197084145 162067224844609966647813109)
          ·
            refine ⟨15193802329182184373232479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162067224844609966647813109 15193802329182184373232479)
            ·
              refine ⟨22790703493773276559848719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15193802329182184373232479 22790703493773276559848719)
              ·
                refine ⟨34186055240659914839773079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22790703493773276559848719 34186055240659914839773079)
                ·
                  refine ⟨51279082860989872259659619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34186055240659914839773079 51279082860989872259659619)
                  ·
                    refine ⟨76918624291484808389489429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51279082860989872259659619 76918624291484808389489429)
                    ·
                      refine ⟨3605560513663350393257317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76918624291484808389489429 3605560513663350393257317)
                      ·
                        rfl

theorem cell23_7021804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_7021804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021804 prefixEnd_7021804 := by exact prefixLift 7021804
  have htrace : WordTrace (prefixWord ++ tailWord_7021804) baseStart_7021804 baseEnd_7021804 := by
    simpa [prefixWord, tailWord_7021804, baseEnd_7021804] using wordTrace_append hprefix tailTrace_7021804
  have hstable : (prefixWord ++ tailWord_7021804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021804).length < 2 ^ (prefixWord ++ tailWord_7021804).sum := by decide
  have hdescent : baseEnd_7021804 < baseStart_7021804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021811 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 1, 2, 3]
def baseStart_7021811 : Nat := 118140960795 + 7021811 * 2 ^ 59
def prefixEnd_7021811 : Nat := 4983230072969 + 3 ^ 40 * 7021811 * 2
def baseEnd_7021811 : Nat := 3605564108027931865869785

theorem tailTrace_7021811 : CollatzResearch.WordTrace tailWord_7021811 prefixEnd_7021811 3605564108027931865869785 := by
  unfold tailWord_7021811
  simp only [CollatzResearch.WordTrace]
  refine ⟨256106487164185451688345287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170737658109456967792230191 256106487164185451688345287)
  ·
    refine ⟨384159730746278177532517931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256106487164185451688345287 384159730746278177532517931)
    ·
      refine ⟨576239596119417266298776897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384159730746278177532517931 576239596119417266298776897)
      ·
        refine ⟨432179697089562949724082673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576239596119417266298776897 432179697089562949724082673)
        ·
          refine ⟨324134772817172212293062005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432179697089562949724082673 324134772817172212293062005)
          ·
            refine ⟨30387634951609894902474563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 324134772817172212293062005 30387634951609894902474563)
            ·
              refine ⟨45581452427414842353711845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30387634951609894902474563 45581452427414842353711845)
              ·
                refine ⟨8546522330140282941320971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45581452427414842353711845 8546522330140282941320971)
                ·
                  refine ⟨12819783495210424411981457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8546522330140282941320971 12819783495210424411981457)
                  ·
                    refine ⟨9614837621407818308986093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12819783495210424411981457 9614837621407818308986093)
                    ·
                      refine ⟨3605564108027931865869785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9614837621407818308986093 3605564108027931865869785)
                      ·
                        rfl

theorem cell23_7021811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 2, 3].length) (baseStart_7021811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021811 prefixEnd_7021811 := by exact prefixLift 7021811
  have htrace : WordTrace (prefixWord ++ tailWord_7021811) baseStart_7021811 baseEnd_7021811 := by
    simpa [prefixWord, tailWord_7021811, baseEnd_7021811] using wordTrace_append hprefix tailTrace_7021811
  have hstable : (prefixWord ++ tailWord_7021811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021811).length < 2 ^ (prefixWord ++ tailWord_7021811).sum := by decide
  have hdescent : baseEnd_7021811 < baseStart_7021811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021824 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 3]
def baseStart_7021824 : Nat := 118140960795 + 7021824 * 2 ^ 59
def prefixEnd_7021824 : Nat := 4983230072969 + 3 ^ 40 * 7021824 * 2
def baseEnd_7021824 : Nat := 3605570783276440315007225

theorem tailTrace_7021824 : CollatzResearch.WordTrace tailWord_7021824 prefixEnd_7021824 3605570783276440315007225 := by
  unfold tailWord_7021824
  simp only [CollatzResearch.WordTrace]
  refine ⟨128053480656569177454284263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170737974208758903272379017 128053480656569177454284263)
  ·
    refine ⟨192080220984853766181426395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128053480656569177454284263 192080220984853766181426395)
    ·
      refine ⟨288120331477280649272139593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192080220984853766181426395 288120331477280649272139593)
      ·
        refine ⟨216090248607960486954104695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288120331477280649272139593 216090248607960486954104695)
        ·
          refine ⟨324135372911940730431157043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216090248607960486954104695 324135372911940730431157043)
          ·
            refine ⟨486203059367911095646735565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324135372911940730431157043 486203059367911095646735565)
            ·
              refine ⟨182326147262966660867525837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 486203059367911095646735565 182326147262966660867525837)
              ·
                refine ⟨68372305223612497825322189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182326147262966660867525837 68372305223612497825322189)
                ·
                  refine ⟨25639614458854686684495821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68372305223612497825322189 25639614458854686684495821)
                  ·
                    refine ⟨9614855422070507506685933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25639614458854686684495821 9614855422070507506685933)
                    ·
                      refine ⟨3605570783276440315007225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9614855422070507506685933 3605570783276440315007225)
                      ·
                        rfl

theorem cell23_7021824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_7021824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021824 prefixEnd_7021824 := by exact prefixLift 7021824
  have htrace : WordTrace (prefixWord ++ tailWord_7021824) baseStart_7021824 baseEnd_7021824 := by
    simpa [prefixWord, tailWord_7021824, baseEnd_7021824] using wordTrace_append hprefix tailTrace_7021824
  have hstable : (prefixWord ++ tailWord_7021824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021824).length < 2 ^ (prefixWord ++ tailWord_7021824).sum := by decide
  have hdescent : baseEnd_7021824 < baseStart_7021824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021828 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_7021828 : Nat := 118140960795 + 7021828 * 2 ^ 59
def prefixEnd_7021828 : Nat := 4983230072969 + 3 ^ 40 * 7021828 * 2
def baseEnd_7021828 : Nat := 3605572837199058299357207

theorem tailTrace_7021828 : CollatzResearch.WordTrace tailWord_7021828 prefixEnd_7021828 3605572837199058299357207 := by
  unfold tailWord_7021828
  simp only [CollatzResearch.WordTrace]
  refine ⟨128053553602561931795857069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170738071470082575727809425 128053553602561931795857069)
  ·
    refine ⟨48020082600960724423446401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128053553602561931795857069 48020082600960724423446401)
    ·
      refine ⟨36015061950720543317584801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48020082600960724423446401 36015061950720543317584801)
      ·
        refine ⟨27011296463040407488188601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36015061950720543317584801 27011296463040407488188601)
        ·
          refine ⟨20258472347280305616141451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27011296463040407488188601 20258472347280305616141451)
          ·
            refine ⟨30387708520920458424212177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20258472347280305616141451 30387708520920458424212177)
            ·
              refine ⟨22790781390690343818159133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30387708520920458424212177 22790781390690343818159133)
              ·
                refine ⟨8546543021508878931809675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22790781390690343818159133 8546543021508878931809675)
                ·
                  refine ⟨12819814532263318397714513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8546543021508878931809675 12819814532263318397714513)
                  ·
                    refine ⟨9614860899197488798285885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12819814532263318397714513 9614860899197488798285885)
                    ·
                      refine ⟨3605572837199058299357207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9614860899197488798285885 3605572837199058299357207)
                      ·
                        rfl

theorem cell23_7021828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_7021828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021828 prefixEnd_7021828 := by exact prefixLift 7021828
  have htrace : WordTrace (prefixWord ++ tailWord_7021828) baseStart_7021828 baseEnd_7021828 := by
    simpa [prefixWord, tailWord_7021828, baseEnd_7021828] using wordTrace_append hprefix tailTrace_7021828
  have hstable : (prefixWord ++ tailWord_7021828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021828).length < 2 ^ (prefixWord ++ tailWord_7021828).sum := by decide
  have hdescent : baseEnd_7021828 < baseStart_7021828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021841 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 4, 1, 3]
def baseStart_7021841 : Nat := 118140960795 + 7021841 * 2 ^ 59
def prefixEnd_7021841 : Nat := 4983230072969 + 3 ^ 40 * 7021841 * 2
def baseEnd_7021841 : Nat := 3605579512447566748494647

theorem tailTrace_7021841 : CollatzResearch.WordTrace tailWord_7021841 prefixEnd_7021841 3605579512447566748494647 := by
  unfold tailWord_7021841
  simp only [CollatzResearch.WordTrace]
  refine ⟨256107581354076766811937377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170738387569384511207958251 256107581354076766811937377)
  ·
    refine ⟨192080686015557575108953033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256107581354076766811937377 192080686015557575108953033)
    ·
      refine ⟨144060514511668181331714775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192080686015557575108953033 144060514511668181331714775)
      ·
        refine ⟨216090771767502271997572163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144060514511668181331714775 216090771767502271997572163)
        ·
          refine ⟨324136157651253407996358245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216090771767502271997572163 324136157651253407996358245)
          ·
            refine ⟨60775529559610013999317171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 324136157651253407996358245 60775529559610013999317171)
            ·
              refine ⟨91163294339415020998975757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60775529559610013999317171 91163294339415020998975757)
              ·
                refine ⟨34186235377280632874615909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91163294339415020998975757 34186235377280632874615909)
                ·
                  refine ⟨6409919133240118663990483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34186235377280632874615909 6409919133240118663990483)
                  ·
                    refine ⟨9614878699860177995985725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6409919133240118663990483 9614878699860177995985725)
                    ·
                      refine ⟨3605579512447566748494647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9614878699860177995985725 3605579512447566748494647)
                      ·
                        rfl

theorem cell23_7021841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_7021841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021841 prefixEnd_7021841 := by exact prefixLift 7021841
  have htrace : WordTrace (prefixWord ++ tailWord_7021841) baseStart_7021841 baseEnd_7021841 := by
    simpa [prefixWord, tailWord_7021841, baseEnd_7021841] using wordTrace_append hprefix tailTrace_7021841
  have hstable : (prefixWord ++ tailWord_7021841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021841).length < 2 ^ (prefixWord ++ tailWord_7021841).sum := by decide
  have hdescent : baseEnd_7021841 < baseStart_7021841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021851 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 3, 3, 2]
def baseStart_7021851 : Nat := 118140960795 + 7021851 * 2 ^ 59
def prefixEnd_7021851 : Nat := 4983230072969 + 3 ^ 40 * 7021851 * 2
def baseEnd_7021851 : Nat := 3605584647254111709369601

theorem tailTrace_7021851 : CollatzResearch.WordTrace tailWord_7021851 prefixEnd_7021851 3605584647254111709369601 := by
  unfold tailWord_7021851
  simp only [CollatzResearch.WordTrace]
  refine ⟨256107946084040538519801407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170738630722693692346534271 256107946084040538519801407)
  ·
    refine ⟨384161919126060807779702111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256107946084040538519801407 384161919126060807779702111)
    ·
      refine ⟨576242878689091211669553167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384161919126060807779702111 576242878689091211669553167)
      ·
        refine ⟨864364318033636817504329751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576242878689091211669553167 864364318033636817504329751)
        ·
          refine ⟨1296546477050455226256494627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864364318033636817504329751 1296546477050455226256494627)
          ·
            refine ⟨1944819715575682839384741941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296546477050455226256494627 1944819715575682839384741941)
            ·
              refine ⟨182326848335220266192319557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1944819715575682839384741941 182326848335220266192319557)
              ·
                refine ⟨34186284062853799911059917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182326848335220266192319557 34186284062853799911059917)
                ·
                  refine ⟨12819856523570174966647469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34186284062853799911059917 12819856523570174966647469)
                  ·
                    refine ⟨4807446196338815612492801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12819856523570174966647469 4807446196338815612492801)
                    ·
                      refine ⟨3605584647254111709369601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807446196338815612492801 3605584647254111709369601)
                      ·
                        rfl

theorem cell23_7021851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 3, 2].length) (baseStart_7021851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021851 prefixEnd_7021851 := by exact prefixLift 7021851
  have htrace : WordTrace (prefixWord ++ tailWord_7021851) baseStart_7021851 baseEnd_7021851 := by
    simpa [prefixWord, tailWord_7021851, baseEnd_7021851] using wordTrace_append hprefix tailTrace_7021851
  have hstable : (prefixWord ++ tailWord_7021851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021851).length < 2 ^ (prefixWord ++ tailWord_7021851).sum := by decide
  have hdescent : baseEnd_7021851 < baseStart_7021851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021892 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_7021892 : Nat := 118140960795 + 7021892 * 2 ^ 59
def prefixEnd_7021892 : Nat := 4983230072969 + 3 ^ 40 * 7021892 * 2
def baseEnd_7021892 : Nat := 3605605699960946048956913

theorem tailTrace_7021892 : CollatzResearch.WordTrace tailWord_7021892 prefixEnd_7021892 3605605699960946048956913 := by
  unfold tailWord_7021892
  simp only [CollatzResearch.WordTrace]
  refine ⟨128054720738446001261021965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170739627651261335014695953 128054720738446001261021965)
  ·
    refine ⟨48020520276917250472883237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128054720738446001261021965 48020520276917250472883237)
    ·
      refine ⟨9003847551921984463665607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48020520276917250472883237 9003847551921984463665607)
      ·
        refine ⟨13505771327882976695498411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9003847551921984463665607 13505771327882976695498411)
        ·
          refine ⟨20258656991824465043247617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13505771327882976695498411 20258656991824465043247617)
          ·
            refine ⟨15193992743868348782435713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20258656991824465043247617 15193992743868348782435713)
            ·
              refine ⟨11395494557901261586826785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15193992743868348782435713 11395494557901261586826785)
              ·
                refine ⟨8546620918425946190120089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11395494557901261586826785 8546620918425946190120089)
                ·
                  refine ⟨6409965688819459642590067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8546620918425946190120089 6409965688819459642590067)
                  ·
                    refine ⟨9614948533229189463885101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6409965688819459642590067 9614948533229189463885101)
                    ·
                      refine ⟨3605605699960946048956913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9614948533229189463885101 3605605699960946048956913)
                      ·
                        rfl

theorem cell23_7021892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_7021892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021892 prefixEnd_7021892 := by exact prefixLift 7021892
  have htrace : WordTrace (prefixWord ++ tailWord_7021892) baseStart_7021892 baseEnd_7021892 := by
    simpa [prefixWord, tailWord_7021892, baseEnd_7021892] using wordTrace_append hprefix tailTrace_7021892
  have hstable : (prefixWord ++ tailWord_7021892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021892).length < 2 ^ (prefixWord ++ tailWord_7021892).sum := by decide
  have hdescent : baseEnd_7021892 < baseStart_7021892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021898 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2]
def baseStart_7021898 : Nat := 118140960795 + 7021898 * 2 ^ 59
def prefixEnd_7021898 : Nat := 4983230072969 + 3 ^ 40 * 7021898 * 2
def baseEnd_7021898 : Nat := 3605608780844873025481885

theorem tailTrace_7021898 : CollatzResearch.WordTrace tailWord_7021898 prefixEnd_7021898 3605608780844873025481885 := by
  unfold tailWord_7021898
  simp only [CollatzResearch.WordTrace]
  refine ⟨64027415078717566386690587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170739773543246843697841565 64027415078717566386690587)
  ·
    refine ⟨96041122618076349580035881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64027415078717566386690587 96041122618076349580035881)
    ·
      refine ⟨72030841963557262185026911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96041122618076349580035881 72030841963557262185026911)
      ·
        refine ⟨108046262945335893277540367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72030841963557262185026911 108046262945335893277540367)
        ·
          refine ⟨162069394418003839916310551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108046262945335893277540367 162069394418003839916310551)
          ·
            refine ⟨243104091627005759874465827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162069394418003839916310551 243104091627005759874465827)
            ·
              refine ⟨364656137440508639811698741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243104091627005759874465827 364656137440508639811698741)
              ·
                refine ⟨34186512885047684982346757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 364656137440508639811698741 34186512885047684982346757)
                ·
                  refine ⟨6409971165946440934190017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34186512885047684982346757 6409971165946440934190017)
                  ·
                    refine ⟨4807478374459830700642513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6409971165946440934190017 4807478374459830700642513)
                    ·
                      refine ⟨3605608780844873025481885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807478374459830700642513 3605608780844873025481885)
                      ·
                        rfl

theorem cell23_7021898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_7021898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021898 prefixEnd_7021898 := by exact prefixLift 7021898
  have htrace : WordTrace (prefixWord ++ tailWord_7021898) baseStart_7021898 baseEnd_7021898 := by
    simpa [prefixWord, tailWord_7021898, baseEnd_7021898] using wordTrace_append hprefix tailTrace_7021898
  have hstable : (prefixWord ++ tailWord_7021898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021898).length < 2 ^ (prefixWord ++ tailWord_7021898).sum := by decide
  have hdescent : baseEnd_7021898 < baseStart_7021898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021904 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 7]
def baseStart_7021904 : Nat := 118140960795 + 7021904 * 2 ^ 59
def prefixEnd_7021904 : Nat := 4983230072969 + 3 ^ 40 * 7021904 * 2
def baseEnd_7021904 : Nat := 400623540192088889111873

theorem tailTrace_7021904 : CollatzResearch.WordTrace tailWord_7021904 prefixEnd_7021904 400623540192088889111873 := by
  unfold tailWord_7021904
  simp only [CollatzResearch.WordTrace]
  refine ⟨128054939576424264285740383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170739919435232352380987177 128054939576424264285740383)
  ·
    refine ⟨192082409364636396428610575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128054939576424264285740383 192082409364636396428610575)
    ·
      refine ⟨288123614046954594642915863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192082409364636396428610575 288123614046954594642915863)
      ·
        refine ⟨432185421070431891964373795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288123614046954594642915863 432185421070431891964373795)
        ·
          refine ⟨648278131605647837946560693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432185421070431891964373795 648278131605647837946560693)
          ·
            refine ⟨60776074838029484807490065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 648278131605647837946560693 60776074838029484807490065)
            ·
              refine ⟨45582056128522113605617549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60776074838029484807490065 45582056128522113605617549)
              ·
                refine ⟨17093271048195792602106581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45582056128522113605617549 17093271048195792602106581)
                ·
                  refine ⟨400623540192088889111873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17093271048195792602106581 400623540192088889111873)
                  ·
                    rfl

theorem cell23_7021904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 7].length) (baseStart_7021904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021904 prefixEnd_7021904 := by exact prefixLift 7021904
  have htrace : WordTrace (prefixWord ++ tailWord_7021904) baseStart_7021904 baseEnd_7021904 := by
    simpa [prefixWord, tailWord_7021904, baseEnd_7021904] using wordTrace_append hprefix tailTrace_7021904
  have hstable : (prefixWord ++ tailWord_7021904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021904).length < 2 ^ (prefixWord ++ tailWord_7021904).sum := by decide
  have hdescent : baseEnd_7021904 < baseStart_7021904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021911 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_7021911 : Nat := 118140960795 + 7021911 * 2 ^ 59
def prefixEnd_7021911 : Nat := 4983230072969 + 3 ^ 40 * 7021911 * 2
def baseEnd_7021911 : Nat := 3605615456093381474619325

theorem tailTrace_7021911 : CollatzResearch.WordTrace tailWord_7021911 prefixEnd_7021911 3605615456093381474619325 := by
  unfold tailWord_7021911
  simp only [CollatzResearch.WordTrace]
  refine ⟨256110134463823168766985587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170740089642548779177990391 256110134463823168766985587)
  ·
    refine ⟨384165201695734753150478381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256110134463823168766985587 384165201695734753150478381)
    ·
      refine ⟨144061950635900532431429393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384165201695734753150478381 144061950635900532431429393)
      ·
        refine ⟨108046462976925399323572045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144061950635900532431429393 108046462976925399323572045)
        ·
          refine ⟨40517423616347024746339517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108046462976925399323572045 40517423616347024746339517)
          ·
            refine ⟨15194033856130134279877319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40517423616347024746339517 15194033856130134279877319)
            ·
              refine ⟨22791050784195201419815979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15194033856130134279877319 22791050784195201419815979)
              ·
                refine ⟨34186576176292802129723969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22791050784195201419815979 34186576176292802129723969)
                ·
                  refine ⟨25639932132219601597292977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34186576176292802129723969 25639932132219601597292977)
                  ·
                    refine ⟨19229949099164701197969733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25639932132219601597292977 19229949099164701197969733)
                    ·
                      refine ⟨3605615456093381474619325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19229949099164701197969733 3605615456093381474619325)
                      ·
                        rfl

theorem cell23_7021911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_7021911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021911 prefixEnd_7021911 := by exact prefixLift 7021911
  have htrace : WordTrace (prefixWord ++ tailWord_7021911) baseStart_7021911 baseEnd_7021911 := by
    simpa [prefixWord, tailWord_7021911, baseEnd_7021911] using wordTrace_append hprefix tailTrace_7021911
  have hstable : (prefixWord ++ tailWord_7021911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021911).length < 2 ^ (prefixWord ++ tailWord_7021911).sum := by decide
  have hdescent : baseEnd_7021911 < baseStart_7021911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7021938 : List Nat := [3, 2, 1, 2, 1, 2, 4, 3, 5]
def baseStart_7021938 : Nat := 118140960795 + 7021938 * 2 ^ 59
def prefixEnd_7021938 : Nat := 4983230072969 + 3 ^ 40 * 7021938 * 2
def baseEnd_7021938 : Nat := 400625480007894763220189

theorem tailTrace_7021938 : CollatzResearch.WordTrace tailWord_7021938 prefixEnd_7021938 400625480007894763220189 := by
  unfold tailWord_7021938
  simp only [CollatzResearch.WordTrace]
  refine ⟨64027779808681338094554617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170740746156483568252145645 64027779808681338094554617)
  ·
    refine ⟨48020834856511003570915963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64027779808681338094554617 48020834856511003570915963)
    ·
      refine ⟨72031252284766505356373945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48020834856511003570915963 72031252284766505356373945)
      ·
        refine ⟨54023439213574879017280459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72031252284766505356373945 54023439213574879017280459)
        ·
          refine ⟨81035158820362318525920689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54023439213574879017280459 81035158820362318525920689)
          ·
            refine ⟨60776369115271738894440517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81035158820362318525920689 60776369115271738894440517)
            ·
              refine ⟨11395569209113451042707597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60776369115271738894440517 11395569209113451042707597)
              ·
                refine ⟨4273338453417544141015349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11395569209113451042707597 4273338453417544141015349)
                ·
                  refine ⟨400625480007894763220189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4273338453417544141015349 400625480007894763220189)
                  ·
                    rfl

theorem cell23_7021938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_7021938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7021938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7021938 prefixEnd_7021938 := by exact prefixLift 7021938
  have htrace : WordTrace (prefixWord ++ tailWord_7021938) baseStart_7021938 baseEnd_7021938 := by
    simpa [prefixWord, tailWord_7021938, baseEnd_7021938] using wordTrace_append hprefix tailTrace_7021938
  have hstable : (prefixWord ++ tailWord_7021938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7021938).length < 2 ^ (prefixWord ++ tailWord_7021938).sum := by decide
  have hdescent : baseEnd_7021938 < baseStart_7021938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7021938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022028 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 6]
def baseStart_7022028 : Nat := 118140960795 + 7022028 * 2 ^ 59
def prefixEnd_7022028 : Nat := 4983230072969 + 3 ^ 40 * 7022028 * 2
def baseEnd_7022028 : Nat := 400630614814439724095143

theorem tailTrace_7022028 : CollatzResearch.WordTrace tailWord_7022028 prefixEnd_7022028 400630614814439724095143 := by
  unfold tailWord_7022028
  simp only [CollatzResearch.WordTrace]
  refine ⟨128057200902199648874497369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170742934536266198499329825 128057200902199648874497369)
  ·
    refine ⟨96042900676649736655873027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128057200902199648874497369 96042900676649736655873027)
    ·
      refine ⟨144064351014974604983809541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96042900676649736655873027 144064351014974604983809541)
      ·
        refine ⟨27012065815307738434464289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144064351014974604983809541 27012065815307738434464289)
        ·
          refine ⟨20259049361480803825848217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27012065815307738434464289 20259049361480803825848217)
          ·
            refine ⟨15194287021110602869386163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20259049361480803825848217 15194287021110602869386163)
            ·
              refine ⟨22791430531665904304079245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15194287021110602869386163 22791430531665904304079245)
              ·
                refine ⟨8546786449374714114029717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22791430531665904304079245 8546786449374714114029717)
                ·
                  refine ⟨400630614814439724095143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8546786449374714114029717 400630614814439724095143)
                  ·
                    rfl

theorem cell23_7022028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 6].length) (baseStart_7022028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022028 prefixEnd_7022028 := by exact prefixLift 7022028
  have htrace : WordTrace (prefixWord ++ tailWord_7022028) baseStart_7022028 baseEnd_7022028 := by
    simpa [prefixWord, tailWord_7022028, baseEnd_7022028] using wordTrace_append hprefix tailTrace_7022028
  have hstable : (prefixWord ++ tailWord_7022028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022028).length < 2 ^ (prefixWord ++ tailWord_7022028).sum := by decide
  have hdescent : baseEnd_7022028 < baseStart_7022028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022065 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 2, 3, 2]
def baseStart_7022065 : Nat := 118140960795 + 7022065 * 2 ^ 59
def prefixEnd_7022065 : Nat := 4983230072969 + 3 ^ 40 * 7022065 * 2
def baseEnd_7022065 : Nat := 3605694532114173872093617

theorem tailTrace_7022065 : CollatzResearch.WordTrace tailWord_7022065 prefixEnd_7022065 3605694532114173872093617 := by
  unfold tailWord_7022065
  simp only [CollatzResearch.WordTrace]
  refine ⟨256115751305265253068091649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170743834203510168712061099 256115751305265253068091649)
  ·
    refine ⟨192086813478948939801068737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256115751305265253068091649 192086813478948939801068737)
    ·
      refine ⟨144065110109211704850801553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192086813478948939801068737 144065110109211704850801553)
      ·
        refine ⟨108048832581908778638101165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144065110109211704850801553 108048832581908778638101165)
        ·
          refine ⟨40518312218215791989287937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108048832581908778638101165 40518312218215791989287937)
          ·
            refine ⟨30388734163661843991965953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40518312218215791989287937 30388734163661843991965953)
            ·
              refine ⟨22791550622746382993974465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30388734163661843991965953 22791550622746382993974465)
              ·
                refine ⟨17093662967059787245480849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22791550622746382993974465 17093662967059787245480849)
                ·
                  refine ⟨12820247225294840434110637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17093662967059787245480849 12820247225294840434110637)
                  ·
                    refine ⟨4807592709485565162791489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12820247225294840434110637 4807592709485565162791489)
                    ·
                      refine ⟨3605694532114173872093617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807592709485565162791489 3605694532114173872093617)
                      ·
                        rfl

theorem cell23_7022065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_7022065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022065 prefixEnd_7022065 := by exact prefixLift 7022065
  have htrace : WordTrace (prefixWord ++ tailWord_7022065) baseStart_7022065 baseEnd_7022065 := by
    simpa [prefixWord, tailWord_7022065, baseEnd_7022065] using wordTrace_append hprefix tailTrace_7022065
  have hstable : (prefixWord ++ tailWord_7022065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022065).length < 2 ^ (prefixWord ++ tailWord_7022065).sum := by decide
  have hdescent : baseEnd_7022065 < baseStart_7022065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022072 : List Nat := [2, 1, 2, 1, 1, 6, 1, 4, 1, 1, 3]
def baseStart_7022072 : Nat := 118140960795 + 7022072 * 2 ^ 59
def prefixEnd_7022072 : Nat := 4983230072969 + 3 ^ 40 * 7022072 * 2
def baseEnd_7022072 : Nat := 3605698126478755344706085

theorem tailTrace_7022072 : CollatzResearch.WordTrace tailWord_7022072 prefixEnd_7022072 3605698126478755344706085 := by
  unfold tailWord_7022072
  simp only [CollatzResearch.WordTrace]
  refine ⟨128058003308119946631798235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170744004410826595509064313 128058003308119946631798235)
  ·
    refine ⟨192087004962179919947697353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128058003308119946631798235 192087004962179919947697353)
    ·
      refine ⟨144065253721634939960773015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192087004962179919947697353 144065253721634939960773015)
      ·
        refine ⟨216097880582452409941159523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144065253721634939960773015 216097880582452409941159523)
        ·
          refine ⟨324146820873678614911739285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216097880582452409941159523 324146820873678614911739285)
          ·
            refine ⟨15194382228453685073987779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 324146820873678614911739285 15194382228453685073987779)
            ·
              refine ⟨22791573342680527610981669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15194382228453685073987779 22791573342680527610981669)
              ·
                refine ⟨4273420001752598927059063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22791573342680527610981669 4273420001752598927059063)
                ·
                  refine ⟨6410130002628898390588595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4273420001752598927059063 6410130002628898390588595)
                  ·
                    refine ⟨9615195003943347585882893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6410130002628898390588595 9615195003943347585882893)
                    ·
                      refine ⟨3605698126478755344706085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9615195003943347585882893 3605698126478755344706085)
                      ·
                        rfl

theorem cell23_7022072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 4, 1, 1, 3].length) (baseStart_7022072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022072 prefixEnd_7022072 := by exact prefixLift 7022072
  have htrace : WordTrace (prefixWord ++ tailWord_7022072) baseStart_7022072 baseEnd_7022072 := by
    simpa [prefixWord, tailWord_7022072, baseEnd_7022072] using wordTrace_append hprefix tailTrace_7022072
  have hstable : (prefixWord ++ tailWord_7022072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022072).length < 2 ^ (prefixWord ++ tailWord_7022072).sum := by decide
  have hdescent : baseEnd_7022072 < baseStart_7022072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022108 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_7022108 : Nat := 118140960795 + 7022108 * 2 ^ 59
def prefixEnd_7022108 : Nat := 4983230072969 + 3 ^ 40 * 7022108 * 2
def baseEnd_7022108 : Nat := 3605716611782317203855919

theorem tailTrace_7022108 : CollatzResearch.WordTrace tailWord_7022108 prefixEnd_7022108 3605716611782317203855919 := by
  unfold tailWord_7022108
  simp only [CollatzResearch.WordTrace]
  refine ⟨128058659822054735705953489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170744879762739647607937985 128058659822054735705953489)
  ·
    refine ⟨96043994866541051779465117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128058659822054735705953489 96043994866541051779465117)
    ·
      refine ⟨36016498074952894417299419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96043994866541051779465117 36016498074952894417299419)
      ·
        refine ⟨54024747112429341625949129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36016498074952894417299419 54024747112429341625949129)
        ·
          refine ⟨40518560334322006219461847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54024747112429341625949129 40518560334322006219461847)
          ·
            refine ⟨60777840501483009329192771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40518560334322006219461847 60777840501483009329192771)
            ·
              refine ⟨91166760752224513993789157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60777840501483009329192771 91166760752224513993789157)
              ·
                refine ⟨17093767641042096373835467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91166760752224513993789157 17093767641042096373835467)
                ·
                  refine ⟨25640651461563144560753201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17093767641042096373835467 25640651461563144560753201)
                  ·
                    refine ⟨19230488596172358420564901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25640651461563144560753201 19230488596172358420564901)
                    ·
                      refine ⟨3605716611782317203855919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19230488596172358420564901 3605716611782317203855919)
                      ·
                        rfl

theorem cell23_7022108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_7022108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022108 prefixEnd_7022108 := by exact prefixLift 7022108
  have htrace : WordTrace (prefixWord ++ tailWord_7022108) baseStart_7022108 baseEnd_7022108 := by
    simpa [prefixWord, tailWord_7022108, baseEnd_7022108] using wordTrace_append hprefix tailTrace_7022108
  have hstable : (prefixWord ++ tailWord_7022108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022108).length < 2 ^ (prefixWord ++ tailWord_7022108).sum := by decide
  have hdescent : baseEnd_7022108 < baseStart_7022108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022112 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 1, 1, 4]
def baseStart_7022112 : Nat := 118140960795 + 7022112 * 2 ^ 59
def prefixEnd_7022112 : Nat := 4983230072969 + 3 ^ 40 * 7022112 * 2
def baseEnd_7022112 : Nat := 3605718665704935188205901

theorem tailTrace_7022112 : CollatzResearch.WordTrace tailWord_7022112 prefixEnd_7022112 3605718665704935188205901 := by
  unfold tailWord_7022112
  simp only [CollatzResearch.WordTrace]
  refine ⟨128058732768047490047526295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170744977024063320063368393 128058732768047490047526295)
  ·
    refine ⟨192088099152071235071289443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128058732768047490047526295 192088099152071235071289443)
    ·
      refine ⟨288132148728106852606934165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192088099152071235071289443 288132148728106852606934165)
      ·
        refine ⟨13506194471630008715950039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 288132148728106852606934165 13506194471630008715950039)
        ·
          refine ⟨20259291707445013073925059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13506194471630008715950039 20259291707445013073925059)
          ·
            refine ⟨30388937561167519610887589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20259291707445013073925059 30388937561167519610887589)
            ·
              refine ⟨5697925792718909927041423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30388937561167519610887589 5697925792718909927041423)
              ·
                refine ⟨8546888689078364890562135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697925792718909927041423 8546888689078364890562135)
                ·
                  refine ⟨12820333033617547335843203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8546888689078364890562135 12820333033617547335843203)
                  ·
                    refine ⟨19230499550426321003764805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12820333033617547335843203 19230499550426321003764805)
                    ·
                      refine ⟨3605718665704935188205901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19230499550426321003764805 3605718665704935188205901)
                      ·
                        rfl

theorem cell23_7022112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_7022112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022112 prefixEnd_7022112 := by exact prefixLift 7022112
  have htrace : WordTrace (prefixWord ++ tailWord_7022112) baseStart_7022112 baseEnd_7022112 := by
    simpa [prefixWord, tailWord_7022112, baseEnd_7022112] using wordTrace_append hprefix tailTrace_7022112
  have hstable : (prefixWord ++ tailWord_7022112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022112).length < 2 ^ (prefixWord ++ tailWord_7022112).sum := by decide
  have hdescent : baseEnd_7022112 < baseStart_7022112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022188 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 3]
def baseStart_7022188 : Nat := 118140960795 + 7022188 * 2 ^ 59
def prefixEnd_7022188 : Nat := 4983230072969 + 3 ^ 40 * 7022188 * 2
def baseEnd_7022188 : Nat := 3605757690234676890855551

theorem tailTrace_7022188 : CollatzResearch.WordTrace tailWord_7022188 prefixEnd_7022188 3605757690234676890855551 := by
  unfold tailWord_7022188
  simp only [CollatzResearch.WordTrace]
  refine ⟨128060118741909822537409609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170746824989213096716546145 128060118741909822537409609)
  ·
    refine ⟨96045089056432366903057207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128060118741909822537409609 96045089056432366903057207)
    ·
      refine ⟨144067633584648550354585811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96045089056432366903057207 144067633584648550354585811)
      ·
        refine ⟨216101450376972825531878717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144067633584648550354585811 216101450376972825531878717)
        ·
          refine ⟨81038043891364809574454519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216101450376972825531878717 81038043891364809574454519)
          ·
            refine ⟨121557065837047214361681779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81038043891364809574454519 121557065837047214361681779)
            ·
              refine ⟨182335598755570821542522669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121557065837047214361681779 182335598755570821542522669)
              ·
                refine ⟨68375849533339058078446001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182335598755570821542522669 68375849533339058078446001)
                ·
                  refine ⟨51281887150004293558834501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68375849533339058078446001 51281887150004293558834501)
                  ·
                    refine ⟨9615353840625805042281469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51281887150004293558834501 9615353840625805042281469)
                    ·
                      refine ⟨3605757690234676890855551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9615353840625805042281469 3605757690234676890855551)
                      ·
                        rfl

theorem cell23_7022188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_7022188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022188 prefixEnd_7022188 := by exact prefixLift 7022188
  have htrace : WordTrace (prefixWord ++ tailWord_7022188) baseStart_7022188 baseEnd_7022188 := by
    simpa [prefixWord, tailWord_7022188, baseEnd_7022188] using wordTrace_append hprefix tailTrace_7022188
  have hstable : (prefixWord ++ tailWord_7022188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022188).length < 2 ^ (prefixWord ++ tailWord_7022188).sum := by decide
  have hdescent : baseEnd_7022188 < baseStart_7022188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022236 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_7022236 : Nat := 118140960795 + 7022236 * 2 ^ 59
def prefixEnd_7022236 : Nat := 4983230072969 + 3 ^ 40 * 7022236 * 2
def baseEnd_7022236 : Nat := 3605782337306092703055331

theorem tailTrace_7022236 : CollatzResearch.WordTrace tailWord_7022236 prefixEnd_7022236 3605782337306092703055331 := by
  unfold tailWord_7022236
  simp only [CollatzResearch.WordTrace]
  refine ⟨128060994093822874636283281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170747992125097166181711041 128060994093822874636283281)
  ·
    refine ⟨96045745570367155977212461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128060994093822874636283281 96045745570367155977212461)
    ·
      refine ⟨36017154588887683491454673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96045745570367155977212461 36017154588887683491454673)
      ·
        refine ⟨27012865941665762618591005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36017154588887683491454673 27012865941665762618591005)
        ·
          refine ⟨10129824728124660981971627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27012865941665762618591005 10129824728124660981971627)
          ·
            refine ⟨15194737092186991472957441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10129824728124660981971627 15194737092186991472957441)
            ·
              refine ⟨11396052819140243604718081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15194737092186991472957441 11396052819140243604718081)
              ·
                refine ⟨8547039614355182703538561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11396052819140243604718081 8547039614355182703538561)
                ·
                  refine ⟨6410279710766387027653921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8547039614355182703538561 6410279710766387027653921)
                  ·
                    refine ⟨4807709783074790270740441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6410279710766387027653921 4807709783074790270740441)
                    ·
                      refine ⟨3605782337306092703055331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807709783074790270740441 3605782337306092703055331)
                      ·
                        rfl

theorem cell23_7022236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_7022236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022236 prefixEnd_7022236 := by exact prefixLift 7022236
  have htrace : WordTrace (prefixWord ++ tailWord_7022236) baseStart_7022236 baseEnd_7022236 := by
    simpa [prefixWord, tailWord_7022236, baseEnd_7022236] using wordTrace_append hprefix tailTrace_7022236
  have hstable : (prefixWord ++ tailWord_7022236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022236).length < 2 ^ (prefixWord ++ tailWord_7022236).sum := by decide
  have hdescent : baseEnd_7022236 < baseStart_7022236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022245 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 2, 5, 2]
def baseStart_7022245 : Nat := 118140960795 + 7022245 * 2 ^ 59
def prefixEnd_7022245 : Nat := 4983230072969 + 3 ^ 40 * 7022245 * 2
def baseEnd_7022245 : Nat := 3605786958631983167842789

theorem tailTrace_7022245 : CollatzResearch.WordTrace tailWord_7022245 prefixEnd_7022245 3605786958631983167842789 := by
  unfold tailWord_7022245
  simp only [CollatzResearch.WordTrace]
  refine ⟨256122316444613143809644189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170748210963075429206429459 256122316444613143809644189)
  ·
    refine ⟨96045868666729928928616571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256122316444613143809644189 96045868666729928928616571)
    ·
      refine ⟨144068803000094893392924857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96045868666729928928616571 144068803000094893392924857)
      ·
        refine ⟨108051602250071170044693643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144068803000094893392924857 108051602250071170044693643)
        ·
          refine ⟨162077403375106755067040465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108051602250071170044693643 162077403375106755067040465)
          ·
            refine ⟨121558052531330066300280349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162077403375106755067040465 121558052531330066300280349)
            ·
              refine ⟨45584269699248774862605131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121558052531330066300280349 45584269699248774862605131)
              ·
                refine ⟨68376404548873162293907697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45584269699248774862605131 68376404548873162293907697)
                ·
                  refine ⟨51282303411654871720430773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68376404548873162293907697 51282303411654871720430773)
                  ·
                    refine ⟨4807715944842644223790385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51282303411654871720430773 4807715944842644223790385)
                    ·
                      refine ⟨3605786958631983167842789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807715944842644223790385 3605786958631983167842789)
                      ·
                        rfl

theorem cell23_7022245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_7022245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022245 prefixEnd_7022245 := by exact prefixLift 7022245
  have htrace : WordTrace (prefixWord ++ tailWord_7022245) baseStart_7022245 baseEnd_7022245 := by
    simpa [prefixWord, tailWord_7022245, baseEnd_7022245] using wordTrace_append hprefix tailTrace_7022245
  have hstable : (prefixWord ++ tailWord_7022245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022245).length < 2 ^ (prefixWord ++ tailWord_7022245).sum := by decide
  have hdescent : baseEnd_7022245 < baseStart_7022245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022295 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 3]
def baseStart_7022295 : Nat := 118140960795 + 7022295 * 2 ^ 59
def prefixEnd_7022295 : Nat := 4983230072969 + 3 ^ 40 * 7022295 * 2
def baseEnd_7022295 : Nat := 3605812632664707972217559

theorem tailTrace_7022295 : CollatzResearch.WordTrace tailWord_7022295 prefixEnd_7022295 3605812632664707972217559 := by
  unfold tailWord_7022295
  simp only [CollatzResearch.WordTrace]
  refine ⟨256124140094432002348964339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170749426729621334899309559 256124140094432002348964339)
  ·
    refine ⟨384186210141648003523446509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256124140094432002348964339 384186210141648003523446509)
    ·
      refine ⟨144069828803118001321292441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384186210141648003523446509 144069828803118001321292441)
      ·
        refine ⟨108052371602338500990969331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144069828803118001321292441 108052371602338500990969331)
        ·
          refine ⟨162078557403507751486453997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108052371602338500990969331 162078557403507751486453997)
          ·
            refine ⟨60779459026315406807420249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162078557403507751486453997 60779459026315406807420249)
            ·
              refine ⟨45584594269736555105565187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60779459026315406807420249 45584594269736555105565187)
              ·
                refine ⟨68376891404604832658347781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45584594269736555105565187 68376891404604832658347781)
                ·
                  refine ⟨12820667138363406123440209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68376891404604832658347781 12820667138363406123440209)
                  ·
                    refine ⟨9615500353772554592580157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12820667138363406123440209 9615500353772554592580157)
                    ·
                      refine ⟨3605812632664707972217559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9615500353772554592580157 3605812632664707972217559)
                      ·
                        rfl

theorem cell23_7022295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_7022295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022295 prefixEnd_7022295 := by exact prefixLift 7022295
  have htrace : WordTrace (prefixWord ++ tailWord_7022295) baseStart_7022295 baseEnd_7022295 := by
    simpa [prefixWord, tailWord_7022295, baseEnd_7022295] using wordTrace_append hprefix tailTrace_7022295
  have hstable : (prefixWord ++ tailWord_7022295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022295).length < 2 ^ (prefixWord ++ tailWord_7022295).sum := by decide
  have hdescent : baseEnd_7022295 < baseStart_7022295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022359 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 3, 1, 3]
def baseStart_7022359 : Nat := 118140960795 + 7022359 * 2 ^ 59
def prefixEnd_7022359 : Nat := 4983230072969 + 3 ^ 40 * 7022359 * 2
def baseEnd_7022359 : Nat := 3605845495426595721817265

theorem tailTrace_7022359 : CollatzResearch.WordTrace tailWord_7022359 prefixEnd_7022359 3605845495426595721817265 := by
  unfold tailWord_7022359
  simp only [CollatzResearch.WordTrace]
  refine ⟨256126474366200141279294131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170750982910800094186196087 256126474366200141279294131)
  ·
    refine ⟨384189711549300211918941197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256126474366200141279294131 384189711549300211918941197)
    ·
      refine ⟨144071141830987579469602949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384189711549300211918941197 144071141830987579469602949)
      ·
        refine ⟨27013339093310171150550553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144071141830987579469602949 27013339093310171150550553)
        ·
          refine ⟨20260004319982628362912915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27013339093310171150550553 20260004319982628362912915)
          ·
            refine ⟨30390006479973942544369373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20260004319982628362912915 30390006479973942544369373)
            ·
              refine ⟨11396252429990228454138515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30390006479973942544369373 11396252429990228454138515)
              ·
                refine ⟨17094378644985342681207773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11396252429990228454138515 17094378644985342681207773)
                ·
                  refine ⟨6410391991869503505452915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17094378644985342681207773 6410391991869503505452915)
                  ·
                    refine ⟨9615587987804255258179373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6410391991869503505452915 9615587987804255258179373)
                    ·
                      refine ⟨3605845495426595721817265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9615587987804255258179373 3605845495426595721817265)
                      ·
                        rfl

theorem cell23_7022359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_7022359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022359 prefixEnd_7022359 := by exact prefixLift 7022359
  have htrace : WordTrace (prefixWord ++ tailWord_7022359) baseStart_7022359 baseEnd_7022359 := by
    simpa [prefixWord, tailWord_7022359, baseEnd_7022359] using wordTrace_append hprefix tailTrace_7022359
  have hstable : (prefixWord ++ tailWord_7022359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022359).length < 2 ^ (prefixWord ++ tailWord_7022359).sum := by decide
  have hdescent : baseEnd_7022359 < baseStart_7022359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022366 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_7022366 : Nat := 118140960795 + 7022366 * 2 ^ 59
def prefixEnd_7022366 : Nat := 4983230072969 + 3 ^ 40 * 7022366 * 2
def baseEnd_7022366 : Nat := 400649898865686354936637

theorem tailTrace_7022366 : CollatzResearch.WordTrace tailWord_7022366 prefixEnd_7022366 400649898865686354936637 := by
  unfold tailWord_7022366
  simp only [CollatzResearch.WordTrace]
  refine ⟨32015841209646847684349869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170751153118116520983199301 32015841209646847684349869)
  ·
    refine ⟨12005940453617567881631201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32015841209646847684349869 12005940453617567881631201)
    ·
      refine ⟨9004455340213175911223401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12005940453617567881631201 9004455340213175911223401)
      ·
        refine ⟨6753341505159881933417551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9004455340213175911223401 6753341505159881933417551)
        ·
          refine ⟨10130012257739822900126327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6753341505159881933417551 10130012257739822900126327)
          ·
            refine ⟨15195018386609734350189491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10130012257739822900126327 15195018386609734350189491)
            ·
              refine ⟨22792527579914601525284237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15195018386609734350189491 22792527579914601525284237)
              ·
                refine ⟨8547197842467975571981589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22792527579914601525284237 8547197842467975571981589)
                ·
                  refine ⟨400649898865686354936637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8547197842467975571981589 400649898865686354936637)
                  ·
                    rfl

theorem cell23_7022366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_7022366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022366 prefixEnd_7022366 := by exact prefixLift 7022366
  have htrace : WordTrace (prefixWord ++ tailWord_7022366) baseStart_7022366 baseEnd_7022366 := by
    simpa [prefixWord, tailWord_7022366, baseEnd_7022366] using wordTrace_append hprefix tailTrace_7022366
  have hstable : (prefixWord ++ tailWord_7022366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022366).length < 2 ^ (prefixWord ++ tailWord_7022366).sum := by decide
  have hdescent : baseEnd_7022366 < baseStart_7022366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022432 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 3]
def baseStart_7022432 : Nat := 118140960795 + 7022432 * 2 ^ 59
def prefixEnd_7022432 : Nat := 4983230072969 + 3 ^ 40 * 7022432 * 2
def baseEnd_7022432 : Nat := 3605882979514373936204429

theorem tailTrace_7022432 : CollatzResearch.WordTrace tailWord_7022432 prefixEnd_7022432 3605882979514373936204429 := by
  unfold tailWord_7022432
  simp only [CollatzResearch.WordTrace]
  refine ⟨128064568447467837373350775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170752757929957116497801033 128064568447467837373350775)
  ·
    refine ⟨192096852671201756060026163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128064568447467837373350775 192096852671201756060026163)
    ·
      refine ⟨288145279006802634090039245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192096852671201756060026163 288145279006802634090039245)
      ·
        refine ⟨108054479627550987783764717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288145279006802634090039245 108054479627550987783764717)
        ·
          refine ⟨40520429860331620418911769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108054479627550987783764717 40520429860331620418911769)
          ·
            refine ⟨30390322395248715314183827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40520429860331620418911769 30390322395248715314183827)
            ·
              refine ⟨45585483592873072971275741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30390322395248715314183827 45585483592873072971275741)
              ·
                refine ⟨17094556347327402364228403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45585483592873072971275741 17094556347327402364228403)
                ·
                  refine ⟨25641834520991103546342605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17094556347327402364228403 25641834520991103546342605)
                  ·
                    refine ⟨9615687945371663829878477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25641834520991103546342605 9615687945371663829878477)
                    ·
                      refine ⟨3605882979514373936204429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9615687945371663829878477 3605882979514373936204429)
                      ·
                        rfl

theorem cell23_7022432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_7022432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022432 prefixEnd_7022432 := by exact prefixLift 7022432
  have htrace : WordTrace (prefixWord ++ tailWord_7022432) baseStart_7022432 baseEnd_7022432 := by
    simpa [prefixWord, tailWord_7022432, baseEnd_7022432] using wordTrace_append hprefix tailTrace_7022432
  have hstable : (prefixWord ++ tailWord_7022432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022432).length < 2 ^ (prefixWord ++ tailWord_7022432).sum := by decide
  have hdescent : baseEnd_7022432 < baseStart_7022432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022475 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 5]
def baseStart_7022475 : Nat := 118140960795 + 7022475 * 2 ^ 59
def prefixEnd_7022475 : Nat := 4983230072969 + 3 ^ 40 * 7022475 * 2
def baseEnd_7022475 : Nat := 3605905059182517267966731

theorem tailTrace_7022475 : CollatzResearch.WordTrace tailWord_7022475 prefixEnd_7022475 3605905059182517267966731 := by
  unfold tailWord_7022475
  simp only [CollatzResearch.WordTrace]
  refine ⟨256130705233779893090516879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170753803489186595393677919 256130705233779893090516879)
  ·
    refine ⟨384196057850669839635775319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256130705233779893090516879 384196057850669839635775319)
    ·
      refine ⟨576294086776004759453662979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384196057850669839635775319 576294086776004759453662979)
      ·
        refine ⟨864441130164007139180494469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576294086776004759453662979 864441130164007139180494469)
        ·
          refine ⟨162082711905751338596342713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 864441130164007139180494469 162082711905751338596342713)
          ·
            refine ⟨121562033929313503947257035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162082711905751338596342713 121562033929313503947257035)
            ·
              refine ⟨182343050893970255920885553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121562033929313503947257035 182343050893970255920885553)
              ·
                refine ⟨136757288170477691940664165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182343050893970255920885553 136757288170477691940664165)
                ·
                  refine ⟨25641991531964567238874531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136757288170477691940664165 25641991531964567238874531)
                  ·
                    refine ⟨38462987297946850858311797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25641991531964567238874531 38462987297946850858311797)
                    ·
                      refine ⟨3605905059182517267966731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38462987297946850858311797 3605905059182517267966731)
                      ·
                        rfl

theorem cell23_7022475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 5].length) (baseStart_7022475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022475 prefixEnd_7022475 := by exact prefixLift 7022475
  have htrace : WordTrace (prefixWord ++ tailWord_7022475) baseStart_7022475 baseEnd_7022475 := by
    simpa [prefixWord, tailWord_7022475, baseEnd_7022475] using wordTrace_append hprefix tailTrace_7022475
  have hstable : (prefixWord ++ tailWord_7022475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022475).length < 2 ^ (prefixWord ++ tailWord_7022475).sum := by decide
  have hdescent : baseEnd_7022475 < baseStart_7022475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022489 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 1, 4, 2]
def baseStart_7022489 : Nat := 118140960795 + 7022489 * 2 ^ 59
def prefixEnd_7022489 : Nat := 4983230072969 + 3 ^ 40 * 7022489 * 2
def baseEnd_7022489 : Nat := 3605912247911680213191667

theorem tailTrace_7022489 : CollatzResearch.WordTrace tailWord_7022489 prefixEnd_7022489 3605912247911680213191667 := by
  unfold tailWord_7022489
  simp only [CollatzResearch.WordTrace]
  refine ⟨256131215855729173481526521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170754143903819448987684347 256131215855729173481526521)
  ·
    refine ⟨192098411891796880111144891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256131215855729173481526521 192098411891796880111144891)
    ·
      refine ⟨288147617837695320166717337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192098411891796880111144891 288147617837695320166717337)
      ·
        refine ⟨216110713378271490125038003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288147617837695320166717337 216110713378271490125038003)
        ·
          refine ⟨324166070067407235187557005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216110713378271490125038003 324166070067407235187557005)
          ·
            refine ⟨121562276275277713195333877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324166070067407235187557005 121562276275277713195333877)
            ·
              refine ⟨11396463400807285612062551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121562276275277713195333877 11396463400807285612062551)
              ·
                refine ⟨17094695101210928418093827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11396463400807285612062551 17094695101210928418093827)
                ·
                  refine ⟨25642042651816392627140741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17094695101210928418093827 25642042651816392627140741)
                  ·
                    refine ⟨4807882997215573617588889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25642042651816392627140741 4807882997215573617588889)
                    ·
                      refine ⟨3605912247911680213191667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807882997215573617588889 3605912247911680213191667)
                      ·
                        rfl

theorem cell23_7022489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 4, 2].length) (baseStart_7022489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022489 prefixEnd_7022489 := by exact prefixLift 7022489
  have htrace : WordTrace (prefixWord ++ tailWord_7022489) baseStart_7022489 baseEnd_7022489 := by
    simpa [prefixWord, tailWord_7022489, baseEnd_7022489] using wordTrace_append hprefix tailTrace_7022489
  have hstable : (prefixWord ++ tailWord_7022489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022489).length < 2 ^ (prefixWord ++ tailWord_7022489).sum := by decide
  have hdescent : baseEnd_7022489 < baseStart_7022489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022522 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3]
def baseStart_7022522 : Nat := 118140960795 + 7022522 * 2 ^ 59
def prefixEnd_7022522 : Nat := 4983230072969 + 3 ^ 40 * 7022522 * 2
def baseEnd_7022522 : Nat := 3605929192773278584079015

theorem tailTrace_7022522 : CollatzResearch.WordTrace tailWord_7022522 prefixEnd_7022522 3605929192773278584079015 := by
  unfold tailWord_7022522
  simp only [CollatzResearch.WordTrace]
  refine ⟨64033104866152405029369455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170754946309739746744985213 64033104866152405029369455)
  ·
    refine ⟨96049657299228607544054183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64033104866152405029369455 96049657299228607544054183)
    ·
      refine ⟨144074485948842911316081275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96049657299228607544054183 144074485948842911316081275)
      ·
        refine ⟨216111728923264366974121913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144074485948842911316081275 216111728923264366974121913)
        ·
          refine ⟨162083796692448275230591435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216111728923264366974121913 162083796692448275230591435)
          ·
            refine ⟨243125695038672412845887153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162083796692448275230591435 243125695038672412845887153)
            ·
              refine ⟨182344271279004309634415365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243125695038672412845887153 182344271279004309634415365)
              ·
                refine ⟨34189550864813308056452881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182344271279004309634415365 34189550864813308056452881)
                ·
                  refine ⟨25642163148609981042339661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34189550864813308056452881 25642163148609981042339661)
                  ·
                    refine ⟨9615811180728742890877373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25642163148609981042339661 9615811180728742890877373)
                    ·
                      refine ⟨3605929192773278584079015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9615811180728742890877373 3605929192773278584079015)
                      ·
                        rfl

theorem cell23_7022522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3].length) (baseStart_7022522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022522 prefixEnd_7022522 := by exact prefixLift 7022522
  have htrace : WordTrace (prefixWord ++ tailWord_7022522) baseStart_7022522 baseEnd_7022522 := by
    simpa [prefixWord, tailWord_7022522, baseEnd_7022522] using wordTrace_append hprefix tailTrace_7022522
  have hstable : (prefixWord ++ tailWord_7022522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022522).length < 2 ^ (prefixWord ++ tailWord_7022522).sum := by decide
  have hdescent : baseEnd_7022522 < baseStart_7022522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022540 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 2, 2, 2]
def baseStart_7022540 : Nat := 118140960795 + 7022540 * 2 ^ 59
def prefixEnd_7022540 : Nat := 4983230072969 + 3 ^ 40 * 7022540 * 2
def baseEnd_7022540 : Nat := 3605938435425059513653933

theorem tailTrace_7022540 : CollatzResearch.WordTrace tailWord_7022540 prefixEnd_7022540 3605938435425059513653933 := by
  unfold tailWord_7022540
  simp only [CollatzResearch.WordTrace]
  refine ⟨128066537989272204595816537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170755383985696272794422049 128066537989272204595816537)
  ·
    refine ⟨96049903491954153446862403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128066537989272204595816537 96049903491954153446862403)
    ·
      refine ⟨144074855237931230170293605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96049903491954153446862403 144074855237931230170293605)
      ·
        refine ⟨27014035357112105656930051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144074855237931230170293605 27014035357112105656930051)
        ·
          refine ⟨40521053035668158485395077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27014035357112105656930051 40521053035668158485395077)
          ·
            refine ⟨7597697444187779716011577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40521053035668158485395077 7597697444187779716011577)
            ·
              refine ⟨5698273083140834787008683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7597697444187779716011577 5698273083140834787008683)
              ·
                refine ⟨8547409624711252180513025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698273083140834787008683 8547409624711252180513025)
                ·
                  refine ⟨6410557218533439135384769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8547409624711252180513025 6410557218533439135384769)
                  ·
                    refine ⟨4807917913900079351538577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6410557218533439135384769 4807917913900079351538577)
                    ·
                      refine ⟨3605938435425059513653933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4807917913900079351538577 3605938435425059513653933)
                      ·
                        rfl

theorem cell23_7022540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_7022540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022540 prefixEnd_7022540 := by exact prefixLift 7022540
  have htrace : WordTrace (prefixWord ++ tailWord_7022540) baseStart_7022540 baseEnd_7022540 := by
    simpa [prefixWord, tailWord_7022540, baseEnd_7022540] using wordTrace_append hprefix tailTrace_7022540
  have hstable : (prefixWord ++ tailWord_7022540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022540).length < 2 ^ (prefixWord ++ tailWord_7022540).sum := by decide
  have hdescent : baseEnd_7022540 < baseStart_7022540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022542 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_7022542 : Nat := 118140960795 + 7022542 * 2 ^ 59
def prefixEnd_7022542 : Nat := 4983230072969 + 3 ^ 40 * 7022542 * 2
def baseEnd_7022542 : Nat := 1201979820795456168609641

theorem tailTrace_7022542 : CollatzResearch.WordTrace tailWord_7022542 prefixEnd_7022542 1201979820795456168609641 := by
  unfold tailWord_7022542
  simp only [CollatzResearch.WordTrace]
  refine ⟨32016643615567145441650735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170755432616358109022137253 32016643615567145441650735)
  ·
    refine ⟨48024965423350718162476103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32016643615567145441650735 48024965423350718162476103)
    ·
      refine ⟨72037448135026077243714155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48024965423350718162476103 72037448135026077243714155)
      ·
        refine ⟨108056172202539115865571233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72037448135026077243714155 108056172202539115865571233)
        ·
          refine ⟨81042129151904336899178425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108056172202539115865571233 81042129151904336899178425)
          ·
            refine ⟨60781596863928252674383819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81042129151904336899178425 60781596863928252674383819)
            ·
              refine ⟨91172395295892379011575729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60781596863928252674383819 91172395295892379011575729)
              ·
                refine ⟨68379296471919284258681797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91172395295892379011575729 68379296471919284258681797)
                ·
                  refine ⟨12821118088484865798502837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68379296471919284258681797 12821118088484865798502837)
                  ·
                    refine ⟨1201979820795456168609641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12821118088484865798502837 1201979820795456168609641)
                    ·
                      rfl

theorem cell23_7022542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_7022542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022542 prefixEnd_7022542 := by exact prefixLift 7022542
  have htrace : WordTrace (prefixWord ++ tailWord_7022542) baseStart_7022542 baseEnd_7022542 := by
    simpa [prefixWord, tailWord_7022542, baseEnd_7022542] using wordTrace_append hprefix tailTrace_7022542
  have hstable : (prefixWord ++ tailWord_7022542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022542).length < 2 ^ (prefixWord ++ tailWord_7022542).sum := by decide
  have hdescent : baseEnd_7022542 < baseStart_7022542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022559 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 2, 5]
def baseStart_7022559 : Nat := 118140960795 + 7022559 * 2 ^ 59
def prefixEnd_7022559 : Nat := 4983230072969 + 3 ^ 40 * 7022559 * 2
def baseEnd_7022559 : Nat := 1201982730519164979772115

theorem tailTrace_7022559 : CollatzResearch.WordTrace tailWord_7022559 prefixEnd_7022559 1201982730519164979772115 := by
  unfold tailWord_7022559
  simp only [CollatzResearch.WordTrace]
  refine ⟨256133768965475575436574731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170755845976983716957716487 256133768965475575436574731)
  ·
    refine ⟨384200653448213363154862097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256133768965475575436574731 384200653448213363154862097)
    ·
      refine ⟨288150490086160022366146573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384200653448213363154862097 288150490086160022366146573)
      ·
        refine ⟨108056433782310008387304965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288150490086160022366146573 108056433782310008387304965)
        ·
          refine ⟨20260581334183126572619681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108056433782310008387304965 20260581334183126572619681)
          ·
            refine ⟨15195436000637344929464761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20260581334183126572619681 15195436000637344929464761)
            ·
              refine ⟨11396577000478008697098571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15195436000637344929464761 11396577000478008697098571)
              ·
                refine ⟨17094865500717013045647857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11396577000478008697098571 17094865500717013045647857)
                ·
                  refine ⟨12821149125537759784235893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17094865500717013045647857 12821149125537759784235893)
                  ·
                    refine ⟨1201982730519164979772115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12821149125537759784235893 1201982730519164979772115)
                    ·
                      rfl

theorem cell23_7022559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 5].length) (baseStart_7022559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022559 prefixEnd_7022559 := by exact prefixLift 7022559
  have htrace : WordTrace (prefixWord ++ tailWord_7022559) baseStart_7022559 baseEnd_7022559 := by
    simpa [prefixWord, tailWord_7022559, baseEnd_7022559] using wordTrace_append hprefix tailTrace_7022559
  have hstable : (prefixWord ++ tailWord_7022559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022559).length < 2 ^ (prefixWord ++ tailWord_7022559).sum := by decide
  have hdescent : baseEnd_7022559 < baseStart_7022559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022613 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 2, 1, 4]
def baseStart_7022613 : Nat := 118140960795 + 7022613 * 2 ^ 59
def prefixEnd_7022613 : Nat := 4983230072969 + 3 ^ 40 * 7022613 * 2
def baseEnd_7022613 : Nat := 3605975919512837728041097

theorem tailTrace_7022613 : CollatzResearch.WordTrace tailWord_7022613 prefixEnd_7022613 3605975919512837728041097 := by
  unfold tailWord_7022613
  simp only [CollatzResearch.WordTrace]
  refine ⟨256135738507279942659040493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170757159004853295106026995 256135738507279942659040493)
  ·
    refine ⟨96050901940229978497140185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256135738507279942659040493 96050901940229978497140185)
    ·
      refine ⟨72038176455172483872855139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96050901940229978497140185 72038176455172483872855139)
      ·
        refine ⟨108057264682758725809282709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72038176455172483872855139 108057264682758725809282709)
        ·
          refine ⟨5065184282004315272310127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108057264682758725809282709 5065184282004315272310127)
          ·
            refine ⟨7597776423006472908465191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5065184282004315272310127 7597776423006472908465191)
            ·
              refine ⟨11396664634509709362697787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7597776423006472908465191 11396664634509709362697787)
              ·
                refine ⟨17094996951764564044046681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11396664634509709362697787 17094996951764564044046681)
                ·
                  refine ⟨12821247713823423033035011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17094996951764564044046681 12821247713823423033035011)
                  ·
                    refine ⟨19231871570735134549552517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12821247713823423033035011 19231871570735134549552517)
                    ·
                      refine ⟨3605975919512837728041097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19231871570735134549552517 3605975919512837728041097)
                      ·
                        rfl

theorem cell23_7022613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_7022613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022613 prefixEnd_7022613 := by exact prefixLift 7022613
  have htrace : WordTrace (prefixWord ++ tailWord_7022613) baseStart_7022613 baseEnd_7022613 := by
    simpa [prefixWord, tailWord_7022613, baseEnd_7022613] using wordTrace_append hprefix tailTrace_7022613
  have hstable : (prefixWord ++ tailWord_7022613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022613).length < 2 ^ (prefixWord ++ tailWord_7022613).sum := by decide
  have hdescent : baseEnd_7022613 < baseStart_7022613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022679 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 4, 4]
def baseStart_7022679 : Nat := 118140960795 + 7022679 * 2 ^ 59
def prefixEnd_7022679 : Nat := 4983230072969 + 3 ^ 40 * 7022679 * 2
def baseEnd_7022679 : Nat := 1202003269745344823271931

theorem tailTrace_7022679 : CollatzResearch.WordTrace tailWord_7022679 prefixEnd_7022679 1202003269745344823271931 := by
  unfold tailWord_7022679
  simp only [CollatzResearch.WordTrace]
  refine ⟨256138145725040835930943091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170758763816693890620628727 256138145725040835930943091)
  ·
    refine ⟨384207218587561253896414637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256138145725040835930943091 384207218587561253896414637)
    ·
      refine ⟨144077706970335470211155489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384207218587561253896414637 144077706970335470211155489)
      ·
        refine ⟨108058280227751602658366617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144077706970335470211155489 108058280227751602658366617)
        ·
          refine ⟨81043710170813701993774963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108058280227751602658366617 81043710170813701993774963)
          ·
            refine ⟨121565565256220552990662445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81043710170813701993774963 121565565256220552990662445)
            ·
              refine ⟨45587086971082707371498417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121565565256220552990662445 45587086971082707371498417)
              ·
                refine ⟨34190315228312030528623813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45587086971082707371498417 34190315228312030528623813)
                ·
                  refine ⟨6410684105308505724116965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34190315228312030528623813 6410684105308505724116965)
                  ·
                    refine ⟨1202003269745344823271931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6410684105308505724116965 1202003269745344823271931)
                    ·
                      rfl

theorem cell23_7022679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_7022679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022679 prefixEnd_7022679 := by exact prefixLift 7022679
  have htrace : WordTrace (prefixWord ++ tailWord_7022679) baseStart_7022679 baseEnd_7022679 := by
    simpa [prefixWord, tailWord_7022679, baseEnd_7022679] using wordTrace_append hprefix tailTrace_7022679
  have hstable : (prefixWord ++ tailWord_7022679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022679).length < 2 ^ (prefixWord ++ tailWord_7022679).sum := by decide
  have hdescent : baseEnd_7022679 < baseStart_7022679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022680 : List Nat := [2, 1, 2, 2, 1, 6, 1, 3, 1, 1, 3]
def baseStart_7022680 : Nat := 118140960795 + 7022680 * 2 ^ 59
def prefixEnd_7022680 : Nat := 4983230072969 + 3 ^ 40 * 7022680 * 2
def baseEnd_7022680 : Nat := 3606010322716688965903289

theorem tailTrace_7022680 : CollatzResearch.WordTrace tailWord_7022680 prefixEnd_7022680 3606010322716688965903289 := by
  unfold tailWord_7022680
  simp only [CollatzResearch.WordTrace]
  refine ⟨128069091099018606550864747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170758788132024808734486329 128069091099018606550864747)
  ·
    refine ⟨192103636648527909826297121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128069091099018606550864747 192103636648527909826297121)
    ·
      refine ⟨144077727486395932369722841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192103636648527909826297121 144077727486395932369722841)
      ·
        refine ⟨108058295614796949277292131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144077727486395932369722841 108058295614796949277292131)
        ·
          refine ⟨162087443422195423915938197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108058295614796949277292131 162087443422195423915938197)
          ·
            refine ⟨7597848910415410496059603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162087443422195423915938197 7597848910415410496059603)
            ·
              refine ⟨11396773365623115744089405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7597848910415410496059603 11396773365623115744089405)
              ·
                refine ⟨4273790012108668404033527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11396773365623115744089405 4273790012108668404033527)
                ·
                  refine ⟨6410685018163002606050291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4273790012108668404033527 6410685018163002606050291)
                  ·
                    refine ⟨9616027527244503909075437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6410685018163002606050291 9616027527244503909075437)
                    ·
                      refine ⟨3606010322716688965903289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9616027527244503909075437 3606010322716688965903289)
                      ·
                        rfl

theorem cell23_7022680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_7022680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022680 prefixEnd_7022680 := by exact prefixLift 7022680
  have htrace : WordTrace (prefixWord ++ tailWord_7022680) baseStart_7022680 baseEnd_7022680 := by
    simpa [prefixWord, tailWord_7022680, baseEnd_7022680] using wordTrace_append hprefix tailTrace_7022680
  have hstable : (prefixWord ++ tailWord_7022680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022680).length < 2 ^ (prefixWord ++ tailWord_7022680).sum := by decide
  have hdescent : baseEnd_7022680 < baseStart_7022680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022689 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_7022689 : Nat := 118140960795 + 7022689 * 2 ^ 59
def prefixEnd_7022689 : Nat := 4983230072969 + 3 ^ 40 * 7022689 * 2
def baseEnd_7022689 : Nat := 3606014944042579430690747

theorem tailTrace_7022689 : CollatzResearch.WordTrace tailWord_7022689 prefixEnd_7022689 3606014944042579430690747 := by
  unfold tailWord_7022689
  simp only [CollatzResearch.WordTrace]
  refine ⟨256138510455004607638807121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170759006970003071759204747 256138510455004607638807121)
  ·
    refine ⟨192103882841253455729105341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256138510455004607638807121 192103882841253455729105341)
    ·
      refine ⟨72038956065470045898414503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192103882841253455729105341 72038956065470045898414503)
      ·
        refine ⟨108058434098205068847621755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72038956065470045898414503 108058434098205068847621755)
        ·
          refine ⟨162087651147307603271432633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108058434098205068847621755 162087651147307603271432633)
          ·
            refine ⟨121565738360480702453574475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162087651147307603271432633 121565738360480702453574475)
            ·
              refine ⟨182348607540721053680361713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121565738360480702453574475 182348607540721053680361713)
              ·
                refine ⟨136761455655540790260271285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182348607540721053680361713 136761455655540790260271285)
                ·
                  refine ⟨12821386467706949086900433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136761455655540790260271285 12821386467706949086900433)
                  ·
                    refine ⟨9616039850780211815175325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12821386467706949086900433 9616039850780211815175325)
                    ·
                      refine ⟨3606014944042579430690747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9616039850780211815175325 3606014944042579430690747)
                      ·
                        rfl

theorem cell23_7022689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_7022689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022689 prefixEnd_7022689 := by exact prefixLift 7022689
  have htrace : WordTrace (prefixWord ++ tailWord_7022689) baseStart_7022689 baseEnd_7022689 := by
    simpa [prefixWord, tailWord_7022689, baseEnd_7022689] using wordTrace_append hprefix tailTrace_7022689
  have hstable : (prefixWord ++ tailWord_7022689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022689).length < 2 ^ (prefixWord ++ tailWord_7022689).sum := by decide
  have hdescent : baseEnd_7022689 < baseStart_7022689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022690 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7022690 : Nat := 118140960795 + 7022690 * 2 ^ 59
def prefixEnd_7022690 : Nat := 4983230072969 + 3 ^ 40 * 7022690 * 2
def baseEnd_7022690 : Nat := 3606015457523233926778243

theorem tailTrace_7022690 : CollatzResearch.WordTrace tailWord_7022690 prefixEnd_7022690 3606015457523233926778243 := by
  unfold tailWord_7022690
  simp only [CollatzResearch.WordTrace]
  refine ⟨64034636732000246202398381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170759031285333989873062349 64034636732000246202398381)
  ·
    refine ⟨24012988774500092325899393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64034636732000246202398381 24012988774500092325899393)
    ·
      refine ⟨18009741580875069244424545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24012988774500092325899393 18009741580875069244424545)
      ·
        refine ⟨13507306185656301933318409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18009741580875069244424545 13507306185656301933318409)
        ·
          refine ⟨10130479639242226449988807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13507306185656301933318409 10130479639242226449988807)
          ·
            refine ⟨15195719458863339674983211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10130479639242226449988807 15195719458863339674983211)
            ·
              refine ⟨22793579188295009512474817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15195719458863339674983211 22793579188295009512474817)
              ·
                refine ⟨17095184391221257134356113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22793579188295009512474817 17095184391221257134356113)
                ·
                  refine ⟨12821388293415942850767085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17095184391221257134356113 12821388293415942850767085)
                  ·
                    refine ⟨4808020610030978569037657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12821388293415942850767085 4808020610030978569037657)
                    ·
                      refine ⟨3606015457523233926778243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808020610030978569037657 3606015457523233926778243)
                      ·
                        rfl

theorem cell23_7022690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7022690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022690 prefixEnd_7022690 := by exact prefixLift 7022690
  have htrace : WordTrace (prefixWord ++ tailWord_7022690) baseStart_7022690 baseEnd_7022690 := by
    simpa [prefixWord, tailWord_7022690, baseEnd_7022690] using wordTrace_append hprefix tailTrace_7022690
  have hstable : (prefixWord ++ tailWord_7022690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022690).length < 2 ^ (prefixWord ++ tailWord_7022690).sum := by decide
  have hdescent : baseEnd_7022690 < baseStart_7022690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022692 : List Nat := [2, 3, 1, 1, 2, 1, 13]
def baseStart_7022692 : Nat := 118140960795 + 7022692 * 2 ^ 59
def prefixEnd_7022692 : Nat := 4983230072969 + 3 ^ 40 * 7022692 * 2
def baseEnd_7022692 : Nat := 44518722030673369369793

theorem tailTrace_7022692 : CollatzResearch.WordTrace tailWord_7022692 prefixEnd_7022692 44518722030673369369793 := by
  unfold tailWord_7022692
  simp only [CollatzResearch.WordTrace]
  refine ⟨128069309936996869575583165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170759079915995826100777553 128069309936996869575583165)
  ·
    refine ⟨48025991226373826090843687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128069309936996869575583165 48025991226373826090843687)
    ·
      refine ⟨72038986839560739136265531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48025991226373826090843687 72038986839560739136265531)
      ·
        refine ⟨108058480259341108704398297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72038986839560739136265531 108058480259341108704398297)
        ·
          refine ⟨81043860194505831528298723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108058480259341108704398297 81043860194505831528298723)
          ·
            refine ⟨121565790291758747292448085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81043860194505831528298723 121565790291758747292448085)
            ·
              refine ⟨44518722030673369369793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 121565790291758747292448085 44518722030673369369793)
              ·
                rfl

theorem cell23_7022692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 13].length) (baseStart_7022692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022692 prefixEnd_7022692 := by exact prefixLift 7022692
  have htrace : WordTrace (prefixWord ++ tailWord_7022692) baseStart_7022692 baseEnd_7022692 := by
    simpa [prefixWord, tailWord_7022692, baseEnd_7022692] using wordTrace_append hprefix tailTrace_7022692
  have hstable : (prefixWord ++ tailWord_7022692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022692).length < 2 ^ (prefixWord ++ tailWord_7022692).sum := by decide
  have hdescent : baseEnd_7022692 < baseStart_7022692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022703 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 3, 2, 2]
def baseStart_7022703 : Nat := 118140960795 + 7022703 * 2 ^ 59
def prefixEnd_7022703 : Nat := 4983230072969 + 3 ^ 40 * 7022703 * 2
def baseEnd_7022703 : Nat := 3606022132771742375915683

theorem tailTrace_7022703 : CollatzResearch.WordTrace tailWord_7022703 prefixEnd_7022703 3606022132771742375915683 := by
  unfold tailWord_7022703
  simp only [CollatzResearch.WordTrace]
  refine ⟨256139021076953888029816763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170759347384635925353211175 256139021076953888029816763)
  ·
    refine ⟨384208531615430832044725145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256139021076953888029816763 384208531615430832044725145)
    ·
      refine ⟨288156398711573124033543859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384208531615430832044725145 288156398711573124033543859)
      ·
        refine ⟨432234598067359686050315789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288156398711573124033543859 432234598067359686050315789)
        ·
          refine ⟨162087974275259882268868421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432234598067359686050315789 162087974275259882268868421)
          ·
            refine ⟨30391495176611227925412829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162087974275259882268868421 30391495176611227925412829)
            ·
              refine ⟨11396810691229210472029811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30391495176611227925412829 11396810691229210472029811)
              ·
                refine ⟨17095216036843815708044717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11396810691229210472029811 17095216036843815708044717)
                ·
                  refine ⟨6410706013816430890516769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17095216036843815708044717 6410706013816430890516769)
                  ·
                    refine ⟨4808029510362323167887577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6410706013816430890516769 4808029510362323167887577)
                    ·
                      refine ⟨3606022132771742375915683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808029510362323167887577 3606022132771742375915683)
                      ·
                        rfl

theorem cell23_7022703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 2, 2].length) (baseStart_7022703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022703 prefixEnd_7022703 := by exact prefixLift 7022703
  have htrace : WordTrace (prefixWord ++ tailWord_7022703) baseStart_7022703 baseEnd_7022703 := by
    simpa [prefixWord, tailWord_7022703, baseEnd_7022703] using wordTrace_append hprefix tailTrace_7022703
  have hstable : (prefixWord ++ tailWord_7022703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022703).length < 2 ^ (prefixWord ++ tailWord_7022703).sum := by decide
  have hdescent : baseEnd_7022703 < baseStart_7022703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022712 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_7022712 : Nat := 118140960795 + 7022712 * 2 ^ 59
def prefixEnd_7022712 : Nat := 4983230072969 + 3 ^ 40 * 7022712 * 2
def baseEnd_7022712 : Nat := 3606026754097632840703141

theorem tailTrace_7022712 : CollatzResearch.WordTrace tailWord_7022712 prefixEnd_7022712 3606026754097632840703141 := by
  unfold tailWord_7022712
  simp only [CollatzResearch.WordTrace]
  refine ⟨128069674666960641283447195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170759566222614188377929593 128069674666960641283447195)
  ·
    refine ⟨192104512000440961925170793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128069674666960641283447195 192104512000440961925170793)
    ·
      refine ⟨144078384000330721443878095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192104512000440961925170793 144078384000330721443878095)
      ·
        refine ⟨216117576000496082165817143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144078384000330721443878095 216117576000496082165817143)
        ·
          refine ⟨324176364000744123248725715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216117576000496082165817143 324176364000744123248725715)
          ·
            refine ⟨486264546001116184873088573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324176364000744123248725715 486264546001116184873088573)
            ·
              refine ⟨182349204750418569327408215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 486264546001116184873088573 182349204750418569327408215)
              ·
                refine ⟨273523807125627853991112323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182349204750418569327408215 273523807125627853991112323)
                ·
                  refine ⟨410285710688441780986668485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273523807125627853991112323 410285710688441780986668485)
                  ·
                    refine ⟨76928570754082833935000341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 410285710688441780986668485 76928570754082833935000341)
                    ·
                      refine ⟨3606026754097632840703141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76928570754082833935000341 3606026754097632840703141)
                      ·
                        rfl

theorem cell23_7022712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_7022712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022712 prefixEnd_7022712 := by exact prefixLift 7022712
  have htrace : WordTrace (prefixWord ++ tailWord_7022712) baseStart_7022712 baseEnd_7022712 := by
    simpa [prefixWord, tailWord_7022712, baseEnd_7022712] using wordTrace_append hprefix tailTrace_7022712
  have hstable : (prefixWord ++ tailWord_7022712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022712).length < 2 ^ (prefixWord ++ tailWord_7022712).sum := by decide
  have hdescent : baseEnd_7022712 < baseStart_7022712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022713 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 2, 4]
def baseStart_7022713 : Nat := 118140960795 + 7022713 * 2 ^ 59
def prefixEnd_7022713 : Nat := 4983230072969 + 3 ^ 40 * 7022713 * 2
def baseEnd_7022713 : Nat := 1202009089192762445596879

theorem tailTrace_7022713 : CollatzResearch.WordTrace tailWord_7022713 prefixEnd_7022713 1202009089192762445596879 := by
  unfold tailWord_7022713
  simp only [CollatzResearch.WordTrace]
  refine ⟨256139385806917659737680793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170759590537945106491787195 256139385806917659737680793)
  ·
    refine ⟨192104539355188244803260595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256139385806917659737680793 192104539355188244803260595)
    ·
      refine ⟨288156809032782367204890893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192104539355188244803260595 288156809032782367204890893)
      ·
        refine ⟨108058803387293387701834085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288156809032782367204890893 108058803387293387701834085)
        ·
          refine ⟨20261025635117510194093891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108058803387293387701834085 20261025635117510194093891)
          ·
            refine ⟨30391538452676265291140837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20261025635117510194093891 30391538452676265291140837)
            ·
              refine ⟨5698413459876799742088907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30391538452676265291140837 5698413459876799742088907)
              ·
                refine ⟨8547620189815199613133361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698413459876799742088907 8547620189815199613133361)
                ·
                  refine ⟨6410715142361399709850021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8547620189815199613133361 6410715142361399709850021)
                  ·
                    refine ⟨1202009089192762445596879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6410715142361399709850021 1202009089192762445596879)
                    ·
                      rfl

theorem cell23_7022713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 2, 4].length) (baseStart_7022713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022713 prefixEnd_7022713 := by exact prefixLift 7022713
  have htrace : WordTrace (prefixWord ++ tailWord_7022713) baseStart_7022713 baseEnd_7022713 := by
    simpa [prefixWord, tailWord_7022713, baseEnd_7022713] using wordTrace_append hprefix tailTrace_7022713
  have hstable : (prefixWord ++ tailWord_7022713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022713).length < 2 ^ (prefixWord ++ tailWord_7022713).sum := by decide
  have hdescent : baseEnd_7022713 < baseStart_7022713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022723 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 1, 2, 3]
def baseStart_7022723 : Nat := 118140960795 + 7022723 * 2 ^ 59
def prefixEnd_7022723 : Nat := 4983230072969 + 3 ^ 40 * 7022723 * 2
def baseEnd_7022723 : Nat := 3606032402384832297665591

theorem tailTrace_7022723 : CollatzResearch.WordTrace tailWord_7022723 prefixEnd_7022723 3606032402384832297665591 := by
  unfold tailWord_7022723
  simp only [CollatzResearch.WordTrace]
  refine ⟨256139750536881431445544823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170759833691254287630363215 256139750536881431445544823)
  ·
    refine ⟨384209625805322147168317235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256139750536881431445544823 384209625805322147168317235)
    ·
      refine ⟨576314438707983220752475853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384209625805322147168317235 576314438707983220752475853)
      ·
        refine ⟨216117914515493707782178445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 576314438707983220752475853 216117914515493707782178445)
        ·
          refine ⟨81044217943310140418316917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216117914515493707782178445 81044217943310140418316917)
          ·
            refine ⟨7597895432185325664217211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81044217943310140418316917 7597895432185325664217211)
            ·
              refine ⟨11396843148277988496325817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7597895432185325664217211 11396843148277988496325817)
              ·
                refine ⟨8547632361208491372244363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11396843148277988496325817 8547632361208491372244363)
                ·
                  refine ⟨12821448541812737058366545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8547632361208491372244363 12821448541812737058366545)
                  ·
                    refine ⟨9616086406359552793774909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12821448541812737058366545 9616086406359552793774909)
                    ·
                      refine ⟨3606032402384832297665591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9616086406359552793774909 3606032402384832297665591)
                      ·
                        rfl

theorem cell23_7022723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_7022723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022723 prefixEnd_7022723 := by exact prefixLift 7022723
  have htrace : WordTrace (prefixWord ++ tailWord_7022723) baseStart_7022723 baseEnd_7022723 := by
    simpa [prefixWord, tailWord_7022723, baseEnd_7022723] using wordTrace_append hprefix tailTrace_7022723
  have hstable : (prefixWord ++ tailWord_7022723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022723).length < 2 ^ (prefixWord ++ tailWord_7022723).sum := by decide
  have hdescent : baseEnd_7022723 < baseStart_7022723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022740 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_7022740 : Nat := 118140960795 + 7022740 * 2 ^ 59
def prefixEnd_7022740 : Nat := 4983230072969 + 3 ^ 40 * 7022740 * 2
def baseEnd_7022740 : Nat := 3606041131555958731153013

theorem tailTrace_7022740 : CollatzResearch.WordTrace tailWord_7022740 prefixEnd_7022740 3606041131555958731153013 := by
  unfold tailWord_7022740
  simp only [CollatzResearch.WordTrace]
  refine ⟨128070185288909921674456837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170760247051879895565942449 128070185288909921674456837)
  ·
    refine ⟨24013159741670610313960657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128070185288909921674456837 24013159741670610313960657)
    ·
      refine ⟨18009869806252957735470493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24013159741670610313960657 18009869806252957735470493)
      ·
        refine ⟨6753701177344859150801435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18009869806252957735470493 6753701177344859150801435)
        ·
          refine ⟨10130551766017288726202153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6753701177344859150801435 10130551766017288726202153)
          ·
            refine ⟨7597913824512966544651615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10130551766017288726202153 7597913824512966544651615)
            ·
              refine ⟨11396870736769449816977423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7597913824512966544651615 11396870736769449816977423)
              ·
                refine ⟨17095306105154174725466135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11396870736769449816977423 17095306105154174725466135)
                ·
                  refine ⟨25642959157731262088199203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17095306105154174725466135 25642959157731262088199203)
                  ·
                    refine ⟨38464438736596893132298805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25642959157731262088199203 38464438736596893132298805)
                    ·
                      refine ⟨3606041131555958731153013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38464438736596893132298805 3606041131555958731153013)
                      ·
                        rfl

theorem cell23_7022740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_7022740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022740 prefixEnd_7022740 := by exact prefixLift 7022740
  have htrace : WordTrace (prefixWord ++ tailWord_7022740) baseStart_7022740 baseEnd_7022740 := by
    simpa [prefixWord, tailWord_7022740, baseEnd_7022740] using wordTrace_append hprefix tailTrace_7022740
  have hstable : (prefixWord ++ tailWord_7022740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022740).length < 2 ^ (prefixWord ++ tailWord_7022740).sum := by decide
  have hdescent : baseEnd_7022740 < baseStart_7022740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022753 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_7022753 : Nat := 118140960795 + 7022753 * 2 ^ 59
def prefixEnd_7022753 : Nat := 4983230072969 + 3 ^ 40 * 7022753 * 2
def baseEnd_7022753 : Nat := 3606047806804467180290453

theorem tailTrace_7022753 : CollatzResearch.WordTrace tailWord_7022753 prefixEnd_7022753 3606047806804467180290453 := by
  unfold tailWord_7022753
  simp only [CollatzResearch.WordTrace]
  refine ⟨256140844726772746569136913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170760563151181831046091275 256140844726772746569136913)
  ·
    refine ⟨192105633545079559926852685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256140844726772746569136913 192105633545079559926852685)
    ·
      refine ⟨72039612579404834972569757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192105633545079559926852685 72039612579404834972569757)
      ·
        refine ⟨27014854717276813114713659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72039612579404834972569757 27014854717276813114713659)
        ·
          refine ⟨40522282075915219672070489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27014854717276813114713659 40522282075915219672070489)
          ·
            refine ⟨30391711556936414754052867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40522282075915219672070489 30391711556936414754052867)
            ·
              refine ⟨45587567335404622131079301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30391711556936414754052867 45587567335404622131079301)
              ·
                refine ⟨8547668875388366649577369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45587567335404622131079301 8547668875388366649577369)
                ·
                  refine ⟨6410751656541274987183027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8547668875388366649577369 6410751656541274987183027)
                  ·
                    refine ⟨9616127484811912480774541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6410751656541274987183027 9616127484811912480774541)
                    ·
                      refine ⟨3606047806804467180290453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9616127484811912480774541 3606047806804467180290453)
                      ·
                        rfl

theorem cell23_7022753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_7022753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022753 prefixEnd_7022753 := by exact prefixLift 7022753
  have htrace : WordTrace (prefixWord ++ tailWord_7022753) baseStart_7022753 baseEnd_7022753 := by
    simpa [prefixWord, tailWord_7022753, baseEnd_7022753] using wordTrace_append hprefix tailTrace_7022753
  have hstable : (prefixWord ++ tailWord_7022753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022753).length < 2 ^ (prefixWord ++ tailWord_7022753).sum := by decide
  have hdescent : baseEnd_7022753 < baseStart_7022753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022754 : List Nat := [3, 3, 1, 3, 1, 1, 4, 2, 1, 2, 2]
def baseStart_7022754 : Nat := 118140960795 + 7022754 * 2 ^ 59
def prefixEnd_7022754 : Nat := 4983230072969 + 3 ^ 40 * 7022754 * 2
def baseEnd_7022754 : Nat := 3606048320285121676377949

theorem tailTrace_7022754 : CollatzResearch.WordTrace tailWord_7022754 prefixEnd_7022754 3606048320285121676377949 := by
  unfold tailWord_7022754
  simp only [CollatzResearch.WordTrace]
  refine ⟨64035220299942280934980829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170760587466512749159948877 64035220299942280934980829)
  ·
    refine ⟨24013207612478355350617811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64035220299942280934980829 24013207612478355350617811)
    ·
      refine ⟨36019811418717533025926717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24013207612478355350617811 36019811418717533025926717)
      ·
        refine ⟨13507429282019074884722519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36019811418717533025926717 13507429282019074884722519)
        ·
          refine ⟨20261143923028612327083779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13507429282019074884722519 20261143923028612327083779)
          ·
            refine ⟨30391715884542918490625669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20261143923028612327083779 30391715884542918490625669)
            ·
              refine ⟨5698446728351797216992313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30391715884542918490625669 5698446728351797216992313)
              ·
                refine ⟨4273835046263847912744235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5698446728351797216992313 4273835046263847912744235)
                ·
                  refine ⟨6410752569395771869116353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4273835046263847912744235 6410752569395771869116353)
                  ·
                    refine ⟨4808064427046828901837265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6410752569395771869116353 4808064427046828901837265)
                    ·
                      refine ⟨3606048320285121676377949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808064427046828901837265 3606048320285121676377949)
                      ·
                        rfl

theorem cell23_7022754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_7022754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022754 prefixEnd_7022754 := by exact prefixLift 7022754
  have htrace : WordTrace (prefixWord ++ tailWord_7022754) baseStart_7022754 baseEnd_7022754 := by
    simpa [prefixWord, tailWord_7022754, baseEnd_7022754] using wordTrace_append hprefix tailTrace_7022754
  have hstable : (prefixWord ++ tailWord_7022754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022754).length < 2 ^ (prefixWord ++ tailWord_7022754).sum := by decide
  have hdescent : baseEnd_7022754 < baseStart_7022754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022779 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 3]
def baseStart_7022779 : Nat := 118140960795 + 7022779 * 2 ^ 59
def prefixEnd_7022779 : Nat := 4983230072969 + 3 ^ 40 * 7022779 * 2
def baseEnd_7022779 : Nat := 3606061157301484078565333

theorem tailTrace_7022779 : CollatzResearch.WordTrace tailWord_7022779 prefixEnd_7022779 3606061157301484078565333 := by
  unfold tailWord_7022779
  simp only [CollatzResearch.WordTrace]
  refine ⟨256141793024678553009583391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170761195349785702006388927 256141793024678553009583391)
  ·
    refine ⟨384212689537017829514375087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256141793024678553009583391 384212689537017829514375087)
    ·
      refine ⟨576319034305526744271562631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384212689537017829514375087 576319034305526744271562631)
      ·
        refine ⟨864478551458290116407343947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576319034305526744271562631 864478551458290116407343947)
        ·
          refine ⟨1296717827187435174611015921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864478551458290116407343947 1296717827187435174611015921)
          ·
            refine ⟨972538370390576380958261941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1296717827187435174611015921 972538370390576380958261941)
            ·
              refine ⟨91175472224116535714837057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 972538370390576380958261941 91175472224116535714837057)
              ·
                refine ⟨68381604168087401786127793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91175472224116535714837057 68381604168087401786127793)
                ·
                  refine ⟨51286203126065551339595845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68381604168087401786127793 51286203126065551339595845)
                  ·
                    refine ⟨9616163086137290876174221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51286203126065551339595845 9616163086137290876174221)
                    ·
                      refine ⟨3606061157301484078565333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9616163086137290876174221 3606061157301484078565333)
                      ·
                        rfl

theorem cell23_7022779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 3].length) (baseStart_7022779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022779 prefixEnd_7022779 := by exact prefixLift 7022779
  have htrace : WordTrace (prefixWord ++ tailWord_7022779) baseStart_7022779 baseEnd_7022779 := by
    simpa [prefixWord, tailWord_7022779, baseEnd_7022779] using wordTrace_append hprefix tailTrace_7022779
  have hstable : (prefixWord ++ tailWord_7022779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022779).length < 2 ^ (prefixWord ++ tailWord_7022779).sum := by decide
  have hdescent : baseEnd_7022779 < baseStart_7022779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022810 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2]
def baseStart_7022810 : Nat := 118140960795 + 7022810 * 2 ^ 59
def prefixEnd_7022810 : Nat := 4983230072969 + 3 ^ 40 * 7022810 * 2
def baseEnd_7022810 : Nat := 3606077075201773457277691

theorem tailTrace_7022810 : CollatzResearch.WordTrace tailWord_7022810 prefixEnd_7022810 3606077075201773457277691 := by
  unfold tailWord_7022810
  simp only [CollatzResearch.WordTrace]
  refine ⟨64035730921891561325990471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170761949125044163535974589 64035730921891561325990471)
  ·
    refine ⟨96053596382837341988985707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64035730921891561325990471 96053596382837341988985707)
    ·
      refine ⟨144080394574256012983478561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96053596382837341988985707 144080394574256012983478561)
      ·
        refine ⟨108060295930692009737608921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144080394574256012983478561 108060295930692009737608921)
        ·
          refine ⟨81045221948019007303206691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108060295930692009737608921 81045221948019007303206691)
          ·
            refine ⟨121567832922028510954810037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81045221948019007303206691 121567832922028510954810037)
            ·
              refine ⟨11396984336440172902013441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121567832922028510954810037 11396984336440172902013441)
              ·
                refine ⟨8547738252330129676510081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11396984336440172902013441 8547738252330129676510081)
                ·
                  refine ⟨6410803689247597257382561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8547738252330129676510081 6410803689247597257382561)
                  ·
                    refine ⟨4808102766935697943036921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6410803689247597257382561 4808102766935697943036921)
                    ·
                      refine ⟨3606077075201773457277691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808102766935697943036921 3606077075201773457277691)
                      ·
                        rfl

theorem cell23_7022810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_7022810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022810 prefixEnd_7022810 := by exact prefixLift 7022810
  have htrace : WordTrace (prefixWord ++ tailWord_7022810) baseStart_7022810 baseEnd_7022810 := by
    simpa [prefixWord, tailWord_7022810, baseEnd_7022810] using wordTrace_append hprefix tailTrace_7022810
  have hstable : (prefixWord ++ tailWord_7022810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022810).length < 2 ^ (prefixWord ++ tailWord_7022810).sum := by decide
  have hdescent : baseEnd_7022810 < baseStart_7022810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022816 : List Nat := [2, 1, 1, 3, 1, 3, 1, 6, 5]
def baseStart_7022816 : Nat := 118140960795 + 7022816 * 2 ^ 59
def prefixEnd_7022816 : Nat := 4983230072969 + 3 ^ 40 * 7022816 * 2
def baseEnd_7022816 : Nat := 400675572898411159311407

theorem tailTrace_7022816 : CollatzResearch.WordTrace tailWord_7022816 prefixEnd_7022816 400675572898411159311407 := by
  unfold tailWord_7022816
  simp only [CollatzResearch.WordTrace]
  refine ⟨128071571262772254164340151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170762095017029672219120201 128071571262772254164340151)
  ·
    refine ⟨192107356894158381246510227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128071571262772254164340151 192107356894158381246510227)
    ·
      refine ⟨288161035341237571869765341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192107356894158381246510227 288161035341237571869765341)
      ·
        refine ⟨108060388252964089451162003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288161035341237571869765341 108060388252964089451162003)
        ·
          refine ⟨162090582379446134176743005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108060388252964089451162003 162090582379446134176743005)
          ·
            refine ⟨60783968392292300316278627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162090582379446134176743005 60783968392292300316278627)
            ·
              refine ⟨91175952588438450474417941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60783968392292300316278627 91175952588438450474417941)
              ·
                refine ⟨4273872777583052365988341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91175952588438450474417941 4273872777583052365988341)
                ·
                  refine ⟨400675572898411159311407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4273872777583052365988341 400675572898411159311407)
                  ·
                    rfl

theorem cell23_7022816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 5].length) (baseStart_7022816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022816 prefixEnd_7022816 := by exact prefixLift 7022816
  have htrace : WordTrace (prefixWord ++ tailWord_7022816) baseStart_7022816 baseEnd_7022816 := by
    simpa [prefixWord, tailWord_7022816, baseEnd_7022816] using wordTrace_append hprefix tailTrace_7022816
  have hstable : (prefixWord ++ tailWord_7022816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022816).length < 2 ^ (prefixWord ++ tailWord_7022816).sum := by decide
  have hdescent : baseEnd_7022816 < baseStart_7022816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022826 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_7022826 : Nat := 118140960795 + 7022826 * 2 ^ 59
def prefixEnd_7022826 : Nat := 4983230072969 + 3 ^ 40 * 7022826 * 2
def baseEnd_7022826 : Nat := 3606085290892245394677617

theorem tailTrace_7022826 : CollatzResearch.WordTrace tailWord_7022826 prefixEnd_7022826 3606085290892245394677617 := by
  unfold tailWord_7022826
  simp only [CollatzResearch.WordTrace]
  refine ⟨64035876813877070009136083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170762338170338853357696221 64035876813877070009136083)
  ·
    refine ⟨96053815220815605013704125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64035876813877070009136083 96053815220815605013704125)
    ·
      refine ⟨36020180707805851880139047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96053815220815605013704125 36020180707805851880139047)
      ·
        refine ⟨54030271061708777820208571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36020180707805851880139047 54030271061708777820208571)
        ·
          refine ⟨81045406592563166730312857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54030271061708777820208571 81045406592563166730312857)
          ·
            refine ⟨60784054944422375047734643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81045406592563166730312857 60784054944422375047734643)
            ·
              refine ⟨91176082416633562571601965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60784054944422375047734643 91176082416633562571601965)
              ·
                refine ⟨34191030906237585964350737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91176082416633562571601965 34191030906237585964350737)
                ·
                  refine ⟨25643273179678189473263053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34191030906237585964350737 25643273179678189473263053)
                  ·
                    refine ⟨9616227442379321052473645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25643273179678189473263053 9616227442379321052473645)
                    ·
                      refine ⟨3606085290892245394677617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9616227442379321052473645 3606085290892245394677617)
                      ·
                        rfl

theorem cell23_7022826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_7022826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022826 prefixEnd_7022826 := by exact prefixLift 7022826
  have htrace : WordTrace (prefixWord ++ tailWord_7022826) baseStart_7022826 baseEnd_7022826 := by
    simpa [prefixWord, tailWord_7022826, baseEnd_7022826] using wordTrace_append hprefix tailTrace_7022826
  have hstable : (prefixWord ++ tailWord_7022826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022826).length < 2 ^ (prefixWord ++ tailWord_7022826).sum := by decide
  have hdescent : baseEnd_7022826 < baseStart_7022826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022846 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_7022846 : Nat := 118140960795 + 7022846 * 2 ^ 59
def prefixEnd_7022846 : Nat := 4983230072969 + 3 ^ 40 * 7022846 * 2
def baseEnd_7022846 : Nat := 1202031853501778438809175

theorem tailTrace_7022846 : CollatzResearch.WordTrace tailWord_7022846 prefixEnd_7022846 1202031853501778438809175 := by
  unfold tailWord_7022846
  simp only [CollatzResearch.WordTrace]
  refine ⟨32018029589429477931534049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170762824476957215634848261 32018029589429477931534049)
  ·
    refine ⟨24013522192072108448650537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32018029589429477931534049 24013522192072108448650537)
    ·
      refine ⟨18010141644054081336487903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24013522192072108448650537 18010141644054081336487903)
      ·
        refine ⟨27015212466081122004731855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18010141644054081336487903 27015212466081122004731855)
        ·
          refine ⟨40522818699121683007097783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27015212466081122004731855 40522818699121683007097783)
          ·
            refine ⟨60784228048682524510646675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40522818699121683007097783 60784228048682524510646675)
            ·
              refine ⟨91176342073023786765970013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60784228048682524510646675 91176342073023786765970013)
              ·
                refine ⟨34191128277383920037238755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91176342073023786765970013 34191128277383920037238755)
                ·
                  refine ⟨51286692416075880055858133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34191128277383920037238755 51286692416075880055858133)
                  ·
                    refine ⟨1202031853501778438809175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51286692416075880055858133 1202031853501778438809175)
                    ·
                      rfl

theorem cell23_7022846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_7022846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022846 prefixEnd_7022846 := by exact prefixLift 7022846
  have htrace : WordTrace (prefixWord ++ tailWord_7022846) baseStart_7022846 baseEnd_7022846 := by
    simpa [prefixWord, tailWord_7022846, baseEnd_7022846] using wordTrace_append hprefix tailTrace_7022846
  have hstable : (prefixWord ++ tailWord_7022846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022846).length < 2 ^ (prefixWord ++ tailWord_7022846).sum := by decide
  have hdescent : baseEnd_7022846 < baseStart_7022846 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022850 : List Nat := [3, 4, 1, 1, 2, 1, 3, 3, 5]
def baseStart_7022850 : Nat := 118140960795 + 7022850 * 2 ^ 59
def prefixEnd_7022850 : Nat := 4983230072969 + 3 ^ 40 * 7022850 * 2
def baseEnd_7022850 : Nat := 400677512714217033419723

theorem tailTrace_7022850 : CollatzResearch.WordTrace tailWord_7022850 prefixEnd_7022850 400677512714217033419723 := by
  unfold tailWord_7022850
  simp only [CollatzResearch.WordTrace]
  refine ⟨64036095651855333033854501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170762921738280888090278669 64036095651855333033854501)
  ·
    refine ⟨12006767934722874943847719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64036095651855333033854501 12006767934722874943847719)
    ·
      refine ⟨18010151902084312415771579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12006767934722874943847719 18010151902084312415771579)
      ·
        refine ⟨27015227853126468623657369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18010151902084312415771579 27015227853126468623657369)
        ·
          refine ⟨20261420889844851467743027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27015227853126468623657369 20261420889844851467743027)
          ·
            refine ⟨30392131334767277201614541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20261420889844851467743027 30392131334767277201614541)
            ·
              refine ⟨11397049250537728950605453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30392131334767277201614541 11397049250537728950605453)
              ·
                refine ⟨4273893468951648356477045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11397049250537728950605453 4273893468951648356477045)
                ·
                  refine ⟨400677512714217033419723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4273893468951648356477045 400677512714217033419723)
                  ·
                    rfl

theorem cell23_7022850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_7022850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022850 prefixEnd_7022850 := by exact prefixLift 7022850
  have htrace : WordTrace (prefixWord ++ tailWord_7022850) baseStart_7022850 baseEnd_7022850 := by
    simpa [prefixWord, tailWord_7022850, baseEnd_7022850] using wordTrace_append hprefix tailTrace_7022850
  have hstable : (prefixWord ++ tailWord_7022850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022850).length < 2 ^ (prefixWord ++ tailWord_7022850).sum := by decide
  have hdescent : baseEnd_7022850 < baseStart_7022850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022900 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_7022900 : Nat := 118140960795 + 7022900 * 2 ^ 59
def prefixEnd_7022900 : Nat := 4983230072969 + 3 ^ 40 * 7022900 * 2
def baseEnd_7022900 : Nat := 3606123288460678105152277

theorem tailTrace_7022900 : CollatzResearch.WordTrace tailWord_7022900 prefixEnd_7022900 3606123288460678105152277 := by
  unfold tailWord_7022900
  simp only [CollatzResearch.WordTrace]
  refine ⟨128073103128620095337369077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170764137504826793783158769 128073103128620095337369077)
  ·
    refine ⟨12006853418308133937878351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128073103128620095337369077 12006853418308133937878351)
    ·
      refine ⟨18010280127462200906817527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12006853418308133937878351 18010280127462200906817527)
      ·
        refine ⟨27015420191193301360226291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18010280127462200906817527 27015420191193301360226291)
        ·
          refine ⟨40523130286789952040339437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27015420191193301360226291 40523130286789952040339437)
          ·
            refine ⟨15196173857546232015127289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40523130286789952040339437 15196173857546232015127289)
            ·
              refine ⟨11397130393159674011345467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15196173857546232015127289 11397130393159674011345467)
              ·
                refine ⟨17095695589739511017018201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11397130393159674011345467 17095695589739511017018201)
                ·
                  refine ⟨12821771692304633262763651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17095695589739511017018201 12821771692304633262763651)
                  ·
                    refine ⟨19232657538456949894145477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12821771692304633262763651 19232657538456949894145477)
                    ·
                      refine ⟨3606123288460678105152277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19232657538456949894145477 3606123288460678105152277)
                      ·
                        rfl

theorem cell23_7022900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_7022900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022900 prefixEnd_7022900 := by exact prefixLift 7022900
  have htrace : WordTrace (prefixWord ++ tailWord_7022900) baseStart_7022900 baseEnd_7022900 := by
    simpa [prefixWord, tailWord_7022900, baseEnd_7022900] using wordTrace_append hprefix tailTrace_7022900
  have hstable : (prefixWord ++ tailWord_7022900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022900).length < 2 ^ (prefixWord ++ tailWord_7022900).sum := by decide
  have hdescent : baseEnd_7022900 < baseStart_7022900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022943 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 4, 3, 2]
def baseStart_7022943 : Nat := 118140960795 + 7022943 * 2 ^ 59
def prefixEnd_7022943 : Nat := 4983230072969 + 3 ^ 40 * 7022943 * 2
def baseEnd_7022943 : Nat := 3606145368128821436914579

theorem tailTrace_7022943 : CollatzResearch.WordTrace tailWord_7022943 prefixEnd_7022943 3606145368128821436914579 := by
  unfold tailWord_7022943
  simp only [CollatzResearch.WordTrace]
  refine ⟨256147774596084409018553483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170765183064056272679035655 256147774596084409018553483)
  ·
    refine ⟨384221661894126613527830225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256147774596084409018553483 384221661894126613527830225)
    ·
      refine ⟨288166246420594960145872669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384221661894126613527830225 288166246420594960145872669)
      ·
        refine ⟨108062342407723110054702251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288166246420594960145872669 108062342407723110054702251)
        ·
          refine ⟨162093513611584665082053377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108062342407723110054702251 162093513611584665082053377)
          ·
            refine ⟨121570135208688498811540033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162093513611584665082053377 121570135208688498811540033)
            ·
              refine ⟨91177601406516374108655025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121570135208688498811540033 91177601406516374108655025)
              ·
                refine ⟨68383201054887280581491269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91177601406516374108655025 68383201054887280581491269)
                ·
                  refine ⟨12821850197791365109029613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68383201054887280581491269 12821850197791365109029613)
                  ·
                    refine ⟨4808193824171761915886105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12821850197791365109029613 4808193824171761915886105)
                    ·
                      refine ⟨3606145368128821436914579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808193824171761915886105 3606145368128821436914579)
                      ·
                        rfl

theorem cell23_7022943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_7022943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022943 prefixEnd_7022943 := by exact prefixLift 7022943
  have htrace : WordTrace (prefixWord ++ tailWord_7022943) baseStart_7022943 baseEnd_7022943 := by
    simpa [prefixWord, tailWord_7022943, baseEnd_7022943] using wordTrace_append hprefix tailTrace_7022943
  have hstable : (prefixWord ++ tailWord_7022943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022943).length < 2 ^ (prefixWord ++ tailWord_7022943).sum := by decide
  have hdescent : baseEnd_7022943 < baseStart_7022943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022960 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 2, 3, 2]
def baseStart_7022960 : Nat := 118140960795 + 7022960 * 2 ^ 59
def prefixEnd_7022960 : Nat := 4983230072969 + 3 ^ 40 * 7022960 * 2
def baseEnd_7022960 : Nat := 3606154097299947870402001

theorem tailTrace_7022960 : CollatzResearch.WordTrace tailWord_7022960 prefixEnd_7022960 3606154097299947870402001 := by
  unfold tailWord_7022960
  simp only [CollatzResearch.WordTrace]
  refine ⟨128074197318511410460961167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170765596424681880614614889 128074197318511410460961167)
  ·
    refine ⟨192111295977767115691441751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128074197318511410460961167 192111295977767115691441751)
    ·
      refine ⟨288166943966650673537162627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192111295977767115691441751 288166943966650673537162627)
      ·
        refine ⟨432250415949976010305743941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288166943966650673537162627 432250415949976010305743941)
        ·
          refine ⟨81046952990620501932326989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432250415949976010305743941 81046952990620501932326989)
          ·
            refine ⟨30392607371482688224622621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81046952990620501932326989 30392607371482688224622621)
            ·
              refine ⟨11397227764306008084233483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30392607371482688224622621 11397227764306008084233483)
              ·
                refine ⟨17095841646459012126350225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11397227764306008084233483 17095841646459012126350225)
                ·
                  refine ⟨12821881234844259094762669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17095841646459012126350225 12821881234844259094762669)
                  ·
                    refine ⟨4808205463066597160536001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12821881234844259094762669 4808205463066597160536001)
                    ·
                      refine ⟨3606154097299947870402001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808205463066597160536001 3606154097299947870402001)
                      ·
                        rfl

theorem cell23_7022960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 2, 3, 2].length) (baseStart_7022960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022960 prefixEnd_7022960 := by exact prefixLift 7022960
  have htrace : WordTrace (prefixWord ++ tailWord_7022960) baseStart_7022960 baseEnd_7022960 := by
    simpa [prefixWord, tailWord_7022960, baseEnd_7022960] using wordTrace_append hprefix tailTrace_7022960
  have hstable : (prefixWord ++ tailWord_7022960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022960).length < 2 ^ (prefixWord ++ tailWord_7022960).sum := by decide
  have hdescent : baseEnd_7022960 < baseStart_7022960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7022983 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 4, 4]
def baseStart_7022983 : Nat := 118140960795 + 7022983 * 2 ^ 59
def prefixEnd_7022983 : Nat := 4983230072969 + 3 ^ 40 * 7022983 * 2
def baseEnd_7022983 : Nat := 1202055302451667093471465

theorem tailTrace_7022983 : CollatzResearch.WordTrace tailWord_7022983 prefixEnd_7022983 1202055302451667093471465 := by
  unfold tailWord_7022983
  simp only [CollatzResearch.WordTrace]
  refine ⟨256149233515939495850009603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170766155677292997233339735 256149233515939495850009603)
  ·
    refine ⟨384223850273909243775014405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256149233515939495850009603 384223850273909243775014405)
    ·
      refine ⟨72041971926357983207815201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384223850273909243775014405 72041971926357983207815201)
      ·
        refine ⟨54031478944768487405861401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72041971926357983207815201 54031478944768487405861401)
        ·
          refine ⟨40523609208576365554396051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54031478944768487405861401 40523609208576365554396051)
          ·
            refine ⟨60785413812864548331594077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40523609208576365554396051 60785413812864548331594077)
            ·
              refine ⟨22794530179824205624347779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60785413812864548331594077 22794530179824205624347779)
              ·
                refine ⟨34191795269736308436521669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22794530179824205624347779 34191795269736308436521669)
                ·
                  refine ⟨6410961613075557831847813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34191795269736308436521669 6410961613075557831847813)
                  ·
                    refine ⟨1202055302451667093471465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6410961613075557831847813 1202055302451667093471465)
                    ·
                      rfl

theorem cell23_7022983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_7022983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7022983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7022983 prefixEnd_7022983 := by exact prefixLift 7022983
  have htrace : WordTrace (prefixWord ++ tailWord_7022983) baseStart_7022983 baseEnd_7022983 := by
    simpa [prefixWord, tailWord_7022983, baseEnd_7022983] using wordTrace_append hprefix tailTrace_7022983
  have hstable : (prefixWord ++ tailWord_7022983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7022983).length < 2 ^ (prefixWord ++ tailWord_7022983).sum := by decide
  have hdescent : baseEnd_7022983 < baseStart_7022983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7022983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023000 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 1, 6]
def baseStart_7023000 : Nat := 118140960795 + 7023000 * 2 ^ 59
def prefixEnd_7023000 : Nat := 4983230072969 + 3 ^ 40 * 7023000 * 2
def baseEnd_7023000 : Nat := 1202058212175375904633939

theorem tailTrace_7023000 : CollatzResearch.WordTrace tailWord_7023000 prefixEnd_7023000 1202058212175375904633939 := by
  unfold tailWord_7023000
  simp only [CollatzResearch.WordTrace]
  refine ⟨128074926778438953876689227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170766569037918605168918969 128074926778438953876689227)
  ·
    refine ⟨192112390167658430815033841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128074926778438953876689227 192112390167658430815033841)
    ·
      refine ⟨144084292625743823111275381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192112390167658430815033841 144084292625743823111275381)
      ·
        refine ⟨13507902433663483416682067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144084292625743823111275381 13507902433663483416682067)
        ·
          refine ⟨20261853650495225125023101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13507902433663483416682067 20261853650495225125023101)
          ·
            refine ⟨7598195118935709421883663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20261853650495225125023101 7598195118935709421883663)
            ·
              refine ⟨11397292678403564132825495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7598195118935709421883663 11397292678403564132825495)
              ·
                refine ⟨17095939017605346199238243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11397292678403564132825495 17095939017605346199238243)
                ·
                  refine ⟨25643908526408019298857365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17095939017605346199238243 25643908526408019298857365)
                  ·
                    refine ⟨1202058212175375904633939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25643908526408019298857365 1202058212175375904633939)
                    ·
                      rfl

theorem cell23_7023000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_7023000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023000 prefixEnd_7023000 := by exact prefixLift 7023000
  have htrace : WordTrace (prefixWord ++ tailWord_7023000) baseStart_7023000 baseEnd_7023000 := by
    simpa [prefixWord, tailWord_7023000, baseEnd_7023000] using wordTrace_append hprefix tailTrace_7023000
  have hstable : (prefixWord ++ tailWord_7023000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023000).length < 2 ^ (prefixWord ++ tailWord_7023000).sum := by decide
  have hdescent : baseEnd_7023000 < baseStart_7023000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023040 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 2, 1, 3]
def baseStart_7023040 : Nat := 118140960795 + 7023040 * 2 ^ 59
def prefixEnd_7023040 : Nat := 4983230072969 + 3 ^ 40 * 7023040 * 2
def baseEnd_7023040 : Nat := 3606195175752307557401633

theorem tailTrace_7023040 : CollatzResearch.WordTrace tailWord_7023040 prefixEnd_7023040 3606195175752307557401633 := by
  unfold tailWord_7023040
  simp only [CollatzResearch.WordTrace]
  refine ⟨128075656238366497292417287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170767541651155329723223049 128075656238366497292417287)
  ·
    refine ⟨192113484357549745938625931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128075656238366497292417287 192113484357549745938625931)
    ·
      refine ⟨288170226536324618907938897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192113484357549745938625931 288170226536324618907938897)
      ·
        refine ⟨216127669902243464180954173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288170226536324618907938897 216127669902243464180954173)
        ·
          refine ⟨81047876213341299067857815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216127669902243464180954173 81047876213341299067857815)
          ·
            refine ⟨121571814320011948601786723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81047876213341299067857815 121571814320011948601786723)
            ·
              refine ⟨182357721480017922902680085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121571814320011948601786723 182357721480017922902680085)
              ·
                refine ⟨8548018194375840136063129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182357721480017922902680085 8548018194375840136063129)
                ·
                  refine ⟨6411013645781880102047347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8548018194375840136063129 6411013645781880102047347)
                  ·
                    refine ⟨9616520468672820153071021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6411013645781880102047347 9616520468672820153071021)
                    ·
                      refine ⟨3606195175752307557401633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9616520468672820153071021 3606195175752307557401633)
                      ·
                        rfl

theorem cell23_7023040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 2, 1, 3].length) (baseStart_7023040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023040 prefixEnd_7023040 := by exact prefixLift 7023040
  have htrace : WordTrace (prefixWord ++ tailWord_7023040) baseStart_7023040 baseEnd_7023040 := by
    simpa [prefixWord, tailWord_7023040, baseEnd_7023040] using wordTrace_append hprefix tailTrace_7023040
  have hstable : (prefixWord ++ tailWord_7023040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023040).length < 2 ^ (prefixWord ++ tailWord_7023040).sum := by decide
  have hdescent : baseEnd_7023040 < baseStart_7023040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023050 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2]
def baseStart_7023050 : Nat := 118140960795 + 7023050 * 2 ^ 59
def prefixEnd_7023050 : Nat := 4983230072969 + 3 ^ 40 * 7023050 * 2
def baseEnd_7023050 : Nat := 3606200310558852518276587

theorem tailTrace_7023050 : CollatzResearch.WordTrace tailWord_7023050 prefixEnd_7023050 3606200310558852518276587 := by
  unfold tailWord_7023050
  simp only [CollatzResearch.WordTrace]
  refine ⟨64037919301674191573174651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170767784804464510861799069 64037919301674191573174651)
  ·
    refine ⟨96056878952511287359761977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64037919301674191573174651 96056878952511287359761977)
    ·
      refine ⟨72042659214383465519821483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96056878952511287359761977 72042659214383465519821483)
      ·
        refine ⟨108063988821575198279732225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72042659214383465519821483 108063988821575198279732225)
        ·
          refine ⟨81047991616181398709799169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108063988821575198279732225 81047991616181398709799169)
          ·
            refine ⟨60785993712136049032349377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81047991616181398709799169 60785993712136049032349377)
            ·
              refine ⟨45589495284102036774262033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60785993712136049032349377 45589495284102036774262033)
              ·
                refine ⟨34192121463076527580696525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45589495284102036774262033 34192121463076527580696525)
                ·
                  refine ⟨12822045548653697842761197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34192121463076527580696525 12822045548653697842761197)
                  ·
                    refine ⟨4808267080745136691035449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12822045548653697842761197 4808267080745136691035449)
                    ·
                      refine ⟨3606200310558852518276587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808267080745136691035449 3606200310558852518276587)
                      ·
                        rfl

theorem cell23_7023050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_7023050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023050 prefixEnd_7023050 := by exact prefixLift 7023050
  have htrace : WordTrace (prefixWord ++ tailWord_7023050) baseStart_7023050 baseEnd_7023050 := by
    simpa [prefixWord, tailWord_7023050, baseEnd_7023050] using wordTrace_append hprefix tailTrace_7023050
  have hstable : (prefixWord ++ tailWord_7023050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023050).length < 2 ^ (prefixWord ++ tailWord_7023050).sum := by decide
  have hdescent : baseEnd_7023050 < baseStart_7023050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023074 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7023074 : Nat := 118140960795 + 7023074 * 2 ^ 59
def prefixEnd_7023074 : Nat := 4983230072969 + 3 ^ 40 * 7023074 * 2
def baseEnd_7023074 : Nat := 3606212634094560424376477

theorem tailTrace_7023074 : CollatzResearch.WordTrace tailWord_7023074 prefixEnd_7023074 3606212634094560424376477 := by
  unfold tailWord_7023074
  simp only [CollatzResearch.WordTrace]
  refine ⟨64038138139652454597893069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170768368372406545594381517 64038138139652454597893069)
  ·
    refine ⟨24014301802369670474209901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64038138139652454597893069 24014301802369670474209901)
    ·
      refine ⟨9005363175888626427828713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24014301802369670474209901 9005363175888626427828713)
      ·
        refine ⟨6754022381916469820871535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9005363175888626427828713 6754022381916469820871535)
        ·
          refine ⟨10131033572874704731307303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754022381916469820871535 10131033572874704731307303)
          ·
            refine ⟨15196550359312057096960955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10131033572874704731307303 15196550359312057096960955)
            ·
              refine ⟨22794825538968085645441433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15196550359312057096960955 22794825538968085645441433)
              ·
                refine ⟨17096119154226064234081075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22794825538968085645441433 17096119154226064234081075)
                ·
                  refine ⟨25644178731339096351121613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17096119154226064234081075 25644178731339096351121613)
                  ·
                    refine ⟨9616567024252161131670605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25644178731339096351121613 9616567024252161131670605)
                    ·
                      refine ⟨3606212634094560424376477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9616567024252161131670605 3606212634094560424376477)
                      ·
                        rfl

theorem cell23_7023074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7023074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023074 prefixEnd_7023074 := by exact prefixLift 7023074
  have htrace : WordTrace (prefixWord ++ tailWord_7023074) baseStart_7023074 baseEnd_7023074 := by
    simpa [prefixWord, tailWord_7023074, baseEnd_7023074] using wordTrace_append hprefix tailTrace_7023074
  have hstable : (prefixWord ++ tailWord_7023074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023074).length < 2 ^ (prefixWord ++ tailWord_7023074).sum := by decide
  have hdescent : baseEnd_7023074 < baseStart_7023074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023080 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_7023080 : Nat := 118140960795 + 7023080 * 2 ^ 59
def prefixEnd_7023080 : Nat := 4983230072969 + 3 ^ 40 * 7023080 * 2
def baseEnd_7023080 : Nat := 3606215714978487400901449

theorem tailTrace_7023080 : CollatzResearch.WordTrace tailWord_7023080 prefixEnd_7023080 3606215714978487400901449 := by
  unfold tailWord_7023080
  simp only [CollatzResearch.WordTrace]
  refine ⟨128076385698294040708145347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170768514264392054277527129 128076385698294040708145347)
  ·
    refine ⟨192114578547441061062218021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128076385698294040708145347 192114578547441061062218021)
    ·
      refine ⟨36021483477645198949165879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192114578547441061062218021 36021483477645198949165879)
      ·
        refine ⟨54032225216467798423748819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36021483477645198949165879 54032225216467798423748819)
        ·
          refine ⟨81048337824701697635623229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54032225216467798423748819 81048337824701697635623229)
          ·
            refine ⟨30393126684263136613358711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81048337824701697635623229 30393126684263136613358711)
            ·
              refine ⟨45589690026394704920038067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30393126684263136613358711 45589690026394704920038067)
              ·
                refine ⟨68384535039592057380057101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45589690026394704920038067 68384535039592057380057101)
                ·
                  refine ⟨25644200639847021517521413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68384535039592057380057101 25644200639847021517521413)
                  ·
                    refine ⟨4808287619971316534535265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25644200639847021517521413 4808287619971316534535265)
                    ·
                      refine ⟨3606215714978487400901449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808287619971316534535265 3606215714978487400901449)
                      ·
                        rfl

theorem cell23_7023080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_7023080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023080 prefixEnd_7023080 := by exact prefixLift 7023080
  have htrace : WordTrace (prefixWord ++ tailWord_7023080) baseStart_7023080 baseEnd_7023080 := by
    simpa [prefixWord, tailWord_7023080, baseEnd_7023080] using wordTrace_append hprefix tailTrace_7023080
  have hstable : (prefixWord ++ tailWord_7023080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023080).length < 2 ^ (prefixWord ++ tailWord_7023080).sum := by decide
  have hdescent : baseEnd_7023080 < baseStart_7023080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023097 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 2, 2, 2]
def baseStart_7023097 : Nat := 118140960795 + 7023097 * 2 ^ 59
def prefixEnd_7023097 : Nat := 4983230072969 + 3 ^ 40 * 7023097 * 2
def baseEnd_7023097 : Nat := 3606224444149613834388871

theorem tailTrace_7023097 : CollatzResearch.WordTrace tailWord_7023097 prefixEnd_7023097 3606224444149613834388871 := by
  unfold tailWord_7023097
  simp only [CollatzResearch.WordTrace]
  refine ⟨256153391437526493319659545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170768927625017662213106363 256153391437526493319659545)
  ·
    refine ⟨192115043578144869989744659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256153391437526493319659545 192115043578144869989744659)
    ·
      refine ⟨288172565367217304984616989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192115043578144869989744659 288172565367217304984616989)
      ·
        refine ⟨108064712012706489369231371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288172565367217304984616989 108064712012706489369231371)
        ·
          refine ⟨162097068019059734053847057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108064712012706489369231371 162097068019059734053847057)
          ·
            refine ⟨121572801014294800540385293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162097068019059734053847057 121572801014294800540385293)
            ·
              refine ⟨45589800380360550202644485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121572801014294800540385293 45589800380360550202644485)
              ·
                refine ⟨8548087571317603162995841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45589800380360550202644485 8548087571317603162995841)
                ·
                  refine ⟨6411065678488202372246881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8548087571317603162995841 6411065678488202372246881)
                  ·
                    refine ⟨4808299258866151779185161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6411065678488202372246881 4808299258866151779185161)
                    ·
                      refine ⟨3606224444149613834388871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808299258866151779185161 3606224444149613834388871)
                      ·
                        rfl

theorem cell23_7023097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 2, 2].length) (baseStart_7023097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023097 prefixEnd_7023097 := by exact prefixLift 7023097
  have htrace : WordTrace (prefixWord ++ tailWord_7023097) baseStart_7023097 baseEnd_7023097 := by
    simpa [prefixWord, tailWord_7023097, baseEnd_7023097] using wordTrace_append hprefix tailTrace_7023097
  have hstable : (prefixWord ++ tailWord_7023097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023097).length < 2 ^ (prefixWord ++ tailWord_7023097).sum := by decide
  have hdescent : baseEnd_7023097 < baseStart_7023097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023180 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 3, 4]
def baseStart_7023180 : Nat := 118140960795 + 7023180 * 2 ^ 59
def prefixEnd_7023180 : Nat := 4983230072969 + 3 ^ 40 * 7023180 * 2
def baseEnd_7023180 : Nat := 1202089021014645669883663

theorem tailTrace_7023180 : CollatzResearch.WordTrace tailWord_7023180 prefixEnd_7023180 1202089021014645669883663 := by
  unfold tailWord_7023180
  simp only [CollatzResearch.WordTrace]
  refine ⟨128078209348112899247465497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170770945797483865663287329 128078209348112899247465497)
  ·
    refine ⟨96058657011084674435599123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128078209348112899247465497 96058657011084674435599123)
    ·
      refine ⟨144087985516627011653398685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96058657011084674435599123 144087985516627011653398685)
      ·
        refine ⟨54032994568735129370024507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144087985516627011653398685 54032994568735129370024507)
        ·
          refine ⟨81049491853102694055036761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54032994568735129370024507 81049491853102694055036761)
          ·
            refine ⟨60787118889827020541277571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81049491853102694055036761 60787118889827020541277571)
            ·
              refine ⟨91180678334740530811916357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60787118889827020541277571 91180678334740530811916357)
              ·
                refine ⟨17096377187763849527234317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91180678334740530811916357 17096377187763849527234317)
                ·
                  refine ⟨6411141445411443572712869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17096377187763849527234317 6411141445411443572712869)
                  ·
                    refine ⟨1202089021014645669883663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6411141445411443572712869 1202089021014645669883663)
                    ·
                      rfl

theorem cell23_7023180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_7023180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023180 prefixEnd_7023180 := by exact prefixLift 7023180
  have htrace : WordTrace (prefixWord ++ tailWord_7023180) baseStart_7023180 baseEnd_7023180 := by
    simpa [prefixWord, tailWord_7023180, baseEnd_7023180] using wordTrace_append hprefix tailTrace_7023180
  have hstable : (prefixWord ++ tailWord_7023180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023180).length < 2 ^ (prefixWord ++ tailWord_7023180).sum := by decide
  have hdescent : baseEnd_7023180 < baseStart_7023180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023210 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 6]
def baseStart_7023210 : Nat := 118140960795 + 7023210 * 2 ^ 59
def prefixEnd_7023210 : Nat := 4983230072969 + 3 ^ 40 * 7023210 * 2
def baseEnd_7023210 : Nat := 400698051940396876919539

theorem tailTrace_7023210 : CollatzResearch.WordTrace tailWord_7023210 prefixEnd_7023210 400698051940396876919539 := by
  unfold tailWord_7023210
  simp only [CollatzResearch.WordTrace]
  refine ⟨64039378221529278404630771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170771675257411409079015389 64039378221529278404630771)
  ·
    refine ⟨96059067332293917606946157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64039378221529278404630771 96059067332293917606946157)
    ·
      refine ⟨36022150249610219102604809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96059067332293917606946157 36022150249610219102604809)
      ·
        refine ⟨27016612687207664326953607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36022150249610219102604809 27016612687207664326953607)
        ·
          refine ⟨40524919030811496490430411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27016612687207664326953607 40524919030811496490430411)
          ·
            refine ⟨60787378546217244735645617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40524919030811496490430411 60787378546217244735645617)
            ·
              refine ⟨45590533909662933551734213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60787378546217244735645617 45590533909662933551734213)
              ·
                refine ⟨8548225108061800040950165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45590533909662933551734213 8548225108061800040950165)
                ·
                  refine ⟨400698051940396876919539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8548225108061800040950165 400698051940396876919539)
                  ·
                    rfl

theorem cell23_7023210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_7023210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023210 prefixEnd_7023210 := by exact prefixLift 7023210
  have htrace : WordTrace (prefixWord ++ tailWord_7023210) baseStart_7023210 baseEnd_7023210 := by
    simpa [prefixWord, tailWord_7023210, baseEnd_7023210] using wordTrace_append hprefix tailTrace_7023210
  have hstable : (prefixWord ++ tailWord_7023210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023210).length < 2 ^ (prefixWord ++ tailWord_7023210).sum := by decide
  have hdescent : baseEnd_7023210 < baseStart_7023210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023214 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_7023214 : Nat := 118140960795 + 7023214 * 2 ^ 59
def prefixEnd_7023214 : Nat := 4983230072969 + 3 ^ 40 * 7023214 * 2
def baseEnd_7023214 : Nat := 1202094840462063292208611

theorem tailTrace_7023214 : CollatzResearch.WordTrace tailWord_7023214 prefixEnd_7023214 1202094840462063292208611 := by
  unfold tailWord_7023214
  simp only [CollatzResearch.WordTrace]
  refine ⟨32019707347262827787708587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170771772518735081534445797 32019707347262827787708587)
  ·
    refine ⟨48029561020894241681562881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32019707347262827787708587 48029561020894241681562881)
    ·
      refine ⟨36022170765670681261172161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48029561020894241681562881 36022170765670681261172161)
      ·
        refine ⟨27016628074253010945879121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36022170765670681261172161 27016628074253010945879121)
        ·
          refine ⟨20262471055689758209409341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27016628074253010945879121 20262471055689758209409341)
          ·
            refine ⟨7598426645883659328528503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20262471055689758209409341 7598426645883659328528503)
            ·
              refine ⟨11397639968825488992792755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7598426645883659328528503 11397639968825488992792755)
              ·
                refine ⟨17096459953238233489189133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11397639968825488992792755 17096459953238233489189133)
                ·
                  refine ⟨6411172482464337558445925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17096459953238233489189133 6411172482464337558445925)
                  ·
                    refine ⟨1202094840462063292208611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6411172482464337558445925 1202094840462063292208611)
                    ·
                      rfl

theorem cell23_7023214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_7023214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023214 prefixEnd_7023214 := by exact prefixLift 7023214
  have htrace : WordTrace (prefixWord ++ tailWord_7023214) baseStart_7023214 baseEnd_7023214 := by
    simpa [prefixWord, tailWord_7023214, baseEnd_7023214] using wordTrace_append hprefix tailTrace_7023214
  have hstable : (prefixWord ++ tailWord_7023214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023214).length < 2 ^ (prefixWord ++ tailWord_7023214).sum := by decide
  have hdescent : baseEnd_7023214 < baseStart_7023214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023257 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 1, 5]
def baseStart_7023257 : Nat := 118140960795 + 7023257 * 2 ^ 59
def prefixEnd_7023257 : Nat := 4983230072969 + 3 ^ 40 * 7023257 * 2
def baseEnd_7023257 : Nat := 1202102200351444402796045

theorem tailTrace_7023257 : CollatzResearch.WordTrace tailWord_7023257 prefixEnd_7023257 1202102200351444402796045 := by
  unfold tailWord_7023257
  simp only [CollatzResearch.WordTrace]
  refine ⟨256159227116946840645484025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170772818077964560430322683 256159227116946840645484025)
  ·
    refine ⟨192119420337710130484113019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256159227116946840645484025 192119420337710130484113019)
    ·
      refine ⟨288179130506565195726169529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192119420337710130484113019 288179130506565195726169529)
      ·
        refine ⟨216134347879923896794627147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288179130506565195726169529 216134347879923896794627147)
        ·
          refine ⟨324201521819885845191940721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216134347879923896794627147 324201521819885845191940721)
          ·
            refine ⟨243151141364914383893955541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324201521819885845191940721 243151141364914383893955541)
            ·
              refine ⟨5698854875740180872514583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 243151141364914383893955541 5698854875740180872514583)
              ·
                refine ⟨8548282313610271308771875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5698854875740180872514583 8548282313610271308771875)
                ·
                  refine ⟨12822423470415406963157813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8548282313610271308771875 12822423470415406963157813)
                  ·
                    refine ⟨1202102200351444402796045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12822423470415406963157813 1202102200351444402796045)
                    ·
                      rfl

theorem cell23_7023257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 5].length) (baseStart_7023257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023257 prefixEnd_7023257 := by exact prefixLift 7023257
  have htrace : WordTrace (prefixWord ++ tailWord_7023257) baseStart_7023257 baseEnd_7023257 := by
    simpa [prefixWord, tailWord_7023257, baseEnd_7023257] using wordTrace_append hprefix tailTrace_7023257
  have hstable : (prefixWord ++ tailWord_7023257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023257).length < 2 ^ (prefixWord ++ tailWord_7023257).sum := by decide
  have hdescent : baseEnd_7023257 < baseStart_7023257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023277 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_7023277 : Nat := 118140960795 + 7023277 * 2 ^ 59
def prefixEnd_7023277 : Nat := 4983230072969 + 3 ^ 40 * 7023277 * 2
def baseEnd_7023277 : Nat := 3606316870667423130138043

theorem tailTrace_7023277 : CollatzResearch.WordTrace tailWord_7023277 prefixEnd_7023277 3606316870667423130138043 := by
  unfold tailWord_7023277
  simp only [CollatzResearch.WordTrace]
  refine ⟨256159956576874384061212085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170773304384582922707474723 256159956576874384061212085)
  ·
    refine ⟨24014995929081973505738633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256159956576874384061212085 24014995929081973505738633)
    ·
      refine ⟨18011246946811480129303975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24014995929081973505738633 18011246946811480129303975)
      ·
        refine ⟨27016870420217220193955963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18011246946811480129303975 27016870420217220193955963)
        ·
          refine ⟨40525305630325830290933945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27016870420217220193955963 40525305630325830290933945)
          ·
            refine ⟨30393979222744372718200459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40525305630325830290933945 30393979222744372718200459)
            ·
              refine ⟨45590968834116559077300689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30393979222744372718200459 45590968834116559077300689)
              ·
                refine ⟨34193226625587419307975517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45590968834116559077300689 34193226625587419307975517)
                ·
                  refine ⟨12822459984595282240490819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34193226625587419307975517 12822459984595282240490819)
                  ·
                    refine ⟨19233689976892923360736229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12822459984595282240490819 19233689976892923360736229)
                    ·
                      refine ⟨3606316870667423130138043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19233689976892923360736229 3606316870667423130138043)
                      ·
                        rfl

theorem cell23_7023277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_7023277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023277 prefixEnd_7023277 := by exact prefixLift 7023277
  have htrace : WordTrace (prefixWord ++ tailWord_7023277) baseStart_7023277 baseEnd_7023277 := by
    simpa [prefixWord, tailWord_7023277, baseEnd_7023277] using wordTrace_append hprefix tailTrace_7023277
  have hstable : (prefixWord ++ tailWord_7023277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023277).length < 2 ^ (prefixWord ++ tailWord_7023277).sum := by decide
  have hdescent : baseEnd_7023277 < baseStart_7023277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023287 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 1, 6]
def baseStart_7023287 : Nat := 118140960795 + 7023287 * 2 ^ 59
def prefixEnd_7023287 : Nat := 4983230072969 + 3 ^ 40 * 7023287 * 2
def baseEnd_7023287 : Nat := 1202107335157989363670999

theorem tailTrace_7023287 : CollatzResearch.WordTrace tailWord_7023287 prefixEnd_7023287 1202107335157989363670999 := by
  unfold tailWord_7023287
  simp only [CollatzResearch.WordTrace]
  refine ⟨256160321306838155769076115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170773547537892103846050743 256160321306838155769076115)
  ·
    refine ⟨384240481960257233653614173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256160321306838155769076115 384240481960257233653614173)
    ·
      refine ⟨144090180735096462620105315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384240481960257233653614173 144090180735096462620105315)
      ·
        refine ⟨216135271102644693930157973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144090180735096462620105315 216135271102644693930157973)
        ·
          refine ⟨10131340832936470027976155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 216135271102644693930157973 10131340832936470027976155)
          ·
            refine ⟨15197011249404705041964233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10131340832936470027976155 15197011249404705041964233)
            ·
              refine ⟨11397758437053528781473175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15197011249404705041964233 11397758437053528781473175)
              ·
                refine ⟨17096637655580293172209763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11397758437053528781473175 17096637655580293172209763)
                ·
                  refine ⟨25644956483370439758314645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17096637655580293172209763 25644956483370439758314645)
                  ·
                    refine ⟨1202107335157989363670999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25644956483370439758314645 1202107335157989363670999)
                    ·
                      rfl

theorem cell23_7023287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_7023287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023287 prefixEnd_7023287 := by exact prefixLift 7023287
  have htrace : WordTrace (prefixWord ++ tailWord_7023287) baseStart_7023287 baseEnd_7023287 := by
    simpa [prefixWord, tailWord_7023287, baseEnd_7023287] using wordTrace_append hprefix tailTrace_7023287
  have hstable : (prefixWord ++ tailWord_7023287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023287).length < 2 ^ (prefixWord ++ tailWord_7023287).sum := by decide
  have hdescent : baseEnd_7023287 < baseStart_7023287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023317 : List Nat := [1, 3, 2, 5, 1, 1, 10]
def baseStart_7023317 : Nat := 118140960795 + 7023317 * 2 ^ 59
def prefixEnd_7023317 : Nat := 4983230072969 + 3 ^ 40 * 7023317 * 2
def baseEnd_7023317 : Nat := 44522684072760530538739

theorem tailTrace_7023317 : CollatzResearch.WordTrace tailWord_7023317 prefixEnd_7023317 44522684072760530538739 := by
  unfold tailWord_7023317
  simp only [CollatzResearch.WordTrace]
  refine ⟨256161415496729470892668205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170774276997819647261778803 256161415496729470892668205)
  ·
    refine ⟨96060530811273551584750577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256161415496729470892668205 96060530811273551584750577)
    ·
      refine ⟨72045398108455163688562933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96060530811273551584750577 72045398108455163688562933)
      ·
        refine ⟨6754256072667671595802775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72045398108455163688562933 6754256072667671595802775)
        ·
          refine ⟨10131384109001507393704163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754256072667671595802775 10131384109001507393704163)
          ·
            refine ⟨15197076163502261090556245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10131384109001507393704163 15197076163502261090556245)
            ·
              refine ⟨44522684072760530538739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15197076163502261090556245 44522684072760530538739)
              ·
                rfl

theorem cell23_7023317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 10].length) (baseStart_7023317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023317 prefixEnd_7023317 := by exact prefixLift 7023317
  have htrace : WordTrace (prefixWord ++ tailWord_7023317) baseStart_7023317 baseEnd_7023317 := by
    simpa [prefixWord, tailWord_7023317, baseEnd_7023317] using wordTrace_append hprefix tailTrace_7023317
  have hstable : (prefixWord ++ tailWord_7023317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023317).length < 2 ^ (prefixWord ++ tailWord_7023317).sum := by decide
  have hdescent : baseEnd_7023317 < baseStart_7023317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023337 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 5, 3, 2]
def baseStart_7023337 : Nat := 118140960795 + 7023337 * 2 ^ 59
def prefixEnd_7023337 : Nat := 4983230072969 + 3 ^ 40 * 7023337 * 2
def baseEnd_7023337 : Nat := 3606347679506692895387767

theorem tailTrace_7023337 : CollatzResearch.WordTrace tailWord_7023337 prefixEnd_7023337 3606347679506692895387767 := by
  unfold tailWord_7023337
  simp only [CollatzResearch.WordTrace]
  refine ⟨256162144956657014308396265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170774763304438009538930843 256162144956657014308396265)
  ·
    refine ⟨192121608717492760731297199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256162144956657014308396265 192121608717492760731297199)
    ·
      refine ⟨288182413076239141096945799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192121608717492760731297199 288182413076239141096945799)
      ·
        refine ⟨432273619614358711645418699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288182413076239141096945799 432273619614358711645418699)
        ·
          refine ⟨648410429421538067468128049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432273619614358711645418699 648410429421538067468128049)
          ·
            refine ⟨486307822066153550601096037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648410429421538067468128049 486307822066153550601096037)
            ·
              refine ⟨91182716637403790737705507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 486307822066153550601096037 91182716637403790737705507)
              ·
                refine ⟨136774074956105686106558261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91182716637403790737705507 136774074956105686106558261)
                ·
                  refine ⟨12822569527134908072489837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136774074956105686106558261 12822569527134908072489837)
                  ·
                    refine ⟨4808463572675590527183689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12822569527134908072489837 4808463572675590527183689)
                    ·
                      refine ⟨3606347679506692895387767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808463572675590527183689 3606347679506692895387767)
                      ·
                        rfl

theorem cell23_7023337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 3, 2].length) (baseStart_7023337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023337 prefixEnd_7023337 := by exact prefixLift 7023337
  have htrace : WordTrace (prefixWord ++ tailWord_7023337) baseStart_7023337 baseEnd_7023337 := by
    simpa [prefixWord, tailWord_7023337, baseEnd_7023337] using wordTrace_append hprefix tailTrace_7023337
  have hstable : (prefixWord ++ tailWord_7023337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023337).length < 2 ^ (prefixWord ++ tailWord_7023337).sum := by decide
  have hdescent : baseEnd_7023337 < baseStart_7023337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023354 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2]
def baseStart_7023354 : Nat := 118140960795 + 7023354 * 2 ^ 59
def prefixEnd_7023354 : Nat := 4983230072969 + 3 ^ 40 * 7023354 * 2
def baseEnd_7023354 : Nat := 3606356408677819328875189

theorem tailTrace_7023354 : CollatzResearch.WordTrace tailWord_7023354 prefixEnd_7023354 3606356408677819328875189 := by
  unfold tailWord_7023354
  simp only [CollatzResearch.WordTrace]
  refine ⟨64040691249398856552941279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170775176665063617474510077 64040691249398856552941279)
  ·
    refine ⟨96061036874098284829411919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64040691249398856552941279 96061036874098284829411919)
    ·
      refine ⟨144091555311147427244117879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96061036874098284829411919 144091555311147427244117879)
      ·
        refine ⟨216137332966721140866176819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144091555311147427244117879 216137332966721140866176819)
        ·
          refine ⟨324205999450081711299265229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216137332966721140866176819 324205999450081711299265229)
          ·
            refine ⟨121577249793780641737224461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324205999450081711299265229 121577249793780641737224461)
            ·
              refine ⟨45591468672667740651459173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121577249793780641737224461 45591468672667740651459173)
              ·
                refine ⟨8548400376125201372148595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45591468672667740651459173 8548400376125201372148595)
                ·
                  refine ⟨12822600564187802058222893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8548400376125201372148595 12822600564187802058222893)
                  ·
                    refine ⟨4808475211570425771833585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12822600564187802058222893 4808475211570425771833585)
                    ·
                      refine ⟨3606356408677819328875189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808475211570425771833585 3606356408677819328875189)
                      ·
                        rfl

theorem cell23_7023354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2].length) (baseStart_7023354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023354 prefixEnd_7023354 := by exact prefixLift 7023354
  have htrace : WordTrace (prefixWord ++ tailWord_7023354) baseStart_7023354 baseEnd_7023354 := by
    simpa [prefixWord, tailWord_7023354, baseEnd_7023354] using wordTrace_append hprefix tailTrace_7023354
  have hstable : (prefixWord ++ tailWord_7023354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023354).length < 2 ^ (prefixWord ++ tailWord_7023354).sum := by decide
  have hdescent : baseEnd_7023354 < baseStart_7023354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023447 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_7023447 : Nat := 118140960795 + 7023447 * 2 ^ 59
def prefixEnd_7023447 : Nat := 4983230072969 + 3 ^ 40 * 7023447 * 2
def baseEnd_7023447 : Nat := 3606404162378687465012261

theorem tailTrace_7023447 : CollatzResearch.WordTrace tailWord_7023447 prefixEnd_7023447 3606404162378687465012261 := by
  unfold tailWord_7023447
  simp only [CollatzResearch.WordTrace]
  refine ⟨256166156986258503094900595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170777437990839002063267063 256166156986258503094900595)
  ·
    refine ⟨384249235479387754642350893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256166156986258503094900595 384249235479387754642350893)
    ·
      refine ⟨144093463304770407990881585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384249235479387754642350893 144093463304770407990881585)
      ·
        refine ⟨108070097478577805993161189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144093463304770407990881585 108070097478577805993161189)
        ·
          refine ⟨20263143277233338623717723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108070097478577805993161189 20263143277233338623717723)
          ·
            refine ⟨30394714915850007935576585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20263143277233338623717723 30394714915850007935576585)
            ·
              refine ⟨22796036186887505951682439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30394714915850007935576585 22796036186887505951682439)
              ·
                refine ⟨34194054280331258927523659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22796036186887505951682439 34194054280331258927523659)
                ·
                  refine ⟨51291081420496888391285489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34194054280331258927523659 51291081420496888391285489)
                  ·
                    refine ⟨38468311065372666293464117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51291081420496888391285489 38468311065372666293464117)
                    ·
                      refine ⟨3606404162378687465012261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38468311065372666293464117 3606404162378687465012261)
                      ·
                        rfl

theorem cell23_7023447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_7023447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023447 prefixEnd_7023447 := by exact prefixLift 7023447
  have htrace : WordTrace (prefixWord ++ tailWord_7023447) baseStart_7023447 baseEnd_7023447 := by
    simpa [prefixWord, tailWord_7023447, baseEnd_7023447] using wordTrace_append hprefix tailTrace_7023447
  have hstable : (prefixWord ++ tailWord_7023447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023447).length < 2 ^ (prefixWord ++ tailWord_7023447).sum := by decide
  have hdescent : baseEnd_7023447 < baseStart_7023447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023467 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 5, 4]
def baseStart_7023467 : Nat := 118140960795 + 7023467 * 2 ^ 59
def prefixEnd_7023467 : Nat := 4983230072969 + 3 ^ 40 * 7023467 * 2
def baseEnd_7023467 : Nat := 1202138143997259128920723

theorem tailTrace_7023467 : CollatzResearch.WordTrace tailWord_7023467 prefixEnd_7023467 1202138143997259128920723 := by
  unfold tailWord_7023467
  simp only [CollatzResearch.WordTrace]
  refine ⟨256166886446186046510628655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170777924297457364340419103 256166886446186046510628655)
  ·
    refine ⟨384250329669279069765942983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256166886446186046510628655 384250329669279069765942983)
    ·
      refine ⟨576375494503918604648914475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384250329669279069765942983 576375494503918604648914475)
      ·
        refine ⟨864563241755877906973371713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576375494503918604648914475 864563241755877906973371713)
        ·
          refine ⟨648422431316908430230028785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 864563241755877906973371713 648422431316908430230028785)
          ·
            refine ⟨486316823487681322672521589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648422431316908430230028785 486316823487681322672521589)
            ·
              refine ⟨45592202201970124000548899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 486316823487681322672521589 45592202201970124000548899)
              ·
                refine ⟨68388303302955186000823349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45592202201970124000548899 68388303302955186000823349)
                ·
                  refine ⟨6411403434652048687577189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68388303302955186000823349 6411403434652048687577189)
                  ·
                    refine ⟨1202138143997259128920723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6411403434652048687577189 1202138143997259128920723)
                    ·
                      rfl

theorem cell23_7023467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 4].length) (baseStart_7023467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023467 prefixEnd_7023467 := by exact prefixLift 7023467
  have htrace : WordTrace (prefixWord ++ tailWord_7023467) baseStart_7023467 baseEnd_7023467 := by
    simpa [prefixWord, tailWord_7023467, baseEnd_7023467] using wordTrace_append hprefix tailTrace_7023467
  have hstable : (prefixWord ++ tailWord_7023467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023467).length < 2 ^ (prefixWord ++ tailWord_7023467).sum := by decide
  have hdescent : baseEnd_7023467 < baseStart_7023467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023474 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 2, 1, 4]
def baseStart_7023474 : Nat := 118140960795 + 7023474 * 2 ^ 59
def prefixEnd_7023474 : Nat := 4983230072969 + 3 ^ 40 * 7023474 * 2
def baseEnd_7023474 : Nat := 3606418026356358859374637

theorem tailTrace_7023474 : CollatzResearch.WordTrace tailWord_7023474 prefixEnd_7023474 3606418026356358859374637 := by
  unfold tailWord_7023474
  simp only [CollatzResearch.WordTrace]
  refine ⟨64041785439290171676533369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170778094504773791137422317 64041785439290171676533369)
  ·
    refine ⟨48031339079467628757400027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64041785439290171676533369 48031339079467628757400027)
    ·
      refine ⟨72047008619201443136100041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48031339079467628757400027 72047008619201443136100041)
      ·
        refine ⟨54035256464401082352075031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72047008619201443136100041 54035256464401082352075031)
        ·
          refine ⟨81052884696601623528112547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54035256464401082352075031 81052884696601623528112547)
          ·
            refine ⟨121579327044902435292168821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81052884696601623528112547 121579327044902435292168821)
            ·
              refine ⟨11398061910459603308640827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121579327044902435292168821 11398061910459603308640827)
              ·
                refine ⟨17097092865689404962961241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11398061910459603308640827 17097092865689404962961241)
                ·
                  refine ⟨12822819649267053722220931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17097092865689404962961241 12822819649267053722220931)
                  ·
                    refine ⟨19234229473900580583331397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12822819649267053722220931 19234229473900580583331397)
                    ·
                      refine ⟨3606418026356358859374637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19234229473900580583331397 3606418026356358859374637)
                      ·
                        rfl

theorem cell23_7023474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_7023474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023474 prefixEnd_7023474 := by exact prefixLift 7023474
  have htrace : WordTrace (prefixWord ++ tailWord_7023474) baseStart_7023474 baseEnd_7023474 := by
    simpa [prefixWord, tailWord_7023474, baseEnd_7023474] using wordTrace_append hprefix tailTrace_7023474
  have hstable : (prefixWord ++ tailWord_7023474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023474).length < 2 ^ (prefixWord ++ tailWord_7023474).sum := by decide
  have hdescent : baseEnd_7023474 < baseStart_7023474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023497 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 8]
def baseStart_7023497 : Nat := 118140960795 + 7023497 * 2 ^ 59
def prefixEnd_7023497 : Nat := 4983230072969 + 3 ^ 40 * 7023497 * 2
def baseEnd_7023497 : Nat := 400714426267934696598559

theorem tailTrace_7023497 : CollatzResearch.WordTrace tailWord_7023497 prefixEnd_7023497 400714426267934696598559 := by
  unfold tailWord_7023497
  simp only [CollatzResearch.WordTrace]
  refine ⟨256167980636077361634220745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170778653757384907756147163 256167980636077361634220745)
  ·
    refine ⟨192125985477058021225665559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256167980636077361634220745 192125985477058021225665559)
    ·
      refine ⟨288188978215587031838498339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192125985477058021225665559 288188978215587031838498339)
      ·
        refine ⟨432283467323380547757747509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288188978215587031838498339 432283467323380547757747509)
        ·
          refine ⟨40526575061566926352288829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 432283467323380547757747509 40526575061566926352288829)
          ·
            refine ⟨15197465648087597382108311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40526575061566926352288829 15197465648087597382108311)
            ·
              refine ⟨22796198472131396073162467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15197465648087597382108311 22796198472131396073162467)
              ·
                refine ⟨34194297708197094109743701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22796198472131396073162467 34194297708197094109743701)
                ·
                  refine ⟨400714426267934696598559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34194297708197094109743701 400714426267934696598559)
                  ·
                    rfl

theorem cell23_7023497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 8].length) (baseStart_7023497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023497 prefixEnd_7023497 := by exact prefixLift 7023497
  have htrace : WordTrace (prefixWord ++ tailWord_7023497) baseStart_7023497 baseEnd_7023497 := by
    simpa [prefixWord, tailWord_7023497, baseEnd_7023497] using wordTrace_append hprefix tailTrace_7023497
  have hstable : (prefixWord ++ tailWord_7023497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023497).length < 2 ^ (prefixWord ++ tailWord_7023497).sum := by decide
  have hdescent : baseEnd_7023497 < baseStart_7023497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023517 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_7023517 : Nat := 118140960795 + 7023517 * 2 ^ 59
def prefixEnd_7023517 : Nat := 4983230072969 + 3 ^ 40 * 7023517 * 2
def baseEnd_7023517 : Nat := 3606440106024502191136939

theorem tailTrace_7023517 : CollatzResearch.WordTrace tailWord_7023517 prefixEnd_7023517 3606440106024502191136939 := by
  unfold tailWord_7023517
  simp only [CollatzResearch.WordTrace]
  refine ⟨256168710096004905049948805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170779140064003270033299203 256168710096004905049948805)
  ·
    refine ⟨48031633143000919696865401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256168710096004905049948805 48031633143000919696865401)
    ·
      refine ⟨36023724857250689772649051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48031633143000919696865401 36023724857250689772649051)
      ·
        refine ⟨54035587285876034658973577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36023724857250689772649051 54035587285876034658973577)
        ·
          refine ⟨40526690464407025994230183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54035587285876034658973577 40526690464407025994230183)
          ·
            refine ⟨60790035696610538991345275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40526690464407025994230183 60790035696610538991345275)
            ·
              refine ⟨91185053544915808487017913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60790035696610538991345275 91185053544915808487017913)
              ·
                refine ⟨68388790158686856365263435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91185053544915808487017913 68388790158686856365263435)
                ·
                  refine ⟨102583185238030284547895153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68388790158686856365263435 102583185238030284547895153)
                  ·
                    refine ⟨76937388928522713410921365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102583185238030284547895153 76937388928522713410921365)
                    ·
                      refine ⟨3606440106024502191136939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76937388928522713410921365 3606440106024502191136939)
                      ·
                        rfl

theorem cell23_7023517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_7023517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023517 prefixEnd_7023517 := by exact prefixLift 7023517
  have htrace : WordTrace (prefixWord ++ tailWord_7023517) baseStart_7023517 baseEnd_7023517 := by
    simpa [prefixWord, tailWord_7023517, baseEnd_7023517] using wordTrace_append hprefix tailTrace_7023517
  have hstable : (prefixWord ++ tailWord_7023517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023517).length < 2 ^ (prefixWord ++ tailWord_7023517).sum := by decide
  have hdescent : baseEnd_7023517 < baseStart_7023517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023544 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 1, 5]
def baseStart_7023544 : Nat := 118140960795 + 7023544 * 2 ^ 59
def prefixEnd_7023544 : Nat := 4983230072969 + 3 ^ 40 * 7023544 * 2
def baseEnd_7023544 : Nat := 1202151323334057861833105

theorem tailTrace_7023544 : CollatzResearch.WordTrace tailWord_7023544 prefixEnd_7023544 1202151323334057861833105 := by
  unfold tailWord_7023544
  simp only [CollatzResearch.WordTrace]
  refine ⟨128084847433453544330590843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170779796577938059107454457 128084847433453544330590843)
  ·
    refine ⟨192127271150180316495886265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128084847433453544330590843 192127271150180316495886265)
    ·
      refine ⟨144095453362635237371914699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192127271150180316495886265 144095453362635237371914699)
      ·
        refine ⟨216143180043952856057872049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144095453362635237371914699 216143180043952856057872049)
        ·
          refine ⟨162107385032964642043404037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216143180043952856057872049 162107385032964642043404037)
          ·
            refine ⟨30395134693680870383138257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162107385032964642043404037 30395134693680870383138257)
            ·
              refine ⟨22796351020260652787353693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30395134693680870383138257 22796351020260652787353693)
              ·
                refine ⟨8548631632597744795257635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22796351020260652787353693 8548631632597744795257635)
                ·
                  refine ⟨12822947448896617192886453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8548631632597744795257635 12822947448896617192886453)
                  ·
                    refine ⟨1202151323334057861833105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12822947448896617192886453 1202151323334057861833105)
                    ·
                      rfl

theorem cell23_7023544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_7023544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023544 prefixEnd_7023544 := by exact prefixLift 7023544
  have htrace : WordTrace (prefixWord ++ tailWord_7023544) baseStart_7023544 baseEnd_7023544 := by
    simpa [prefixWord, tailWord_7023544, baseEnd_7023544] using wordTrace_append hprefix tailTrace_7023544
  have hstable : (prefixWord ++ tailWord_7023544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023544).length < 2 ^ (prefixWord ++ tailWord_7023544).sum := by decide
  have hdescent : baseEnd_7023544 < baseStart_7023544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023564 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_7023564 : Nat := 118140960795 + 7023564 * 2 ^ 59
def prefixEnd_7023564 : Nat := 4983230072969 + 3 ^ 40 * 7023564 * 2
def baseEnd_7023564 : Nat := 3606464239615263507249223

theorem tailTrace_7023564 : CollatzResearch.WordTrace tailWord_7023564 prefixEnd_7023564 3606464239615263507249223 := by
  unfold tailWord_7023564
  simp only [CollatzResearch.WordTrace]
  refine ⟨128085212163417316038454873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170780282884556421384606497 128085212163417316038454873)
  ·
    refine ⟨96063909122562987028841155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128085212163417316038454873 96063909122562987028841155)
    ·
      refine ⟨144095863683844480543261733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96063909122562987028841155 144095863683844480543261733)
      ·
        refine ⟨27017974440720840101861575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144095863683844480543261733 27017974440720840101861575)
        ·
          refine ⟨40526961661081260152792363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27017974440720840101861575 40526961661081260152792363)
          ·
            refine ⟨60790442491621890229188545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40526961661081260152792363 60790442491621890229188545)
            ·
              refine ⟨45592831868716417671891409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60790442491621890229188545 45592831868716417671891409)
              ·
                refine ⟨34194623901537313253918557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45592831868716417671891409 34194623901537313253918557)
                ·
                  refine ⟨12822983963076492470219459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34194623901537313253918557 12822983963076492470219459)
                  ·
                    refine ⟨19234475944614738705329189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12822983963076492470219459 19234475944614738705329189)
                    ·
                      refine ⟨3606464239615263507249223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19234475944614738705329189 3606464239615263507249223)
                      ·
                        rfl

theorem cell23_7023564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_7023564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023564 prefixEnd_7023564 := by exact prefixLift 7023564
  have htrace : WordTrace (prefixWord ++ tailWord_7023564) baseStart_7023564 baseEnd_7023564 := by
    simpa [prefixWord, tailWord_7023564, baseEnd_7023564] using wordTrace_append hprefix tailTrace_7023564
  have hstable : (prefixWord ++ tailWord_7023564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023564).length < 2 ^ (prefixWord ++ tailWord_7023564).sum := by decide
  have hdescent : baseEnd_7023564 < baseStart_7023564 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023565 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 6]
def baseStart_7023565 : Nat := 118140960795 + 7023565 * 2 ^ 59
def prefixEnd_7023565 : Nat := 4983230072969 + 3 ^ 40 * 7023565 * 2
def baseEnd_7023565 : Nat := 400718305899546444815191

theorem tailTrace_7023565 : CollatzResearch.WordTrace tailWord_7023565 prefixEnd_7023565 400718305899546444815191 := by
  unfold tailWord_7023565
  simp only [CollatzResearch.WordTrace]
  refine ⟨256170460799831009247696149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170780307199887339498464099 256170460799831009247696149)
  ·
    refine ⟨12007990349992078558485757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 256170460799831009247696149 12007990349992078558485757)
    ·
      refine ⟨4502996381247029459432159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12007990349992078558485757 4502996381247029459432159)
      ·
        refine ⟨6754494571870544189148239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4502996381247029459432159 6754494571870544189148239)
        ·
          refine ⟨10131741857805816283722359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754494571870544189148239 10131741857805816283722359)
          ·
            refine ⟨15197612786708724425583539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10131741857805816283722359 15197612786708724425583539)
            ·
              refine ⟨22796419180063086638375309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15197612786708724425583539 22796419180063086638375309)
              ·
                refine ⟨8548657192523657489390741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22796419180063086638375309 8548657192523657489390741)
                ·
                  refine ⟨400718305899546444815191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8548657192523657489390741 400718305899546444815191)
                  ·
                    rfl

theorem cell23_7023565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_7023565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023565 prefixEnd_7023565 := by exact prefixLift 7023565
  have htrace : WordTrace (prefixWord ++ tailWord_7023565) baseStart_7023565 baseEnd_7023565 := by
    simpa [prefixWord, tailWord_7023565, baseEnd_7023565] using wordTrace_append hprefix tailTrace_7023565
  have hstable : (prefixWord ++ tailWord_7023565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023565).length < 2 ^ (prefixWord ++ tailWord_7023565).sum := by decide
  have hdescent : baseEnd_7023565 < baseStart_7023565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023581 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_7023581 : Nat := 118140960795 + 7023581 * 2 ^ 59
def prefixEnd_7023581 : Nat := 4983230072969 + 3 ^ 40 * 7023581 * 2
def baseEnd_7023581 : Nat := 3606472968786389940736645

theorem tailTrace_7023581 : CollatzResearch.WordTrace tailWord_7023581 prefixEnd_7023581 3606472968786389940736645 := by
  unfold tailWord_7023581
  simp only [CollatzResearch.WordTrace]
  refine ⟨256171044367773043980278597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170780696245182029320185731 256171044367773043980278597)
  ·
    refine ⟨48032070818957445746302237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256171044367773043980278597 48032070818957445746302237)
    ·
      refine ⟨18012026557109042154863339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48032070818957445746302237 18012026557109042154863339)
      ·
        refine ⟨27018039835663563232295009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18012026557109042154863339 27018039835663563232295009)
        ·
          refine ⟨20263529876747672424221257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27018039835663563232295009 20263529876747672424221257)
          ·
            refine ⟨15197647407560754318165943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20263529876747672424221257 15197647407560754318165943)
            ·
              refine ⟨22796471111341131477248915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15197647407560754318165943 22796471111341131477248915)
              ·
                refine ⟨34194706667011697215873373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22796471111341131477248915 34194706667011697215873373)
                ·
                  refine ⟨12823015000129386455952515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34194706667011697215873373 12823015000129386455952515)
                  ·
                    refine ⟨19234522500194079683928773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12823015000129386455952515 19234522500194079683928773)
                    ·
                      refine ⟨3606472968786389940736645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19234522500194079683928773 3606472968786389940736645)
                      ·
                        rfl

theorem cell23_7023581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_7023581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023581 prefixEnd_7023581 := by exact prefixLift 7023581
  have htrace : WordTrace (prefixWord ++ tailWord_7023581) baseStart_7023581 baseEnd_7023581 := by
    simpa [prefixWord, tailWord_7023581, baseEnd_7023581] using wordTrace_append hprefix tailTrace_7023581
  have hstable : (prefixWord ++ tailWord_7023581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023581).length < 2 ^ (prefixWord ++ tailWord_7023581).sum := by decide
  have hdescent : baseEnd_7023581 < baseStart_7023581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023587 : List Nat := [1, 1, 1, 6, 1, 1, 1, 11]
def baseStart_7023587 : Nat := 118140960795 + 7023587 * 2 ^ 59
def prefixEnd_7023587 : Nat := 4983230072969 + 3 ^ 40 * 7023587 * 2
def baseEnd_7023587 : Nat := 133573187024826552491171

theorem tailTrace_7023587 : CollatzResearch.WordTrace tailWord_7023587 prefixEnd_7023587 133573187024826552491171 := by
  unfold tailWord_7023587
  simp only [CollatzResearch.WordTrace]
  refine ⟨256171263205751307004997015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170780842137167538003331343 256171263205751307004997015)
  ·
    refine ⟨384256894808626960507495523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256171263205751307004997015 384256894808626960507495523)
    ·
      refine ⟨576385342212940440761243285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384256894808626960507495523 576385342212940440761243285)
      ·
        refine ⟨27018062916231583160683279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 576385342212940440761243285 27018062916231583160683279)
        ·
          refine ⟨40527094374347374741024919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27018062916231583160683279 40527094374347374741024919)
          ·
            refine ⟨60790641561521062111537379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40527094374347374741024919 60790641561521062111537379)
            ·
              refine ⟨91185962342281593167306069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60790641561521062111537379 91185962342281593167306069)
              ·
                refine ⟨133573187024826552491171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 91185962342281593167306069 133573187024826552491171)
                ·
                  rfl

theorem cell23_7023587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 11].length) (baseStart_7023587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023587 prefixEnd_7023587 := by exact prefixLift 7023587
  have htrace : WordTrace (prefixWord ++ tailWord_7023587) baseStart_7023587 baseEnd_7023587 := by
    simpa [prefixWord, tailWord_7023587, baseEnd_7023587] using wordTrace_append hprefix tailTrace_7023587
  have hstable : (prefixWord ++ tailWord_7023587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023587).length < 2 ^ (prefixWord ++ tailWord_7023587).sum := by decide
  have hdescent : baseEnd_7023587 < baseStart_7023587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023594 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_7023594 : Nat := 118140960795 + 7023594 * 2 ^ 59
def prefixEnd_7023594 : Nat := 4983230072969 + 3 ^ 40 * 7023594 * 2
def baseEnd_7023594 : Nat := 3606479644034898389874085

theorem tailTrace_7023594 : CollatzResearch.WordTrace tailWord_7023594 prefixEnd_7023594 3606479644034898389874085 := by
  unfold tailWord_7023594
  simp only [CollatzResearch.WordTrace]
  refine ⟨64042879629181486800125459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170781012344483964800334557 64042879629181486800125459)
  ·
    refine ⟨96064319443772230200188189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64042879629181486800125459 96064319443772230200188189)
    ·
      refine ⟨36024119791414586325070571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96064319443772230200188189 36024119791414586325070571)
      ·
        refine ⟨54036179687121879487605857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36024119791414586325070571 54036179687121879487605857)
        ·
          refine ⟨40527134765341409615704393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54036179687121879487605857 40527134765341409615704393)
          ·
            refine ⟨30395351074006057211778295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40527134765341409615704393 30395351074006057211778295)
            ·
              refine ⟨45593026611009085817667443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30395351074006057211778295 45593026611009085817667443)
              ·
                refine ⟨68389539916513628726501165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45593026611009085817667443 68389539916513628726501165)
                ·
                  refine ⟨25646077468692610772437937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68389539916513628726501165 25646077468692610772437937)
                  ·
                    refine ⟨19234558101519458079328453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25646077468692610772437937 19234558101519458079328453)
                    ·
                      refine ⟨3606479644034898389874085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19234558101519458079328453 3606479644034898389874085)
                      ·
                        rfl

theorem cell23_7023594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_7023594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023594 prefixEnd_7023594 := by exact prefixLift 7023594
  have htrace : WordTrace (prefixWord ++ tailWord_7023594) baseStart_7023594 baseEnd_7023594 := by
    simpa [prefixWord, tailWord_7023594, baseEnd_7023594] using wordTrace_append hprefix tailTrace_7023594
  have hstable : (prefixWord ++ tailWord_7023594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023594).length < 2 ^ (prefixWord ++ tailWord_7023594).sum := by decide
  have hdescent : baseEnd_7023594 < baseStart_7023594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023601 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 5]
def baseStart_7023601 : Nat := 118140960795 + 7023601 * 2 ^ 59
def prefixEnd_7023601 : Nat := 4983230072969 + 3 ^ 40 * 7023601 * 2
def baseEnd_7023601 : Nat := 3606483238399479862486553

theorem tailTrace_7023601 : CollatzResearch.WordTrace tailWord_7023601 prefixEnd_7023601 3606483238399479862486553 := by
  unfold tailWord_7023601
  simp only [CollatzResearch.WordTrace]
  refine ⟨256171773827700587396006657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170781182551800391597337771 256171773827700587396006657)
  ·
    refine ⟨192128830370775440547004993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256171773827700587396006657 192128830370775440547004993)
    ·
      refine ⟨144096622778081580410253745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192128830370775440547004993 144096622778081580410253745)
      ·
        refine ⟨108072467083561185307690309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144096622778081580410253745 108072467083561185307690309)
        ·
          refine ⟨20263587578167722245191933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108072467083561185307690309 20263587578167722245191933)
          ·
            refine ⟨7598845341812895841946975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20263587578167722245191933 7598845341812895841946975)
            ·
              refine ⟨11398268012719343762920463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7598845341812895841946975 11398268012719343762920463)
              ·
                refine ⟨17097402019079015644380695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11398268012719343762920463 17097402019079015644380695)
                ·
                  refine ⟨25646103028618523466571043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17097402019079015644380695 25646103028618523466571043)
                  ·
                    refine ⟨38469154542927785199856565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25646103028618523466571043 38469154542927785199856565)
                    ·
                      refine ⟨3606483238399479862486553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38469154542927785199856565 3606483238399479862486553)
                      ·
                        rfl

theorem cell23_7023601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_7023601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023601 prefixEnd_7023601 := by exact prefixLift 7023601
  have htrace : WordTrace (prefixWord ++ tailWord_7023601) baseStart_7023601 baseEnd_7023601 := by
    simpa [prefixWord, tailWord_7023601, baseEnd_7023601] using wordTrace_append hprefix tailTrace_7023601
  have hstable : (prefixWord ++ tailWord_7023601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023601).length < 2 ^ (prefixWord ++ tailWord_7023601).sum := by decide
  have hdescent : baseEnd_7023601 < baseStart_7023601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023641 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 3, 3, 2]
def baseStart_7023641 : Nat := 118140960795 + 7023641 * 2 ^ 59
def prefixEnd_7023641 : Nat := 4983230072969 + 3 ^ 40 * 7023641 * 2
def baseEnd_7023641 : Nat := 3606503777625659705986369

theorem tailTrace_7023641 : CollatzResearch.WordTrace tailWord_7023641 prefixEnd_7023641 3606503777625659705986369 := by
  unfold tailWord_7023641
  simp only [CollatzResearch.WordTrace]
  refine ⟨256173232747555674227462777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170782155165037116151641851 256173232747555674227462777)
  ·
    refine ⟨192129924560666755670597083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256173232747555674227462777 192129924560666755670597083)
    ·
      refine ⟨288194886841000133505895625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192129924560666755670597083 288194886841000133505895625)
      ·
        refine ⟨216146165130750100129421719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288194886841000133505895625 216146165130750100129421719)
        ·
          refine ⟨324219247696125150194132579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216146165130750100129421719 324219247696125150194132579)
          ·
            refine ⟨486328871544187725291198869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324219247696125150194132579 486328871544187725291198869)
            ·
              refine ⟨22796665853633799623024947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 486328871544187725291198869 22796665853633799623024947)
              ·
                refine ⟨34194998780450699434537421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22796665853633799623024947 34194998780450699434537421)
                ·
                  refine ⟨12823124542669012287951533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34194998780450699434537421 12823124542669012287951533)
                  ·
                    refine ⟨4808671703500879607981825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12823124542669012287951533 4808671703500879607981825)
                    ·
                      refine ⟨3606503777625659705986369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808671703500879607981825 3606503777625659705986369)
                      ·
                        rfl

theorem cell23_7023641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 3, 2].length) (baseStart_7023641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023641 prefixEnd_7023641 := by exact prefixLift 7023641
  have htrace : WordTrace (prefixWord ++ tailWord_7023641) baseStart_7023641 baseEnd_7023641 := by
    simpa [prefixWord, tailWord_7023641, baseEnd_7023641] using wordTrace_append hprefix tailTrace_7023641
  have hstable : (prefixWord ++ tailWord_7023641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023641).length < 2 ^ (prefixWord ++ tailWord_7023641).sum := by decide
  have hdescent : baseEnd_7023641 < baseStart_7023641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023674 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3]
def baseStart_7023674 : Nat := 118140960795 + 7023674 * 2 ^ 59
def prefixEnd_7023674 : Nat := 4983230072969 + 3 ^ 40 * 7023674 * 2
def baseEnd_7023674 : Nat := 3606520722487258076873717

theorem tailTrace_7023674 : CollatzResearch.WordTrace tailWord_7023674 prefixEnd_7023674 3606520722487258076873717 := by
  unfold tailWord_7023674
  simp only [CollatzResearch.WordTrace]
  refine ⟨64043609089109030215853519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170782957570957413908942717 64043609089109030215853519)
  ·
    refine ⟨96065413633663545323780279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64043609089109030215853519 96065413633663545323780279)
    ·
      refine ⟨144098120450495317985670419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96065413633663545323780279 144098120450495317985670419)
      ·
        refine ⟨216147180675742976978505629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144098120450495317985670419 216147180675742976978505629)
        ·
          refine ⟨81055192753403616366939611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216147180675742976978505629 81055192753403616366939611)
          ·
            refine ⟨121582789130105424550409417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81055192753403616366939611 121582789130105424550409417)
            ·
              refine ⟨91187091847579068412807063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121582789130105424550409417 91187091847579068412807063)
              ·
                refine ⟨136780637771368602619210595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91187091847579068412807063 136780637771368602619210595)
                ·
                  refine ⟨205170956657052903928815893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136780637771368602619210595 205170956657052903928815893)
                  ·
                    refine ⟨9617388593299354871663245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 205170956657052903928815893 9617388593299354871663245)
                    ·
                      refine ⟨3606520722487258076873717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9617388593299354871663245 3606520722487258076873717)
                      ·
                        rfl

theorem cell23_7023674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3].length) (baseStart_7023674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023674 prefixEnd_7023674 := by exact prefixLift 7023674
  have htrace : WordTrace (prefixWord ++ tailWord_7023674) baseStart_7023674 baseEnd_7023674 := by
    simpa [prefixWord, tailWord_7023674, baseEnd_7023674] using wordTrace_append hprefix tailTrace_7023674
  have hstable : (prefixWord ++ tailWord_7023674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023674).length < 2 ^ (prefixWord ++ tailWord_7023674).sum := by decide
  have hdescent : baseEnd_7023674 < baseStart_7023674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023694 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_7023694 : Nat := 118140960795 + 7023694 * 2 ^ 59
def prefixEnd_7023694 : Nat := 4983230072969 + 3 ^ 40 * 7023694 * 2
def baseEnd_7023694 : Nat := 400725665788927555402625

theorem tailTrace_7023694 : CollatzResearch.WordTrace tailWord_7023694 prefixEnd_7023694 400725665788927555402625 := by
  unfold tailWord_7023694
  simp only [CollatzResearch.WordTrace]
  refine ⟨32021895727045458034892767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170783443877575776186094757 32021895727045458034892767)
  ·
    refine ⟨48032843590568187052339151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32021895727045458034892767 48032843590568187052339151)
    ·
      refine ⟨72049265385852280578508727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48032843590568187052339151 72049265385852280578508727)
      ·
        refine ⟨108073898078778420867763091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72049265385852280578508727 108073898078778420867763091)
        ·
          refine ⟨162110847118167631301644637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108073898078778420867763091 162110847118167631301644637)
          ·
            refine ⟨60791567669312861738116739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162110847118167631301644637 60791567669312861738116739)
            ·
              refine ⟨91187351503969292607175109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60791567669312861738116739 91187351503969292607175109)
              ·
                refine ⟨17097628406994242363845333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91187351503969292607175109 17097628406994242363845333)
                ·
                  refine ⟨400725665788927555402625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17097628406994242363845333 400725665788927555402625)
                  ·
                    rfl

theorem cell23_7023694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_7023694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023694 prefixEnd_7023694 := by exact prefixLift 7023694
  have htrace : WordTrace (prefixWord ++ tailWord_7023694) baseStart_7023694 baseEnd_7023694 := by
    simpa [prefixWord, tailWord_7023694, baseEnd_7023694] using wordTrace_append hprefix tailTrace_7023694
  have hstable : (prefixWord ++ tailWord_7023694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023694).length < 2 ^ (prefixWord ++ tailWord_7023694).sum := by decide
  have hdescent : baseEnd_7023694 < baseStart_7023694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023728 : List Nat := [2, 1, 1, 1, 5, 1, 5, 2, 5]
def baseStart_7023728 : Nat := 118140960795 + 7023728 * 2 ^ 59
def prefixEnd_7023728 : Nat := 4983230072969 + 3 ^ 40 * 7023728 * 2
def baseEnd_7023728 : Nat := 400727605604733429510941

theorem tailTrace_7023728 : CollatzResearch.WordTrace tailWord_7023728 prefixEnd_7023728 400727605604733429510941 := by
  unfold tailWord_7023728
  simp only [CollatzResearch.WordTrace]
  refine ⟨128088202949120244042939919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170784270598826992057253225 128088202949120244042939919)
  ·
    refine ⟨192132304423680366064409879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128088202949120244042939919 192132304423680366064409879)
    ·
      refine ⟨288198456635520549096614819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192132304423680366064409879 288198456635520549096614819)
      ·
        refine ⟨432297684953280823644922229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288198456635520549096614819 432297684953280823644922229)
        ·
          refine ⟨40527907964370077216711459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 432297684953280823644922229 40527907964370077216711459)
          ·
            refine ⟨60791861946555115825067189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40527907964370077216711459 60791861946555115825067189)
            ·
              refine ⟨5699237057489542108600049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60791861946555115825067189 5699237057489542108600049)
              ·
                refine ⟨4274427793117156581450037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5699237057489542108600049 4274427793117156581450037)
                ·
                  refine ⟨400727605604733429510941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4274427793117156581450037 400727605604733429510941)
                  ·
                    rfl

theorem cell23_7023728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 2, 5].length) (baseStart_7023728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023728 prefixEnd_7023728 := by exact prefixLift 7023728
  have htrace : WordTrace (prefixWord ++ tailWord_7023728) baseStart_7023728 baseEnd_7023728 := by
    simpa [prefixWord, tailWord_7023728, baseEnd_7023728] using wordTrace_append hprefix tailTrace_7023728
  have hstable : (prefixWord ++ tailWord_7023728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023728).length < 2 ^ (prefixWord ++ tailWord_7023728).sum := by decide
  have hdescent : baseEnd_7023728 < baseStart_7023728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023744 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 4]
def baseStart_7023744 : Nat := 118140960795 + 7023744 * 2 ^ 59
def prefixEnd_7023744 : Nat := 4983230072969 + 3 ^ 40 * 7023744 * 2
def baseEnd_7023744 : Nat := 3606556666133072802998395

theorem tailTrace_7023744 : CollatzResearch.WordTrace tailWord_7023744 prefixEnd_7023744 3606556666133072802998395 := by
  unfold tailWord_7023744
  simp only [CollatzResearch.WordTrace]
  refine ⟨128088494733091261409231143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170784659644121681878974857 128088494733091261409231143)
  ·
    refine ⟨192132742099636892113846715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128088494733091261409231143 192132742099636892113846715)
    ·
      refine ⟨288199113149455338170770073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192132742099636892113846715 288199113149455338170770073)
      ·
        refine ⟨216149334862091503628077555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288199113149455338170770073 216149334862091503628077555)
        ·
          refine ⟨324224002293137255442116333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216149334862091503628077555 324224002293137255442116333)
          ·
            refine ⟨121584000859926470790793625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324224002293137255442116333 121584000859926470790793625)
            ·
              refine ⟨91188000644944853093095219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121584000859926470790793625 91188000644944853093095219)
              ·
                refine ⟨136782000967417279639642829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91188000644944853093095219 136782000967417279639642829)
                ·
                  refine ⟨51293250362781479864866061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136782000967417279639642829 51293250362781479864866061)
                  ·
                    refine ⟨19234968886043054949324773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51293250362781479864866061 19234968886043054949324773)
                    ·
                      refine ⟨3606556666133072802998395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19234968886043054949324773 3606556666133072802998395)
                      ·
                        rfl

theorem cell23_7023744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_7023744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023744 prefixEnd_7023744 := by exact prefixLift 7023744
  have htrace : WordTrace (prefixWord ++ tailWord_7023744) baseStart_7023744 baseEnd_7023744 := by
    simpa [prefixWord, tailWord_7023744, baseEnd_7023744] using wordTrace_append hprefix tailTrace_7023744
  have hstable : (prefixWord ++ tailWord_7023744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023744).length < 2 ^ (prefixWord ++ tailWord_7023744).sum := by decide
  have hdescent : baseEnd_7023744 < baseStart_7023744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023758 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_7023758 : Nat := 118140960795 + 7023758 * 2 ^ 59
def prefixEnd_7023758 : Nat := 4983230072969 + 3 ^ 40 * 7023758 * 2
def baseEnd_7023758 : Nat := 1202187951620745249407777

theorem tailTrace_7023758 : CollatzResearch.WordTrace tailWord_7023758 prefixEnd_7023758 1202187951620745249407777 := by
  unfold tailWord_7023758
  simp only [CollatzResearch.WordTrace]
  refine ⟨32022187511016475401183991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170785000058754535472981285 32022187511016475401183991)
  ·
    refine ⟨48033281266524713101775987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32022187511016475401183991 48033281266524713101775987)
    ·
      refine ⟨72049921899787069652663981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48033281266524713101775987 72049921899787069652663981)
      ·
        refine ⟨27018720712420151119748993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72049921899787069652663981 27018720712420151119748993)
        ·
          refine ⟨20264040534315113339811745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27018720712420151119748993 20264040534315113339811745)
          ·
            refine ⟨15198030400736335004858809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20264040534315113339811745 15198030400736335004858809)
            ·
              refine ⟨11398522800552251253644107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15198030400736335004858809 11398522800552251253644107)
              ·
                refine ⟨17097784200828376880466161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11398522800552251253644107 17097784200828376880466161)
                ·
                  refine ⟨12823338150621282660349621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17097784200828376880466161 12823338150621282660349621)
                  ·
                    refine ⟨1202187951620745249407777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12823338150621282660349621 1202187951620745249407777)
                    ·
                      rfl

theorem cell23_7023758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_7023758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023758 prefixEnd_7023758 := by exact prefixLift 7023758
  have htrace : WordTrace (prefixWord ++ tailWord_7023758) baseStart_7023758 baseEnd_7023758 := by
    simpa [prefixWord, tailWord_7023758, baseEnd_7023758] using wordTrace_append hprefix tailTrace_7023758
  have hstable : (prefixWord ++ tailWord_7023758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023758).length < 2 ^ (prefixWord ++ tailWord_7023758).sum := by decide
  have hdescent : baseEnd_7023758 < baseStart_7023758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023801 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 6]
def baseStart_7023801 : Nat := 118140960795 + 7023801 * 2 ^ 59
def prefixEnd_7023801 : Nat := 4983230072969 + 3 ^ 40 * 7023801 * 2
def baseEnd_7023801 : Nat := 400731770503375453331737

theorem tailTrace_7023801 : CollatzResearch.WordTrace tailWord_7023801 prefixEnd_7023801 400731770503375453331737 := by
  unfold tailWord_7023801
  simp only [CollatzResearch.WordTrace]
  refine ⟨256179068426976021553287257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170786045617984014368858171 256179068426976021553287257)
  ·
    refine ⟨192134301320232016164965443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256179068426976021553287257 192134301320232016164965443)
    ·
      refine ⟨288201451980348024247448165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192134301320232016164965443 288201451980348024247448165)
      ·
        refine ⟨54037772246315254546396531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288201451980348024247448165 54037772246315254546396531)
        ·
          refine ⟨81056658369472881819594797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54037772246315254546396531 81056658369472881819594797)
          ·
            refine ⟨30396246888552330682348049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81056658369472881819594797 30396246888552330682348049)
            ·
              refine ⟨22797185166414248011761037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30396246888552330682348049 22797185166414248011761037)
              ·
                refine ⟨8548944437405343004410389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22797185166414248011761037 8548944437405343004410389)
                ·
                  refine ⟨400731770503375453331737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8548944437405343004410389 400731770503375453331737)
                  ·
                    rfl

theorem cell23_7023801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 6].length) (baseStart_7023801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023801 prefixEnd_7023801 := by exact prefixLift 7023801
  have htrace : WordTrace (prefixWord ++ tailWord_7023801) baseStart_7023801 baseEnd_7023801 := by
    simpa [prefixWord, tailWord_7023801, baseEnd_7023801] using wordTrace_append hprefix tailTrace_7023801
  have hstable : (prefixWord ++ tailWord_7023801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023801).length < 2 ^ (prefixWord ++ tailWord_7023801).sum := by decide
  have hdescent : baseEnd_7023801 < baseStart_7023801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023812 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 2, 1, 4]
def baseStart_7023812 : Nat := 118140960795 + 7023812 * 2 ^ 59
def prefixEnd_7023812 : Nat := 4983230072969 + 3 ^ 40 * 7023812 * 2
def baseEnd_7023812 : Nat := 3606591582817578536948083

theorem tailTrace_7023812 : CollatzResearch.WordTrace tailWord_7023812 prefixEnd_7023812 3606591582817578536948083 := by
  unfold tailWord_7023812
  simp only [CollatzResearch.WordTrace]
  refine ⟨128089734814968085215968845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170786313086624113621291793 128089734814968085215968845)
  ·
    refine ⟨48033650555613031955988317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128089734814968085215968845 48033650555613031955988317)
    ·
      refine ⟨18012618958354886983495619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48033650555613031955988317 18012618958354886983495619)
      ·
        refine ⟨27018928437532330475243429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18012618958354886983495619 27018928437532330475243429)
        ·
          refine ⟨5066049082037311964108143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27018928437532330475243429 5066049082037311964108143)
          ·
            refine ⟨7599073623055967946162215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066049082037311964108143 7599073623055967946162215)
            ·
              refine ⟨11398610434583951919243323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7599073623055967946162215 11398610434583951919243323)
              ·
                refine ⟨17097915651875927878864985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11398610434583951919243323 17097915651875927878864985)
                ·
                  refine ⟨12823436738906945909148739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17097915651875927878864985 12823436738906945909148739)
                  ·
                    refine ⟨19235155108360418863723109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12823436738906945909148739 19235155108360418863723109)
                    ·
                      refine ⟨3606591582817578536948083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19235155108360418863723109 3606591582817578536948083)
                      ·
                        rfl

theorem cell23_7023812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_7023812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023812 prefixEnd_7023812 := by exact prefixLift 7023812
  have htrace : WordTrace (prefixWord ++ tailWord_7023812) baseStart_7023812 baseEnd_7023812 := by
    simpa [prefixWord, tailWord_7023812, baseEnd_7023812] using wordTrace_append hprefix tailTrace_7023812
  have hstable : (prefixWord ++ tailWord_7023812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023812).length < 2 ^ (prefixWord ++ tailWord_7023812).sum := by decide
  have hdescent : baseEnd_7023812 < baseStart_7023812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023822 : List Nat := [4, 1, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_7023822 : Nat := 118140960795 + 7023822 * 2 ^ 59
def prefixEnd_7023822 : Nat := 4983230072969 + 3 ^ 40 * 7023822 * 2
def baseEnd_7023822 : Nat := 1202198905874707832607679

theorem tailTrace_7023822 : CollatzResearch.WordTrace tailWord_7023822 prefixEnd_7023822 1202198905874707832607679 := by
  unfold tailWord_7023822
  simp only [CollatzResearch.WordTrace]
  refine ⟨32022479294987492767475215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170786556239933294759867813 32022479294987492767475215)
  ·
    refine ⟨48033718942481239151212823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32022479294987492767475215 48033718942481239151212823)
    ·
      refine ⟨72050578413721858726819235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48033718942481239151212823 72050578413721858726819235)
      ·
        refine ⟨108075867620582788090228853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72050578413721858726819235 108075867620582788090228853)
        ·
          refine ⟨10132112589429636383458955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108075867620582788090228853 10132112589429636383458955)
          ·
            refine ⟨15198168884144454575188433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10132112589429636383458955 15198168884144454575188433)
            ·
              refine ⟨11398626663108340931391325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15198168884144454575188433 11398626663108340931391325)
              ·
                refine ⟨4274484998665627849271747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11398626663108340931391325 4274484998665627849271747)
                ·
                  refine ⟨6411727497998441773907621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4274484998665627849271747 6411727497998441773907621)
                  ·
                    refine ⟨1202198905874707832607679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6411727497998441773907621 1202198905874707832607679)
                    ·
                      rfl

theorem cell23_7023822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_7023822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023822 prefixEnd_7023822 := by exact prefixLift 7023822
  have htrace : WordTrace (prefixWord ++ tailWord_7023822) baseStart_7023822 baseEnd_7023822 := by
    simpa [prefixWord, tailWord_7023822, baseEnd_7023822] using wordTrace_append hprefix tailTrace_7023822
  have hstable : (prefixWord ++ tailWord_7023822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023822).length < 2 ^ (prefixWord ++ tailWord_7023822).sum := by decide
  have hdescent : baseEnd_7023822 < baseStart_7023822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023881 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 4]
def baseStart_7023881 : Nat := 118140960795 + 7023881 * 2 ^ 59
def prefixEnd_7023881 : Nat := 4983230072969 + 3 ^ 40 * 7023881 * 2
def baseEnd_7023881 : Nat := 3606627012982738766985265

theorem tailTrace_7023881 : CollatzResearch.WordTrace tailWord_7023881 prefixEnd_7023881 3606627012982738766985265 := by
  unfold tailWord_7023881
  simp only [CollatzResearch.WordTrace]
  refine ⟨256181986266686195216199497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170787990844457463477466331 256181986266686195216199497)
  ·
    refine ⟨192136489700014646412149623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256181986266686195216199497 192136489700014646412149623)
    ·
      refine ⟨288204734550021969618224435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192136489700014646412149623 288204734550021969618224435)
      ·
        refine ⟨432307101825032954427336653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288204734550021969618224435 432307101825032954427336653)
        ·
          refine ⟨162115163184387357910251245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432307101825032954427336653 162115163184387357910251245)
          ·
            refine ⟨60793186194145259216344217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162115163184387357910251245 60793186194145259216344217)
            ·
              refine ⟨45594889645608944412258163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60793186194145259216344217 45594889645608944412258163)
              ·
                refine ⟨68392334468413416618387245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45594889645608944412258163 68392334468413416618387245)
                ·
                  refine ⟨25647125425655031231895217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68392334468413416618387245 25647125425655031231895217)
                  ·
                    refine ⟨19235344069241273423921413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25647125425655031231895217 19235344069241273423921413)
                    ·
                      refine ⟨3606627012982738766985265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19235344069241273423921413 3606627012982738766985265)
                      ·
                        rfl

theorem cell23_7023881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_7023881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023881 prefixEnd_7023881 := by exact prefixLift 7023881
  have htrace : WordTrace (prefixWord ++ tailWord_7023881) baseStart_7023881 baseEnd_7023881 := by
    simpa [prefixWord, tailWord_7023881, baseEnd_7023881] using wordTrace_append hprefix tailTrace_7023881
  have hstable : (prefixWord ++ tailWord_7023881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023881).length < 2 ^ (prefixWord ++ tailWord_7023881).sum := by decide
  have hdescent : baseEnd_7023881 < baseStart_7023881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023912 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 2, 4]
def baseStart_7023912 : Nat := 118140960795 + 7023912 * 2 ^ 59
def prefixEnd_7023912 : Nat := 4983230072969 + 3 ^ 40 * 7023912 * 2
def baseEnd_7023912 : Nat := 1202214310294342715232541

theorem tailTrace_7023912 : CollatzResearch.WordTrace tailWord_7023912 prefixEnd_7023912 1202214310294342715232541 := by
  unfold tailWord_7023912
  simp only [CollatzResearch.WordTrace]
  refine ⟨128091558464786943755288995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170788744619715925007051993 128091558464786943755288995)
  ·
    refine ⟨192137337697180415632933493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128091558464786943755288995 192137337697180415632933493)
    ·
      refine ⟨18012875409110663965587515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192137337697180415632933493 18012875409110663965587515)
      ·
        refine ⟨27019313113665995948381273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18012875409110663965587515 27019313113665995948381273)
        ·
          refine ⟨20264484835249496961285955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27019313113665995948381273 20264484835249496961285955)
          ·
            refine ⟨30396727252874245441928933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20264484835249496961285955 30396727252874245441928933)
            ·
              refine ⟨5699386359913921020361675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30396727252874245441928933 5699386359913921020361675)
              ·
                refine ⟨8549079539870881530542513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699386359913921020361675 8549079539870881530542513)
                ·
                  refine ⟨6411809654903161147906885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8549079539870881530542513 6411809654903161147906885)
                  ·
                    refine ⟨1202214310294342715232541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6411809654903161147906885 1202214310294342715232541)
                    ·
                      rfl

theorem cell23_7023912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_7023912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023912 prefixEnd_7023912 := by exact prefixLift 7023912
  have htrace : WordTrace (prefixWord ++ tailWord_7023912) baseStart_7023912 baseEnd_7023912 := by
    simpa [prefixWord, tailWord_7023912, baseEnd_7023912] using wordTrace_append hprefix tailTrace_7023912
  have hstable : (prefixWord ++ tailWord_7023912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023912).length < 2 ^ (prefixWord ++ tailWord_7023912).sum := by decide
  have hdescent : baseEnd_7023912 < baseStart_7023912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023922 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_7023922 : Nat := 118140960795 + 7023922 * 2 ^ 59
def prefixEnd_7023922 : Nat := 4983230072969 + 3 ^ 40 * 7023922 * 2
def baseEnd_7023922 : Nat := 3606648065689573106572577

theorem tailTrace_7023922 : CollatzResearch.WordTrace tailWord_7023922 prefixEnd_7023922 3606648065689573106572577 := by
  unfold tailWord_7023922
  simp only [CollatzResearch.WordTrace]
  refine ⟨64045870414884414804610505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170788987773025106145628013 64045870414884414804610505)
  ·
    refine ⟨48034402811163311103457879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64045870414884414804610505 48034402811163311103457879)
    ·
      refine ⟨72051604216744966655186819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48034402811163311103457879 72051604216744966655186819)
      ·
        refine ⟨108077406325117449982780229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72051604216744966655186819 108077406325117449982780229)
        ·
          refine ⟨20264513685959521871771293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108077406325117449982780229 20264513685959521871771293)
          ·
            refine ⟨7599192632234820701914235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20264513685959521871771293 7599192632234820701914235)
            ·
              refine ⟨11398788948352231052871353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7599192632234820701914235 11398788948352231052871353)
              ·
                refine ⟨8549091711264173289653515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11398788948352231052871353 8549091711264173289653515)
                ·
                  refine ⟨12823637566896259934480273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8549091711264173289653515 12823637566896259934480273)
                  ·
                    refine ⟨9617728175172194950860205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12823637566896259934480273 9617728175172194950860205)
                    ·
                      refine ⟨3606648065689573106572577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9617728175172194950860205 3606648065689573106572577)
                      ·
                        rfl

theorem cell23_7023922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_7023922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023922 prefixEnd_7023922 := by exact prefixLift 7023922
  have htrace : WordTrace (prefixWord ++ tailWord_7023922) baseStart_7023922 baseEnd_7023922 := by
    simpa [prefixWord, tailWord_7023922, baseEnd_7023922] using wordTrace_append hprefix tailTrace_7023922
  have hstable : (prefixWord ++ tailWord_7023922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023922).length < 2 ^ (prefixWord ++ tailWord_7023922).sum := by decide
  have hdescent : baseEnd_7023922 < baseStart_7023922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023941 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_7023941 : Nat := 118140960795 + 7023941 * 2 ^ 59
def prefixEnd_7023941 : Nat := 4983230072969 + 3 ^ 40 * 7023941 * 2
def baseEnd_7023941 : Nat := 3606657821822008532234989

theorem tailTrace_7023941 : CollatzResearch.WordTrace tailWord_7023941 prefixEnd_7023941 3606657821822008532234989 := by
  unfold tailWord_7023941
  simp only [CollatzResearch.WordTrace]
  refine ⟨256184174646468825463383677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170789449764312550308922451 256184174646468825463383677)
  ·
    refine ⟨96069065492425809548768879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256184174646468825463383677 96069065492425809548768879)
    ·
      refine ⟨144103598238638714323153319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96069065492425809548768879 144103598238638714323153319)
      ·
        refine ⟨216155397357958071484729979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144103598238638714323153319 216155397357958071484729979)
        ·
          refine ⟨324233096036937107227094969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216155397357958071484729979 324233096036937107227094969)
          ·
            refine ⟨243174822027702830420321227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324233096036937107227094969 243174822027702830420321227)
            ·
              refine ⟨364762233041554245630481841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243174822027702830420321227 364762233041554245630481841)
              ·
                refine ⟨273571674781165684222861381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364762233041554245630481841 273571674781165684222861381)
                ·
                  refine ⟨51294689021468565791786509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273571674781165684222861381 51294689021468565791786509)
                  ·
                    refine ⟨19235508383050712171919941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51294689021468565791786509 19235508383050712171919941)
                    ·
                      refine ⟨3606657821822008532234989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19235508383050712171919941 3606657821822008532234989)
                      ·
                        rfl

theorem cell23_7023941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_7023941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023941 prefixEnd_7023941 := by exact prefixLift 7023941
  have htrace : WordTrace (prefixWord ++ tailWord_7023941) baseStart_7023941 baseEnd_7023941 := by
    simpa [prefixWord, tailWord_7023941, baseEnd_7023941] using wordTrace_append hprefix tailTrace_7023941
  have hstable : (prefixWord ++ tailWord_7023941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023941).length < 2 ^ (prefixWord ++ tailWord_7023941).sum := by decide
  have hdescent : baseEnd_7023941 < baseStart_7023941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023942 : List Nat := [6, 1, 1, 3, 2, 10]
def baseStart_7023942 : Nat := 118140960795 + 7023942 * 2 ^ 59
def prefixEnd_7023942 : Nat := 4983230072969 + 3 ^ 40 * 7023942 * 2
def baseEnd_7023942 : Nat := 14842215371615897235895

theorem tailTrace_7023942 : CollatzResearch.WordTrace tailWord_7023942 prefixEnd_7023942 14842215371615897235895 := by
  unfold tailWord_7023942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8005756597483287582317815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170789474079643468422780053 8005756597483287582317815)
  ·
    refine ⟨12008634896224931373476723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8005756597483287582317815 12008634896224931373476723)
    ·
      refine ⟨18012952344337397060215085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12008634896224931373476723 18012952344337397060215085)
      ·
        refine ⟨6754857129126523897580657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18012952344337397060215085 6754857129126523897580657)
        ·
          refine ⟨5066142846844892923185493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6754857129126523897580657 5066142846844892923185493)
          ·
            refine ⟨14842215371615897235895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5066142846844892923185493 14842215371615897235895)
            ·
              rfl

theorem cell23_7023942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 10].length) (baseStart_7023942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023942 prefixEnd_7023942 := by exact prefixLift 7023942
  have htrace : WordTrace (prefixWord ++ tailWord_7023942) baseStart_7023942 baseEnd_7023942 := by
    simpa [prefixWord, tailWord_7023942, baseEnd_7023942] using wordTrace_append hprefix tailTrace_7023942
  have hstable : (prefixWord ++ tailWord_7023942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023942).length < 2 ^ (prefixWord ++ tailWord_7023942).sum := by decide
  have hdescent : baseEnd_7023942 < baseStart_7023942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023945 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 1, 3, 2]
def baseStart_7023945 : Nat := 118140960795 + 7023945 * 2 ^ 59
def prefixEnd_7023945 : Nat := 4983230072969 + 3 ^ 40 * 7023945 * 2
def baseEnd_7023945 : Nat := 3606659875744626516584971

theorem tailTrace_7023945 : CollatzResearch.WordTrace tailWord_7023945 prefixEnd_7023945 3606659875744626516584971 := by
  unfold tailWord_7023945
  simp only [CollatzResearch.WordTrace]
  refine ⟨256184320538454334146529289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170789547025636222764352859 256184320538454334146529289)
  ·
    refine ⟨192138240403840750609896967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256184320538454334146529289 192138240403840750609896967)
    ·
      refine ⟨288207360605761125914845451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192138240403840750609896967 288207360605761125914845451)
      ·
        refine ⟨432311040908641688872268177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288207360605761125914845451 432311040908641688872268177)
        ·
          refine ⟨324233280681481266654201133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432311040908641688872268177 324233280681481266654201133)
          ·
            refine ⟨121587480255555474995325425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324233280681481266654201133 121587480255555474995325425)
            ·
              refine ⟨91190610191666606246494069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121587480255555474995325425 91190610191666606246494069)
              ·
                refine ⟨8549119705468744335608819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91190610191666606246494069 8549119705468744335608819)
                ·
                  refine ⟨12823679558203116503413229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8549119705468744335608819 12823679558203116503413229)
                  ·
                    refine ⟨4808879834326168688779961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12823679558203116503413229 4808879834326168688779961)
                    ·
                      refine ⟨3606659875744626516584971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4808879834326168688779961 3606659875744626516584971)
                      ·
                        rfl

theorem cell23_7023945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 3, 2].length) (baseStart_7023945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023945 prefixEnd_7023945 := by exact prefixLift 7023945
  have htrace : WordTrace (prefixWord ++ tailWord_7023945) baseStart_7023945 baseEnd_7023945 := by
    simpa [prefixWord, tailWord_7023945, baseEnd_7023945] using wordTrace_append hprefix tailTrace_7023945
  have hstable : (prefixWord ++ tailWord_7023945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023945).length < 2 ^ (prefixWord ++ tailWord_7023945).sum := by decide
  have hdescent : baseEnd_7023945 < baseStart_7023945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023961 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_7023961 : Nat := 118140960795 + 7023961 * 2 ^ 59
def prefixEnd_7023961 : Nat := 4983230072969 + 3 ^ 40 * 7023961 * 2
def baseEnd_7023961 : Nat := 3606668091435098453984897

theorem tailTrace_7023961 : CollatzResearch.WordTrace tailWord_7023961 prefixEnd_7023961 3606668091435098453984897 := by
  unfold tailWord_7023961
  simp only [CollatzResearch.WordTrace]
  refine ⟨256184904106396368879111737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170789936070930912586074491 256184904106396368879111737)
  ·
    refine ⟨192138678079797276659333803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256184904106396368879111737 192138678079797276659333803)
    ·
      refine ⟨288208017119695914989000705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192138678079797276659333803 288208017119695914989000705)
      ·
        refine ⟨216156012839771936241750529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288208017119695914989000705 216156012839771936241750529)
        ·
          refine ⟨162117009629828952181312897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216156012839771936241750529 162117009629828952181312897)
          ·
            refine ⟨121587757222371714135984673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162117009629828952181312897 121587757222371714135984673)
            ·
              refine ⟨91190817916778785601988505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121587757222371714135984673 91190817916778785601988505)
              ·
                refine ⟨68393113437584089201491379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91190817916778785601988505 68393113437584089201491379)
                ·
                  refine ⟨102589670156376133802237069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68393113437584089201491379 102589670156376133802237069)
                  ·
                    refine ⟨38471126308641050175838901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102589670156376133802237069 38471126308641050175838901)
                    ·
                      refine ⟨3606668091435098453984897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38471126308641050175838901 3606668091435098453984897)
                      ·
                        rfl

theorem cell23_7023961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_7023961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023961 prefixEnd_7023961 := by exact prefixLift 7023961
  have htrace : WordTrace (prefixWord ++ tailWord_7023961) baseStart_7023961 baseEnd_7023961 := by
    simpa [prefixWord, tailWord_7023961, baseEnd_7023961] using wordTrace_append hprefix tailTrace_7023961
  have hstable : (prefixWord ++ tailWord_7023961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023961).length < 2 ^ (prefixWord ++ tailWord_7023961).sum := by decide
  have hdescent : baseEnd_7023961 < baseStart_7023961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7023968 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 2, 6]
def baseStart_7023968 : Nat := 118140960795 + 7023968 * 2 ^ 59
def prefixEnd_7023968 : Nat := 4983230072969 + 3 ^ 40 * 7023968 * 2
def baseEnd_7023968 : Nat := 1202223895266559975532455

theorem tailTrace_7023968 : CollatzResearch.WordTrace tailWord_7023968 prefixEnd_7023968 1202223895266559975532455 := by
  unfold tailWord_7023968
  simp only [CollatzResearch.WordTrace]
  refine ⟨128092579708685504537308279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170790106278247339383077705 128092579708685504537308279)
  ·
    refine ⟨192138869563028256805962419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128092579708685504537308279 192138869563028256805962419)
    ·
      refine ⟨288208304344542385208943629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192138869563028256805962419 288208304344542385208943629)
      ·
        refine ⟨108078114129203394453353861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288208304344542385208943629 108078114129203394453353861)
        ·
          refine ⟨20264646399225636460003849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108078114129203394453353861 20264646399225636460003849)
          ·
            refine ⟨15198484799419227345002887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20264646399225636460003849 15198484799419227345002887)
            ·
              refine ⟨22797727199128841017504331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15198484799419227345002887 22797727199128841017504331)
              ·
                refine ⟨34196590798693261526256497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22797727199128841017504331 34196590798693261526256497)
                ·
                  refine ⟨25647443099019946144692373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34196590798693261526256497 25647443099019946144692373)
                  ·
                    refine ⟨1202223895266559975532455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25647443099019946144692373 1202223895266559975532455)
                    ·
                      rfl

theorem cell23_7023968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 6].length) (baseStart_7023968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7023968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7023968 prefixEnd_7023968 := by exact prefixLift 7023968
  have htrace : WordTrace (prefixWord ++ tailWord_7023968) baseStart_7023968 baseEnd_7023968 := by
    simpa [prefixWord, tailWord_7023968, baseEnd_7023968] using wordTrace_append hprefix tailTrace_7023968
  have hstable : (prefixWord ++ tailWord_7023968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7023968).length < 2 ^ (prefixWord ++ tailWord_7023968).sum := by decide
  have hdescent : baseEnd_7023968 < baseStart_7023968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7023968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024045 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7024045 : Nat := 118140960795 + 7024045 * 2 ^ 59
def prefixEnd_7024045 : Nat := 4983230072969 + 3 ^ 40 * 7024045 * 2
def baseEnd_7024045 : Nat := 1202237074603358708444837

theorem tailTrace_7024045 : CollatzResearch.WordTrace tailWord_7024045 prefixEnd_7024045 1202237074603358708444837 := by
  unfold tailWord_7024045
  simp only [CollatzResearch.WordTrace]
  refine ⟨256187967838092051225169589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170791978558728034150113059 256187967838092051225169589)
  ·
    refine ⟨24017621984821129802359649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256187967838092051225169589 24017621984821129802359649)
    ·
      refine ⟨18013216488615847351769737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24017621984821129802359649 18013216488615847351769737)
      ·
        refine ⟨13509912366461885513827303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18013216488615847351769737 13509912366461885513827303)
        ·
          refine ⟨20264868549692828270740955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13509912366461885513827303 20264868549692828270740955)
          ·
            refine ⟨30397302824539242406111433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20264868549692828270740955 30397302824539242406111433)
            ·
              refine ⟨22797977118404431804583575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30397302824539242406111433 22797977118404431804583575)
              ·
                refine ⟨34196965677606647706875363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22797977118404431804583575 34196965677606647706875363)
                ·
                  refine ⟨51295448516409971560313045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34196965677606647706875363 51295448516409971560313045)
                  ·
                    refine ⟨1202237074603358708444837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51295448516409971560313045 1202237074603358708444837)
                    ·
                      rfl

theorem cell23_7024045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7024045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024045 prefixEnd_7024045 := by exact prefixLift 7024045
  have htrace : WordTrace (prefixWord ++ tailWord_7024045) baseStart_7024045 baseEnd_7024045 := by
    simpa [prefixWord, tailWord_7024045, baseEnd_7024045] using wordTrace_append hprefix tailTrace_7024045
  have hstable : (prefixWord ++ tailWord_7024045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024045).length < 2 ^ (prefixWord ++ tailWord_7024045).sum := by decide
  have hdescent : baseEnd_7024045 < baseStart_7024045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024075 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 3, 4]
def baseStart_7024075 : Nat := 118140960795 + 7024075 * 2 ^ 59
def prefixEnd_7024075 : Nat := 4983230072969 + 3 ^ 40 * 7024075 * 2
def baseEnd_7024075 : Nat := 1202242209409903669319791

theorem tailTrace_7024075 : CollatzResearch.WordTrace tailWord_7024075 prefixEnd_7024075 1202242209409903669319791 := by
  unfold tailWord_7024075
  simp only [CollatzResearch.WordTrace]
  refine ⟨256189062027983366348761679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170792708018655577565841119 256189062027983366348761679)
  ·
    refine ⟨384283593041975049523142519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256189062027983366348761679 384283593041975049523142519)
    ·
      refine ⟨576425389562962574284713779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384283593041975049523142519 576425389562962574284713779)
      ·
        refine ⟨864638084344443861427070669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576425389562962574284713779 864638084344443861427070669)
        ·
          refine ⟨324239281629166448035151501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 864638084344443861427070669 324239281629166448035151501)
          ·
            refine ⟨121589730610937418013181813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324239281629166448035151501 121589730610937418013181813)
            ·
              refine ⟨11399037244775382938735795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121589730610937418013181813 11399037244775382938735795)
              ·
                refine ⟨17098555867163074408103693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11399037244775382938735795 17098555867163074408103693)
                ·
                  refine ⟨6411958450186152903038885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17098555867163074408103693 6411958450186152903038885)
                  ·
                    refine ⟨1202242209409903669319791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6411958450186152903038885 1202242209409903669319791)
                    ·
                      rfl

theorem cell23_7024075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 4].length) (baseStart_7024075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024075 prefixEnd_7024075 := by exact prefixLift 7024075
  have htrace : WordTrace (prefixWord ++ tailWord_7024075) baseStart_7024075 baseEnd_7024075 := by
    simpa [prefixWord, tailWord_7024075, baseEnd_7024075] using wordTrace_append hprefix tailTrace_7024075
  have hstable : (prefixWord ++ tailWord_7024075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024075).length < 2 ^ (prefixWord ++ tailWord_7024075).sum := by decide
  have hdescent : baseEnd_7024075 < baseStart_7024075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024078 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_7024078 : Nat := 118140960795 + 7024078 * 2 ^ 59
def prefixEnd_7024078 : Nat := 4983230072969 + 3 ^ 40 * 7024078 * 2
def baseEnd_7024078 : Nat := 3606728168671674496221859

theorem tailTrace_7024078 : CollatzResearch.WordTrace tailWord_7024078 prefixEnd_7024078 3606728168671674496221859 := by
  unfold tailWord_7024078
  simp only [CollatzResearch.WordTrace]
  refine ⟨32023646430871562232640111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170792780964648331907413925 32023646430871562232640111)
  ·
    refine ⟨48035469646307343348960167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32023646430871562232640111 48035469646307343348960167)
    ·
      refine ⟨72053204469461015023440251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48035469646307343348960167 72053204469461015023440251)
      ·
        refine ⟨108079806704191522535160377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72053204469461015023440251 108079806704191522535160377)
        ·
          refine ⟨81059855028143641901370283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108079806704191522535160377 81059855028143641901370283)
          ·
            refine ⟨121589782542215462852055425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81059855028143641901370283 121589782542215462852055425)
            ·
              refine ⟨91192336906661597139041569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121589782542215462852055425 91192336906661597139041569)
              ·
                refine ⟨68394252679996197854281177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91192336906661597139041569 68394252679996197854281177)
                ·
                  refine ⟨51295689509997148390710883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68394252679996197854281177 51295689509997148390710883)
                  ·
                    refine ⟨76943534264995722586066325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51295689509997148390710883 76943534264995722586066325)
                    ·
                      refine ⟨3606728168671674496221859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76943534264995722586066325 3606728168671674496221859)
                      ·
                        rfl

theorem cell23_7024078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_7024078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024078 prefixEnd_7024078 := by exact prefixLift 7024078
  have htrace : WordTrace (prefixWord ++ tailWord_7024078) baseStart_7024078 baseEnd_7024078 := by
    simpa [prefixWord, tailWord_7024078, baseEnd_7024078] using wordTrace_append hprefix tailTrace_7024078
  have hstable : (prefixWord ++ tailWord_7024078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024078).length < 2 ^ (prefixWord ++ tailWord_7024078).sum := by decide
  have hdescent : baseEnd_7024078 < baseStart_7024078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024085 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_7024085 : Nat := 118140960795 + 7024085 * 2 ^ 59
def prefixEnd_7024085 : Nat := 4983230072969 + 3 ^ 40 * 7024085 * 2
def baseEnd_7024085 : Nat := 3606731763036255968834327

theorem tailTrace_7024085 : CollatzResearch.WordTrace tailWord_7024085 prefixEnd_7024085 3606731763036255968834327 := by
  unfold tailWord_7024085
  simp only [CollatzResearch.WordTrace]
  refine ⟨256189426757947138056625709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170792951171964758704417139 256189426757947138056625709)
  ·
    refine ⟨96071035034230176771234641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256189426757947138056625709 96071035034230176771234641)
    ·
      refine ⟨72053276275672632578425981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96071035034230176771234641 72053276275672632578425981)
      ·
        refine ⟨27019978603377237216909743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72053276275672632578425981 27019978603377237216909743)
        ·
          refine ⟨40529967905065855825364615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27019978603377237216909743 40529967905065855825364615)
          ·
            refine ⟨60794951857598783738046923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40529967905065855825364615 60794951857598783738046923)
            ·
              refine ⟨91192427786398175607070385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60794951857598783738046923 91192427786398175607070385)
              ·
                refine ⟨68394320839798631705302789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91192427786398175607070385 68394320839798631705302789)
                ·
                  refine ⟨12823935157462243444744273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68394320839798631705302789 12823935157462243444744273)
                  ·
                    refine ⟨9617951368096682583558205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12823935157462243444744273 9617951368096682583558205)
                    ·
                      refine ⟨3606731763036255968834327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9617951368096682583558205 3606731763036255968834327)
                      ·
                        rfl

theorem cell23_7024085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_7024085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024085 prefixEnd_7024085 := by exact prefixLift 7024085
  have htrace : WordTrace (prefixWord ++ tailWord_7024085) baseStart_7024085 baseEnd_7024085 := by
    simpa [prefixWord, tailWord_7024085, baseEnd_7024085] using wordTrace_append hprefix tailTrace_7024085
  have hstable : (prefixWord ++ tailWord_7024085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024085).length < 2 ^ (prefixWord ++ tailWord_7024085).sum := by decide
  have hdescent : baseEnd_7024085 < baseStart_7024085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024115 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 7, 1, 3]
def baseStart_7024115 : Nat := 118140960795 + 7024115 * 2 ^ 59
def prefixEnd_7024115 : Nat := 4983230072969 + 3 ^ 40 * 7024115 * 2
def baseEnd_7024115 : Nat := 3606747167455890851459189

theorem tailTrace_7024115 : CollatzResearch.WordTrace tailWord_7024115 prefixEnd_7024115 3606747167455890851459189 := by
  unfold tailWord_7024115
  simp only [CollatzResearch.WordTrace]
  refine ⟨256190520947838453180217799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170793680631892302120145199 256190520947838453180217799)
  ·
    refine ⟨384285781421757679770326699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256190520947838453180217799 384285781421757679770326699)
    ·
      refine ⟨576428672132636519655490049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384285781421757679770326699 576428672132636519655490049)
      ·
        refine ⟨432321504099477389741617537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576428672132636519655490049 432321504099477389741617537)
        ·
          refine ⟨324241128074608042306213153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432321504099477389741617537 324241128074608042306213153)
          ·
            refine ⟨243180846055956031729659865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324241128074608042306213153 243180846055956031729659865)
            ·
              refine ⟨182385634541967023797244899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243180846055956031729659865 182385634541967023797244899)
              ·
                refine ⟨273578451812950535695867349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182385634541967023797244899 273578451812950535695867349)
                ·
                  refine ⟨6411994964366028180371891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 273578451812950535695867349 6411994964366028180371891)
                  ·
                    refine ⟨9617992446549042270557837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6411994964366028180371891 9617992446549042270557837)
                    ·
                      refine ⟨3606747167455890851459189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9617992446549042270557837 3606747167455890851459189)
                      ·
                        rfl

theorem cell23_7024115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 7, 1, 3].length) (baseStart_7024115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024115 prefixEnd_7024115 := by exact prefixLift 7024115
  have htrace : WordTrace (prefixWord ++ tailWord_7024115) baseStart_7024115 baseEnd_7024115 := by
    simpa [prefixWord, tailWord_7024115, baseEnd_7024115] using wordTrace_append hprefix tailTrace_7024115
  have hstable : (prefixWord ++ tailWord_7024115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024115).length < 2 ^ (prefixWord ++ tailWord_7024115).sum := by decide
  have hdescent : baseEnd_7024115 < baseStart_7024115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024135 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 3, 5]
def baseStart_7024135 : Nat := 118140960795 + 7024135 * 2 ^ 59
def prefixEnd_7024135 : Nat := 4983230072969 + 3 ^ 40 * 7024135 * 2
def baseEnd_7024135 : Nat := 1202252479022993591069699

theorem tailTrace_7024135 : CollatzResearch.WordTrace tailWord_7024135 prefixEnd_7024135 1202252479022993591069699 := by
  unfold tailWord_7024135
  simp only [CollatzResearch.WordTrace]
  refine ⟨256191250407765996595945859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170794166938510664397297239 256191250407765996595945859)
  ·
    refine ⟨384286875611648994893918789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256191250407765996595945859 384286875611648994893918789)
    ·
      refine ⟨72053789177184186542609773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384286875611648994893918789 72053789177184186542609773)
      ·
        refine ⟨27020170941444069953478665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72053789177184186542609773 27020170941444069953478665)
        ·
          refine ⟨20265128206083052465108999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27020170941444069953478665 20265128206083052465108999)
          ·
            refine ⟨30397692309124578697663499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20265128206083052465108999 30397692309124578697663499)
            ·
              refine ⟨45596538463686868046495249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30397692309124578697663499 45596538463686868046495249)
              ·
                refine ⟨34197403847765151034871437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45596538463686868046495249 34197403847765151034871437)
                ·
                  refine ⟨12824026442911931638076789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34197403847765151034871437 12824026442911931638076789)
                  ·
                    refine ⟨1202252479022993591069699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12824026442911931638076789 1202252479022993591069699)
                    ·
                      rfl

theorem cell23_7024135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_7024135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024135 prefixEnd_7024135 := by exact prefixLift 7024135
  have htrace : WordTrace (prefixWord ++ tailWord_7024135) baseStart_7024135 baseEnd_7024135 := by
    simpa [prefixWord, tailWord_7024135, baseEnd_7024135] using wordTrace_append hprefix tailTrace_7024135
  have hstable : (prefixWord ++ tailWord_7024135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024135).length < 2 ^ (prefixWord ++ tailWord_7024135).sum := by decide
  have hdescent : baseEnd_7024135 < baseStart_7024135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024165 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 4, 4]
def baseStart_7024165 : Nat := 118140960795 + 7024165 * 2 ^ 59
def prefixEnd_7024165 : Nat := 4983230072969 + 3 ^ 40 * 7024165 * 2
def baseEnd_7024165 : Nat := 1202257613829538551944653

theorem tailTrace_7024165 : CollatzResearch.WordTrace tailWord_7024165 prefixEnd_7024165 1202257613829538551944653 := by
  unfold tailWord_7024165
  simp only [CollatzResearch.WordTrace]
  refine ⟨256192344597657311719537949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170794896398438207813025299 256192344597657311719537949)
  ·
    refine ⟨96072129224121491894826731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256192344597657311719537949 96072129224121491894826731)
    ·
      refine ⟨144108193836182237842240097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96072129224121491894826731 144108193836182237842240097)
      ·
        refine ⟨108081145377136678381680073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144108193836182237842240097 108081145377136678381680073)
        ·
          refine ⟨81060859032852508786260055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108081145377136678381680073 81060859032852508786260055)
          ·
            refine ⟨121591288549278763179390083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81060859032852508786260055 121591288549278763179390083)
            ·
              refine ⟨182386932823918144769085125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121591288549278763179390083 182386932823918144769085125)
              ·
                refine ⟨34197549904484652144203461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182386932823918144769085125 34197549904484652144203461)
                ·
                  refine ⟨6412040607090872277038149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34197549904484652144203461 6412040607090872277038149)
                  ·
                    refine ⟨1202257613829538551944653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6412040607090872277038149 1202257613829538551944653)
                    ·
                      rfl

theorem cell23_7024165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_7024165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024165 prefixEnd_7024165 := by exact prefixLift 7024165
  have htrace : WordTrace (prefixWord ++ tailWord_7024165) baseStart_7024165 baseEnd_7024165 := by
    simpa [prefixWord, tailWord_7024165, baseEnd_7024165] using wordTrace_append hprefix tailTrace_7024165
  have hstable : (prefixWord ++ tailWord_7024165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024165).length < 2 ^ (prefixWord ++ tailWord_7024165).sum := by decide
  have hdescent : baseEnd_7024165 < baseStart_7024165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024199 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 1, 6]
def baseStart_7024199 : Nat := 118140960795 + 7024199 * 2 ^ 59
def prefixEnd_7024199 : Nat := 4983230072969 + 3 ^ 40 * 7024199 * 2
def baseEnd_7024199 : Nat := 1202263433276956174269601

theorem tailTrace_7024199 : CollatzResearch.WordTrace tailWord_7024199 prefixEnd_7024199 1202263433276956174269601 := by
  unfold tailWord_7024199
  simp only [CollatzResearch.WordTrace]
  refine ⟨256193584679534135526275651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170795723119689423684183767 256193584679534135526275651)
  ·
    refine ⟨384290377019301203289413477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256193584679534135526275651 384290377019301203289413477)
    ·
      refine ⟨72054445691118975616765027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384290377019301203289413477 72054445691118975616765027)
      ·
        refine ⟨108081668536678463425147541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72054445691118975616765027 108081668536678463425147541)
        ·
          refine ⟨5066328212656802973053791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108081668536678463425147541 5066328212656802973053791)
          ·
            refine ⟨7599492318985204459580687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066328212656802973053791 7599492318985204459580687)
            ·
              refine ⟨11399238478477806689371031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7599492318985204459580687 11399238478477806689371031)
              ·
                refine ⟨17098857717716710034056547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11399238478477806689371031 17098857717716710034056547)
                ·
                  refine ⟨25648286576575065051084821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17098857717716710034056547 25648286576575065051084821)
                  ·
                    refine ⟨1202263433276956174269601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25648286576575065051084821 1202263433276956174269601)
                    ·
                      rfl

theorem cell23_7024199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_7024199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024199 prefixEnd_7024199 := by exact prefixLift 7024199
  have htrace : WordTrace (prefixWord ++ tailWord_7024199) baseStart_7024199 baseEnd_7024199 := by
    simpa [prefixWord, tailWord_7024199, baseEnd_7024199] using wordTrace_append hprefix tailTrace_7024199
  have hstable : (prefixWord ++ tailWord_7024199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024199).length < 2 ^ (prefixWord ++ tailWord_7024199).sum := by decide
  have hdescent : baseEnd_7024199 < baseStart_7024199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024265 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 5]
def baseStart_7024265 : Nat := 118140960795 + 7024265 * 2 ^ 59
def prefixEnd_7024265 : Nat := 4983230072969 + 3 ^ 40 * 7024265 * 2
def baseEnd_7024265 : Nat := 3606824189554065264583499

theorem tailTrace_7024265 : CollatzResearch.WordTrace tailWord_7024265 prefixEnd_7024265 3606824189554065264583499 := by
  unfold tailWord_7024265
  simp only [CollatzResearch.WordTrace]
  refine ⟨256195991897295028798178249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170797327931530019198785499 256195991897295028798178249)
  ·
    refine ⟨192146993922971271598633687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256195991897295028798178249 192146993922971271598633687)
    ·
      refine ⟨288220490884456907397950531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192146993922971271598633687 288220490884456907397950531)
      ·
        refine ⟨432330736326685361096925797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288220490884456907397950531 432330736326685361096925797)
        ·
          refine ⟨81062013061253505205673587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 432330736326685361096925797 81062013061253505205673587)
          ·
            refine ⟨121593019591880257808510381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81062013061253505205673587 121593019591880257808510381)
            ·
              refine ⟨45597382346955096678191393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121593019591880257808510381 45597382346955096678191393)
              ·
                refine ⟨34198036760216322508643545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45597382346955096678191393 34198036760216322508643545)
                ·
                  refine ⟨25648527570162241881482659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34198036760216322508643545 25648527570162241881482659)
                  ·
                    refine ⟨38472791355243362822223989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25648527570162241881482659 38472791355243362822223989)
                    ·
                      refine ⟨3606824189554065264583499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38472791355243362822223989 3606824189554065264583499)
                      ·
                        rfl

theorem cell23_7024265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_7024265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024265 prefixEnd_7024265 := by exact prefixLift 7024265
  have htrace : WordTrace (prefixWord ++ tailWord_7024265) baseStart_7024265 baseEnd_7024265 := by
    simpa [prefixWord, tailWord_7024265, baseEnd_7024265] using wordTrace_append hprefix tailTrace_7024265
  have hstable : (prefixWord ++ tailWord_7024265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024265).length < 2 ^ (prefixWord ++ tailWord_7024265).sum := by decide
  have hdescent : baseEnd_7024265 < baseStart_7024265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024266 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2]
def baseStart_7024266 : Nat := 118140960795 + 7024266 * 2 ^ 59
def prefixEnd_7024266 : Nat := 4983230072969 + 3 ^ 40 * 7024266 * 2
def baseEnd_7024266 : Nat := 3606824703034719760670995

theorem tailTrace_7024266 : CollatzResearch.WordTrace tailWord_7024266 prefixEnd_7024266 3606824703034719760670995 := by
  unfold tailWord_7024266
  simp only [CollatzResearch.WordTrace]
  refine ⟨64049007092572851492241163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170797352246860937312643101 64049007092572851492241163)
  ·
    refine ⟨96073510638859277238361745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64049007092572851492241163 96073510638859277238361745)
    ·
      refine ⟨72055132979144457928771309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96073510638859277238361745 72055132979144457928771309)
      ·
        refine ⟨27020674867179171723289241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72055132979144457928771309 27020674867179171723289241)
        ·
          refine ⟨20265506150384378792466931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27020674867179171723289241 20265506150384378792466931)
          ·
            refine ⟨30398259225576568188700397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20265506150384378792466931 30398259225576568188700397)
            ·
              refine ⟨11399347209591213070762649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30398259225576568188700397 11399347209591213070762649)
              ·
                refine ⟨8549510407193409803071987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11399347209591213070762649 8549510407193409803071987)
                ·
                  refine ⟨12824265610790114704607981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8549510407193409803071987 12824265610790114704607981)
                  ·
                    refine ⟨4809099604046293014227993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12824265610790114704607981 4809099604046293014227993)
                    ·
                      refine ⟨3606824703034719760670995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809099604046293014227993 3606824703034719760670995)
                      ·
                        rfl

theorem cell23_7024266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_7024266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024266 prefixEnd_7024266 := by exact prefixLift 7024266
  have htrace : WordTrace (prefixWord ++ tailWord_7024266) baseStart_7024266 baseEnd_7024266 := by
    simpa [prefixWord, tailWord_7024266, baseEnd_7024266] using wordTrace_append hprefix tailTrace_7024266
  have hstable : (prefixWord ++ tailWord_7024266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024266).length < 2 ^ (prefixWord ++ tailWord_7024266).sum := by decide
  have hdescent : baseEnd_7024266 < baseStart_7024266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024279 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 1, 4, 2]
def baseStart_7024279 : Nat := 118140960795 + 7024279 * 2 ^ 59
def prefixEnd_7024279 : Nat := 4983230072969 + 3 ^ 40 * 7024279 * 2
def baseEnd_7024279 : Nat := 3606831378283228209808435

theorem tailTrace_7024279 : CollatzResearch.WordTrace tailWord_7024279 prefixEnd_7024279 3606831378283228209808435 := by
  unfold tailWord_7024279
  simp only [CollatzResearch.WordTrace]
  refine ⟨256196502519244309189187891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170797668346162872792791927 256196502519244309189187891)
  ·
    refine ⟨384294753778866463783781837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256196502519244309189187891 384294753778866463783781837)
    ·
      refine ⟨144110532667074923918918189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384294753778866463783781837 144110532667074923918918189)
      ·
        refine ⟨54041449750153096469594321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144110532667074923918918189 54041449750153096469594321)
        ·
          refine ⟨40531087312614822352195741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54041449750153096469594321 40531087312614822352195741)
          ·
            refine ⟨15199157742230558382073403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40531087312614822352195741 15199157742230558382073403)
            ·
              refine ⟨22798736613345837573110105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15199157742230558382073403 22798736613345837573110105)
              ·
                refine ⟨17099052460009378179832579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22798736613345837573110105 17099052460009378179832579)
                ·
                  refine ⟨25648578690014067269748869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17099052460009378179832579 25648578690014067269748869)
                  ·
                    refine ⟨4809108504377637613077913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25648578690014067269748869 4809108504377637613077913)
                    ·
                      refine ⟨3606831378283228209808435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809108504377637613077913 3606831378283228209808435)
                      ·
                        rfl

theorem cell23_7024279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_7024279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024279 prefixEnd_7024279 := by exact prefixLift 7024279
  have htrace : WordTrace (prefixWord ++ tailWord_7024279) baseStart_7024279 baseEnd_7024279 := by
    simpa [prefixWord, tailWord_7024279, baseEnd_7024279] using wordTrace_append hprefix tailTrace_7024279
  have hstable : (prefixWord ++ tailWord_7024279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024279).length < 2 ^ (prefixWord ++ tailWord_7024279).sum := by decide
  have hdescent : baseEnd_7024279 < baseStart_7024279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024309 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_7024309 : Nat := 118140960795 + 7024309 * 2 ^ 59
def prefixEnd_7024309 : Nat := 4983230072969 + 3 ^ 40 * 7024309 * 2
def baseEnd_7024309 : Nat := 3606846782702863092433297

theorem tailTrace_7024309 : CollatzResearch.WordTrace tailWord_7024309 prefixEnd_7024309 3606846782702863092433297 := by
  unfold tailWord_7024309
  simp only [CollatzResearch.WordTrace]
  refine ⟨256197596709135624312779981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170798397806090416208519987 256197596709135624312779981)
  ·
    refine ⟨96074098765925859117292493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256197596709135624312779981 96074098765925859117292493)
    ·
      refine ⟨36027787037222197168984685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96074098765925859117292493 36027787037222197168984685)
      ·
        refine ⟨13510420138958323938369257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36027787037222197168984685 13510420138958323938369257)
        ·
          refine ⟨10132815104218742953776943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13510420138958323938369257 10132815104218742953776943)
          ·
            refine ⟨15199222656328114430665415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10132815104218742953776943 15199222656328114430665415)
            ·
              refine ⟨22798833984492171645998123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15199222656328114430665415 22798833984492171645998123)
              ·
                refine ⟨34198250976738257468997185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22798833984492171645998123 34198250976738257468997185)
                ·
                  refine ⟨25648688232553693101747889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34198250976738257468997185 25648688232553693101747889)
                  ·
                    refine ⟨19236516174415269826310917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25648688232553693101747889 19236516174415269826310917)
                    ·
                      refine ⟨3606846782702863092433297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19236516174415269826310917 3606846782702863092433297)
                      ·
                        rfl

theorem cell23_7024309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_7024309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024309 prefixEnd_7024309 := by exact prefixLift 7024309
  have htrace : WordTrace (prefixWord ++ tailWord_7024309) baseStart_7024309 baseEnd_7024309 := by
    simpa [prefixWord, tailWord_7024309, baseEnd_7024309] using wordTrace_append hprefix tailTrace_7024309
  have hstable : (prefixWord ++ tailWord_7024309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024309).length < 2 ^ (prefixWord ++ tailWord_7024309).sum := by decide
  have hdescent : baseEnd_7024309 < baseStart_7024309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024315 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 4, 5]
def baseStart_7024315 : Nat := 118140960795 + 7024315 * 2 ^ 59
def prefixEnd_7024315 : Nat := 4983230072969 + 3 ^ 40 * 7024315 * 2
def baseEnd_7024315 : Nat := 1202283287862263356319423

theorem tailTrace_7024315 : CollatzResearch.WordTrace tailWord_7024315 prefixEnd_7024315 1202283287862263356319423 := by
  unfold tailWord_7024315
  simp only [CollatzResearch.WordTrace]
  refine ⟨256197815547113887337498399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170798543698075924891665599 256197815547113887337498399)
  ·
    refine ⟨384296723320670831006247599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256197815547113887337498399 384296723320670831006247599)
    ·
      refine ⟨576445084981006246509371399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384296723320670831006247599 576445084981006246509371399)
      ·
        refine ⟨864667627471509369764057099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576445084981006246509371399 864667627471509369764057099)
        ·
          refine ⟨1297001441207264054646085649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864667627471509369764057099 1297001441207264054646085649)
          ·
            refine ⟨972751080905448040984564237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297001441207264054646085649 972751080905448040984564237)
            ·
              refine ⟨364781655339543015369211589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 972751080905448040984564237 364781655339543015369211589)
              ·
                refine ⟨68396560376164315381727173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364781655339543015369211589 68396560376164315381727173)
                ·
                  refine ⟨12824355070530809134073845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68396560376164315381727173 12824355070530809134073845)
                  ·
                    refine ⟨1202283287862263356319423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12824355070530809134073845 1202283287862263356319423)
                    ·
                      rfl

theorem cell23_7024315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 5].length) (baseStart_7024315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024315 prefixEnd_7024315 := by exact prefixLift 7024315
  have htrace : WordTrace (prefixWord ++ tailWord_7024315) baseStart_7024315 baseEnd_7024315 := by
    simpa [prefixWord, tailWord_7024315, baseEnd_7024315] using wordTrace_append hprefix tailTrace_7024315
  have hstable : (prefixWord ++ tailWord_7024315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024315).length < 2 ^ (prefixWord ++ tailWord_7024315).sum := by decide
  have hdescent : baseEnd_7024315 < baseStart_7024315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024352 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 4]
def baseStart_7024352 : Nat := 118140960795 + 7024352 * 2 ^ 59
def prefixEnd_7024352 : Nat := 4983230072969 + 3 ^ 40 * 7024352 * 2
def baseEnd_7024352 : Nat := 3606868862371006424195599

theorem tailTrace_7024352 : CollatzResearch.WordTrace tailWord_7024352 prefixEnd_7024352 3606868862371006424195599 := by
  unfold tailWord_7024352
  simp only [CollatzResearch.WordTrace]
  refine ⟨128099582523989921328297655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170799443365319895104396873 128099582523989921328297655)
  ·
    refine ⟨192149373785984881992446483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128099582523989921328297655 192149373785984881992446483)
    ·
      refine ⟨288224060678977322988669725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192149373785984881992446483 288224060678977322988669725)
      ·
        refine ⟨108084022754616496120751147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288224060678977322988669725 108084022754616496120751147)
        ·
          refine ⟨162126034131924744181126721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108084022754616496120751147 162126034131924744181126721)
          ·
            refine ⟨121594525598943558135845041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162126034131924744181126721 121594525598943558135845041)
            ·
              refine ⟨91195894199207668601883781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121594525598943558135845041 91195894199207668601883781)
              ·
                refine ⟨17099230162351437862853209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91195894199207668601883781 17099230162351437862853209)
                ·
                  refine ⟨12824422621763578397139907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17099230162351437862853209 12824422621763578397139907)
                  ·
                    refine ⟨19236633932645367595709861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12824422621763578397139907 19236633932645367595709861)
                    ·
                      refine ⟨3606868862371006424195599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19236633932645367595709861 3606868862371006424195599)
                      ·
                        rfl

theorem cell23_7024352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_7024352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024352 prefixEnd_7024352 := by exact prefixLift 7024352
  have htrace : WordTrace (prefixWord ++ tailWord_7024352) baseStart_7024352 baseEnd_7024352 := by
    simpa [prefixWord, tailWord_7024352, baseEnd_7024352] using wordTrace_append hprefix tailTrace_7024352
  have hstable : (prefixWord ++ tailWord_7024352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024352).length < 2 ^ (prefixWord ++ tailWord_7024352).sum := by decide
  have hdescent : baseEnd_7024352 < baseStart_7024352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024369 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 2, 4, 2]
def baseStart_7024369 : Nat := 118140960795 + 7024369 * 2 ^ 59
def prefixEnd_7024369 : Nat := 4983230072969 + 3 ^ 40 * 7024369 * 2
def baseEnd_7024369 : Nat := 3606877591542132857683021

theorem tailTrace_7024369 : CollatzResearch.WordTrace tailWord_7024369 prefixEnd_7024369 3606877591542132857683021 := by
  unfold tailWord_7024369
  simp only [CollatzResearch.WordTrace]
  refine ⟨256199785088918254559964161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170799856725945503039976107 256199785088918254559964161)
  ·
    refine ⟨192149838816688690919973121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256199785088918254559964161 192149838816688690919973121)
    ·
      refine ⟨144112379112516518189979841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192149838816688690919973121 144112379112516518189979841)
      ·
        refine ⟨108084284334387388642484881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144112379112516518189979841 108084284334387388642484881)
        ·
          refine ⟨81063213250790541481863661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108084284334387388642484881 81063213250790541481863661)
          ·
            refine ⟨30398704969046453055698873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81063213250790541481863661 30398704969046453055698873)
            ·
              refine ⟨22799028726784839791774155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30398704969046453055698873 22799028726784839791774155)
              ·
                refine ⟨34198543090177259687661233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22799028726784839791774155 34198543090177259687661233)
                ·
                  refine ⟨25648907317632944765745925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34198543090177259687661233 25648907317632944765745925)
                  ·
                    refine ⟨4809170122056177143577361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25648907317632944765745925 4809170122056177143577361)
                    ·
                      refine ⟨3606877591542132857683021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809170122056177143577361 3606877591542132857683021)
                      ·
                        rfl

theorem cell23_7024369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_7024369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024369 prefixEnd_7024369 := by exact prefixLift 7024369
  have htrace : WordTrace (prefixWord ++ tailWord_7024369) baseStart_7024369 baseEnd_7024369 := by
    simpa [prefixWord, tailWord_7024369, baseEnd_7024369] using wordTrace_append hprefix tailTrace_7024369
  have hstable : (prefixWord ++ tailWord_7024369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024369).length < 2 ^ (prefixWord ++ tailWord_7024369).sum := by decide
  have hdescent : baseEnd_7024369 < baseStart_7024369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024396 : List Nat := [2, 2, 1, 2, 2, 1, 5, 3, 1, 4]
def baseStart_7024396 : Nat := 118140960795 + 7024396 * 2 ^ 59
def prefixEnd_7024396 : Nat := 4983230072969 + 3 ^ 40 * 7024396 * 2
def baseEnd_7024396 : Nat := 1202297151839934750681799

theorem tailTrace_7024396 : CollatzResearch.WordTrace tailWord_7024396 prefixEnd_7024396 1202297151839934750681799 := by
  unfold tailWord_7024396
  simp only [CollatzResearch.WordTrace]
  refine ⟨128100384929910219085598521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170800513239880292114131361 128100384929910219085598521)
  ·
    refine ⟨96075288697432664314198891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128100384929910219085598521 96075288697432664314198891)
    ·
      refine ⟨144112933046148996471298337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96075288697432664314198891 144112933046148996471298337)
      ·
        refine ⟨108084699784611747353473753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144112933046148996471298337 108084699784611747353473753)
        ·
          refine ⟨81063524838458810515105315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108084699784611747353473753 81063524838458810515105315)
          ·
            refine ⟨121595287257688215772657973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81063524838458810515105315 121595287257688215772657973)
            ·
              refine ⟨11399558180408270228686685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121595287257688215772657973 11399558180408270228686685)
              ·
                refine ⟨4274834317653101335757507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11399558180408270228686685 4274834317653101335757507)
                ·
                  refine ⟨6412251476479652003636261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4274834317653101335757507 6412251476479652003636261)
                  ·
                    refine ⟨1202297151839934750681799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6412251476479652003636261 1202297151839934750681799)
                    ·
                      rfl

theorem cell23_7024396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_7024396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024396 prefixEnd_7024396 := by exact prefixLift 7024396
  have htrace : WordTrace (prefixWord ++ tailWord_7024396) baseStart_7024396 baseEnd_7024396 := by
    simpa [prefixWord, tailWord_7024396, baseEnd_7024396] using wordTrace_append hprefix tailTrace_7024396
  have hstable : (prefixWord ++ tailWord_7024396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024396).length < 2 ^ (prefixWord ++ tailWord_7024396).sum := by decide
  have hdescent : baseEnd_7024396 < baseStart_7024396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024456 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 1, 5]
def baseStart_7024456 : Nat := 118140960795 + 7024456 * 2 ^ 59
def prefixEnd_7024456 : Nat := 4983230072969 + 3 ^ 40 * 7024456 * 2
def baseEnd_7024456 : Nat := 1202307421453024672431707

theorem tailTrace_7024456 : CollatzResearch.WordTrace tailWord_7024456 prefixEnd_7024456 1202307421453024672431707 := by
  unfold tailWord_7024456
  simp only [CollatzResearch.WordTrace]
  refine ⟨128101479119801534209190611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170801972159735378945587481 128101479119801534209190611)
  ·
    refine ⟨192152218679702301313785917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128101479119801534209190611 192152218679702301313785917)
    ·
      refine ⟨72057082004888362992669719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192152218679702301313785917 72057082004888362992669719)
      ·
        refine ⟨108085623007332544489004579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72057082004888362992669719 108085623007332544489004579)
        ·
          refine ⟨162128434510998816733506869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108085623007332544489004579 162128434510998816733506869)
          ·
            refine ⟨15199540735406139068766269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162128434510998816733506869 15199540735406139068766269)
            ·
              refine ⟨5699827775777302150787351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15199540735406139068766269 5699827775777302150787351)
              ·
                refine ⟨8549741663665953226181027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699827775777302150787351 8549741663665953226181027)
                ·
                  refine ⟨12824612495498929839271541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8549741663665953226181027 12824612495498929839271541)
                  ·
                    refine ⟨1202307421453024672431707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12824612495498929839271541 1202307421453024672431707)
                    ·
                      rfl

theorem cell23_7024456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_7024456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024456 prefixEnd_7024456 := by exact prefixLift 7024456
  have htrace : WordTrace (prefixWord ++ tailWord_7024456) baseStart_7024456 baseEnd_7024456 := by
    simpa [prefixWord, tailWord_7024456, baseEnd_7024456] using wordTrace_append hprefix tailTrace_7024456
  have hstable : (prefixWord ++ tailWord_7024456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024456).length < 2 ^ (prefixWord ++ tailWord_7024456).sum := by decide
  have hdescent : baseEnd_7024456 < baseStart_7024456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024479 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 3]
def baseStart_7024479 : Nat := 118140960795 + 7024479 * 2 ^ 59
def prefixEnd_7024479 : Nat := 4983230072969 + 3 ^ 40 * 7024479 * 2
def baseEnd_7024479 : Nat := 3606934074414127427307515

theorem tailTrace_7024479 : CollatzResearch.WordTrace tailWord_7024479 prefixEnd_7024479 3606934074414127427307515 := by
  unfold tailWord_7024479
  simp only [CollatzResearch.WordTrace]
  refine ⟨256203797118519743346468491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170802531412346495564312327 256203797118519743346468491)
  ·
    refine ⟨384305695677779615019702737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256203797118519743346468491 384305695677779615019702737)
    ·
      refine ⟨288229271758334711264777053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384305695677779615019702737 288229271758334711264777053)
      ·
        refine ⟨108085976909375516724291395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288229271758334711264777053 108085976909375516724291395)
        ·
          refine ⟨162128965364063275086437093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108085976909375516724291395 162128965364063275086437093)
          ·
            refine ⟨30399181005761864078706955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162128965364063275086437093 30399181005761864078706955)
            ·
              refine ⟨45598771508642796118060433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30399181005761864078706955 45598771508642796118060433)
              ·
                refine ⟨34199078631482097088545325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45598771508642796118060433 34199078631482097088545325)
                ·
                  refine ⟨12824654486805786408204497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34199078631482097088545325 12824654486805786408204497)
                  ·
                    refine ⟨9618490865104339806153373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12824654486805786408204497 9618490865104339806153373)
                    ·
                      refine ⟨3606934074414127427307515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9618490865104339806153373 3606934074414127427307515)
                      ·
                        rfl

theorem cell23_7024479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_7024479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024479 prefixEnd_7024479 := by exact prefixLift 7024479
  have htrace : WordTrace (prefixWord ++ tailWord_7024479) baseStart_7024479 baseEnd_7024479 := by
    simpa [prefixWord, tailWord_7024479, baseEnd_7024479] using wordTrace_append hprefix tailTrace_7024479
  have hstable : (prefixWord ++ tailWord_7024479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024479).length < 2 ^ (prefixWord ++ tailWord_7024479).sum := by decide
  have hdescent : baseEnd_7024479 < baseStart_7024479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024510 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_7024510 : Nat := 118140960795 + 7024510 * 2 ^ 59
def prefixEnd_7024510 : Nat := 4983230072969 + 3 ^ 40 * 7024510 * 2
def baseEnd_7024510 : Nat := 3606949992314416806019873

theorem tailTrace_7024510 : CollatzResearch.WordTrace tailWord_7024510 prefixEnd_7024510 3606949992314416806019873 := by
  unfold tailWord_7024510
  simp only [CollatzResearch.WordTrace]
  refine ⟨32025615972675929455105873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170803285187604957093897989 32025615972675929455105873)
  ·
    refine ⟨24019211979506947091329405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32025615972675929455105873 24019211979506947091329405)
    ·
      refine ⟨9007204492315105159248527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24019211979506947091329405 9007204492315105159248527)
      ·
        refine ⟨13510806738472657738872791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9007204492315105159248527 13510806738472657738872791)
        ·
          refine ⟨20266210107708986608309187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13510806738472657738872791 20266210107708986608309187)
          ·
            refine ⟨30399315161563479912463781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20266210107708986608309187 30399315161563479912463781)
            ·
              refine ⟨5699871592793152483586959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30399315161563479912463781 5699871592793152483586959)
              ·
                refine ⟨8549807389189728725380439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699871592793152483586959 8549807389189728725380439)
                ·
                  refine ⟨12824711083784593088070659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8549807389189728725380439 12824711083784593088070659)
                  ·
                    refine ⟨19237066625676889632105989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12824711083784593088070659 19237066625676889632105989)
                    ·
                      refine ⟨3606949992314416806019873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19237066625676889632105989 3606949992314416806019873)
                      ·
                        rfl

theorem cell23_7024510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_7024510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024510 prefixEnd_7024510 := by exact prefixLift 7024510
  have htrace : WordTrace (prefixWord ++ tailWord_7024510) baseStart_7024510 baseEnd_7024510 := by
    simpa [prefixWord, tailWord_7024510, baseEnd_7024510] using wordTrace_append hprefix tailTrace_7024510
  have hstable : (prefixWord ++ tailWord_7024510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024510).length < 2 ^ (prefixWord ++ tailWord_7024510).sum := by decide
  have hdescent : baseEnd_7024510 < baseStart_7024510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024520 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 2, 4]
def baseStart_7024520 : Nat := 118140960795 + 7024520 * 2 ^ 59
def prefixEnd_7024520 : Nat := 4983230072969 + 3 ^ 40 * 7024520 * 2
def baseEnd_7024520 : Nat := 1202318375706987255631609

theorem tailTrace_7024520 : CollatzResearch.WordTrace tailWord_7024520 prefixEnd_7024520 1202318375706987255631609 := by
  unfold tailWord_7024520
  simp only [CollatzResearch.WordTrace]
  refine ⟨128102646255685603674355507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170803528340914138232474009 128102646255685603674355507)
  ·
    refine ⟨192153969383528405511533261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128102646255685603674355507 192153969383528405511533261)
    ·
      refine ⟨72057738518823152066824973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192153969383528405511533261 72057738518823152066824973)
      ·
        refine ⟨27021651944558682025059365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72057738518823152066824973 27021651944558682025059365)
        ·
          refine ⟨5066559739604752879698631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27021651944558682025059365 5066559739604752879698631)
          ·
            refine ⟨7599839609407129319547947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066559739604752879698631 7599839609407129319547947)
            ·
              refine ⟨11399759414110693979321921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7599839609407129319547947 11399759414110693979321921)
              ·
                refine ⟨8549819560583020484491441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11399759414110693979321921 8549819560583020484491441)
                ·
                  refine ⟨6412364670437265363368581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8549819560583020484491441 6412364670437265363368581)
                  ·
                    refine ⟨1202318375706987255631609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6412364670437265363368581 1202318375706987255631609)
                    ·
                      rfl

theorem cell23_7024520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_7024520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024520 prefixEnd_7024520 := by exact prefixLift 7024520
  have htrace : WordTrace (prefixWord ++ tailWord_7024520) baseStart_7024520 baseEnd_7024520 := by
    simpa [prefixWord, tailWord_7024520, baseEnd_7024520] using wordTrace_append hprefix tailTrace_7024520
  have hstable : (prefixWord ++ tailWord_7024520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024520).length < 2 ^ (prefixWord ++ tailWord_7024520).sum := by decide
  have hdescent : baseEnd_7024520 < baseStart_7024520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024543 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 1, 3, 3]
def baseStart_7024543 : Nat := 118140960795 + 7024543 * 2 ^ 59
def prefixEnd_7024543 : Nat := 4983230072969 + 3 ^ 40 * 7024543 * 2
def baseEnd_7024543 : Nat := 3606966937176015176907221

theorem tailTrace_7024543 : CollatzResearch.WordTrace tailWord_7024543 prefixEnd_7024543 3606966937176015176907221 := by
  unfold tailWord_7024543
  simp only [CollatzResearch.WordTrace]
  refine ⟨256206131390287882276798283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170804087593525254851198855 256206131390287882276798283)
  ·
    refine ⟨384309197085431823415197425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256206131390287882276798283 384309197085431823415197425)
    ·
      refine ⟨288231897814073867561398069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384309197085431823415197425 288231897814073867561398069)
      ·
        refine ⟨27021740420069425083881069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 288231897814073867561398069 27021740420069425083881069)
        ·
          refine ⟨10133152657526034406455401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27021740420069425083881069 10133152657526034406455401)
          ·
            refine ⟨7599864493144525804841551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10133152657526034406455401 7599864493144525804841551)
            ·
              refine ⟨11399796739716788707262327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7599864493144525804841551 11399796739716788707262327)
              ·
                refine ⟨17099695109575183060893491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11399796739716788707262327 17099695109575183060893491)
                ·
                  refine ⟨25649542664362774591340237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17099695109575183060893491 25649542664362774591340237)
                  ·
                    refine ⟨9618578499136040471752589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25649542664362774591340237 9618578499136040471752589)
                    ·
                      refine ⟨3606966937176015176907221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9618578499136040471752589 3606966937176015176907221)
                      ·
                        rfl

theorem cell23_7024543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_7024543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024543 prefixEnd_7024543 := by exact prefixLift 7024543
  have htrace : WordTrace (prefixWord ++ tailWord_7024543) baseStart_7024543 baseEnd_7024543 := by
    simpa [prefixWord, tailWord_7024543, baseEnd_7024543] using wordTrace_append hprefix tailTrace_7024543
  have hstable : (prefixWord ++ tailWord_7024543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024543).length < 2 ^ (prefixWord ++ tailWord_7024543).sum := by decide
  have hdescent : baseEnd_7024543 < baseStart_7024543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024569 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 5]
def baseStart_7024569 : Nat := 118140960795 + 7024569 * 2 ^ 59
def prefixEnd_7024569 : Nat := 4983230072969 + 3 ^ 40 * 7024569 * 2
def baseEnd_7024569 : Nat := 3606980287673032075182101

theorem tailTrace_7024569 : CollatzResearch.WordTrace tailWord_7024569 prefixEnd_7024569 3606980287673032075182101 := by
  unfold tailWord_7024569
  simp only [CollatzResearch.WordTrace]
  refine ⟨256207079688193688717244761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170804719792129125811496507 256207079688193688717244761)
  ·
    refine ⟨192155309766145266537933571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256207079688193688717244761 192155309766145266537933571)
    ·
      refine ⟨288232964649217899806900357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192155309766145266537933571 288232964649217899806900357)
      ·
        refine ⟨54043680871728356213793817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288232964649217899806900357 54043680871728356213793817)
        ·
          refine ⟨40532760653796267160345363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54043680871728356213793817 40532760653796267160345363)
          ·
            refine ⟨60799140980694400740518045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40532760653796267160345363 60799140980694400740518045)
            ·
              refine ⟨22799677867760400277694267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60799140980694400740518045 22799677867760400277694267)
              ·
                refine ⟨34199516801640600416541401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22799677867760400277694267 34199516801640600416541401)
                ·
                  refine ⟨25649637601230450312406051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34199516801640600416541401 25649637601230450312406051)
                  ·
                    refine ⟨38474456401845675468609077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25649637601230450312406051 38474456401845675468609077)
                    ·
                      refine ⟨3606980287673032075182101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38474456401845675468609077 3606980287673032075182101)
                      ·
                        rfl

theorem cell23_7024569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_7024569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024569 prefixEnd_7024569 := by exact prefixLift 7024569
  have htrace : WordTrace (prefixWord ++ tailWord_7024569) baseStart_7024569 baseEnd_7024569 := by
    simpa [prefixWord, tailWord_7024569, baseEnd_7024569] using wordTrace_append hprefix tailTrace_7024569
  have hstable : (prefixWord ++ tailWord_7024569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024569).length < 2 ^ (prefixWord ++ tailWord_7024569).sum := by decide
  have hdescent : baseEnd_7024569 < baseStart_7024569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024583 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 2, 2, 2]
def baseStart_7024583 : Nat := 118140960795 + 7024583 * 2 ^ 59
def prefixEnd_7024583 : Nat := 4983230072969 + 3 ^ 40 * 7024583 * 2
def baseEnd_7024583 : Nat := 3606987476402195020407037

theorem tailTrace_7024583 : CollatzResearch.WordTrace tailWord_7024583 prefixEnd_7024583 3606987476402195020407037 := by
  unfold tailWord_7024583
  simp only [CollatzResearch.WordTrace]
  refine ⟨256207590310142969108254403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170805060206761979405502935 256207590310142969108254403)
  ·
    refine ⟨384311385465214453662381605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256207590310142969108254403 384311385465214453662381605)
    ·
      refine ⟨72058384774727710061696551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384311385465214453662381605 72058384774727710061696551)
      ·
        refine ⟨108087577162091565092544827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72058384774727710061696551 108087577162091565092544827)
        ·
          refine ⟨162131365743137347638817241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108087577162091565092544827 162131365743137347638817241)
          ·
            refine ⟨121598524307353010729112931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162131365743137347638817241 121598524307353010729112931)
            ·
              refine ⟨182397786461029516093669397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121598524307353010729112931 182397786461029516093669397)
              ·
                refine ⟨8549896240360758566890753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182397786461029516093669397 8549896240360758566890753)
                ·
                  refine ⟨6412422180270568925168065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8549896240360758566890753 6412422180270568925168065)
                  ·
                    refine ⟨4809316635202926693876049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6412422180270568925168065 4809316635202926693876049)
                    ·
                      refine ⟨3606987476402195020407037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809316635202926693876049 3606987476402195020407037)
                      ·
                        rfl

theorem cell23_7024583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_7024583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024583 prefixEnd_7024583 := by exact prefixLift 7024583
  have htrace : WordTrace (prefixWord ++ tailWord_7024583) baseStart_7024583 baseEnd_7024583 := by
    simpa [prefixWord, tailWord_7024583, baseEnd_7024583] using wordTrace_append hprefix tailTrace_7024583
  have hstable : (prefixWord ++ tailWord_7024583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024583).length < 2 ^ (prefixWord ++ tailWord_7024583).sum := by decide
  have hdescent : baseEnd_7024583 < baseStart_7024583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024594 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_7024594 : Nat := 118140960795 + 7024594 * 2 ^ 59
def prefixEnd_7024594 : Nat := 4983230072969 + 3 ^ 40 * 7024594 * 2
def baseEnd_7024594 : Nat := 3606993124689394477369487

theorem tailTrace_7024594 : CollatzResearch.WordTrace tailWord_7024594 prefixEnd_7024594 3606993124689394477369487 := by
  unfold tailWord_7024594
  simp only [CollatzResearch.WordTrace]
  refine ⟨64051997878275779496726209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170805327675402078657936557 64051997878275779496726209)
  ·
    refine ⟨48038998408706834622544657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64051997878275779496726209 48038998408706834622544657)
    ·
      refine ⟨36029248806530125966908493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48038998408706834622544657 36029248806530125966908493)
      ·
        refine ⟨13510968302448797237590685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36029248806530125966908493 13510968302448797237590685)
        ·
          refine ⟨5066613113418298964096507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13510968302448797237590685 5066613113418298964096507)
          ·
            refine ⟨7599919670127448446144761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066613113418298964096507 7599919670127448446144761)
            ·
              refine ⟨5699939752595586334608571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7599919670127448446144761 5699939752595586334608571)
              ·
                refine ⟨8549909628893379501912857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5699939752595586334608571 8549909628893379501912857)
                ·
                  refine ⟨6412432221670034626434643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8549909628893379501912857 6412432221670034626434643)
                  ·
                    refine ⟨9618648332505051939651965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6412432221670034626434643 9618648332505051939651965)
                    ·
                      refine ⟨3606993124689394477369487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9618648332505051939651965 3606993124689394477369487)
                      ·
                        rfl

theorem cell23_7024594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_7024594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024594 prefixEnd_7024594 := by exact prefixLift 7024594
  have htrace : WordTrace (prefixWord ++ tailWord_7024594) baseStart_7024594 baseEnd_7024594 := by
    simpa [prefixWord, tailWord_7024594, baseEnd_7024594] using wordTrace_append hprefix tailTrace_7024594
  have hstable : (prefixWord ++ tailWord_7024594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024594).length < 2 ^ (prefixWord ++ tailWord_7024594).sum := by decide
  have hdescent : baseEnd_7024594 < baseStart_7024594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024599 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 3]
def baseStart_7024599 : Nat := 118140960795 + 7024599 * 2 ^ 59
def prefixEnd_7024599 : Nat := 4983230072969 + 3 ^ 40 * 7024599 * 2
def baseEnd_7024599 : Nat := 3606995692092666957806963

theorem tailTrace_7024599 : CollatzResearch.WordTrace tailWord_7024599 prefixEnd_7024599 3606995692092666957806963 := by
  unfold tailWord_7024599
  simp only [CollatzResearch.WordTrace]
  refine ⟨256208173878085003840836851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170805449252056669227224567 256208173878085003840836851)
  ·
    refine ⟨384312260817127505761255277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256208173878085003840836851 384312260817127505761255277)
    ·
      refine ⟨144117097806422814660470729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384312260817127505761255277 144117097806422814660470729)
      ·
        refine ⟨108087823354817110995353047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144117097806422814660470729 108087823354817110995353047)
        ·
          refine ⟨162131735032225666493029571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108087823354817110995353047 162131735032225666493029571)
          ·
            refine ⟨243197602548338499739544357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162131735032225666493029571 243197602548338499739544357)
            ·
              refine ⟨45599550477813468701164567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243197602548338499739544357 45599550477813468701164567)
              ·
                refine ⟨68399325716720203051746851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45599550477813468701164567 68399325716720203051746851)
                ·
                  refine ⟨102598988575080304577620277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68399325716720203051746851 102598988575080304577620277)
                  ·
                    refine ⟨9618655178913778554151901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102598988575080304577620277 9618655178913778554151901)
                    ·
                      refine ⟨3606995692092666957806963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9618655178913778554151901 3606995692092666957806963)
                      ·
                        rfl

theorem cell23_7024599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_7024599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024599 prefixEnd_7024599 := by exact prefixLift 7024599
  have htrace : WordTrace (prefixWord ++ tailWord_7024599) baseStart_7024599 baseEnd_7024599 := by
    simpa [prefixWord, tailWord_7024599, baseEnd_7024599] using wordTrace_append hprefix tailTrace_7024599
  have hstable : (prefixWord ++ tailWord_7024599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024599).length < 2 ^ (prefixWord ++ tailWord_7024599).sum := by decide
  have hdescent : baseEnd_7024599 < baseStart_7024599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024656 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 2, 4, 2]
def baseStart_7024656 : Nat := 118140960795 + 7024656 * 2 ^ 59
def prefixEnd_7024656 : Nat := 4983230072969 + 3 ^ 40 * 7024656 * 2
def baseEnd_7024656 : Nat := 3607024960489973234794201

theorem tailTrace_7024656 : CollatzResearch.WordTrace tailWord_7024656 prefixEnd_7024656 3607024960489973234794201 := by
  unfold tailWord_7024656
  simp only [CollatzResearch.WordTrace]
  refine ⟨128105126419439251287830911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170806835225919001717107881 128105126419439251287830911)
  ·
    refine ⟨192157689629158876931746367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128105126419439251287830911 192157689629158876931746367)
    ·
      refine ⟨288236534443738315397619551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192157689629158876931746367 288236534443738315397619551)
      ·
        refine ⟨432354801665607473096429327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288236534443738315397619551 432354801665607473096429327)
        ·
          refine ⟨648532202498411209644643991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432354801665607473096429327 648532202498411209644643991)
          ·
            refine ⟨972798303747616814466965987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648532202498411209644643991 972798303747616814466965987)
            ·
              refine ⟨1459197455621425221700448981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 972798303747616814466965987 1459197455621425221700448981)
              ·
                refine ⟨34199940366127153633604273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1459197455621425221700448981 34199940366127153633604273)
                ·
                  refine ⟨25649955274595365225203205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34199940366127153633604273 25649955274595365225203205)
                  ·
                    refine ⟨4809366613986630979725601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25649955274595365225203205 4809366613986630979725601)
                    ·
                      refine ⟨3607024960489973234794201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809366613986630979725601 3607024960489973234794201)
                      ·
                        rfl

theorem cell23_7024656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 4, 2].length) (baseStart_7024656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024656 prefixEnd_7024656 := by exact prefixLift 7024656
  have htrace : WordTrace (prefixWord ++ tailWord_7024656) baseStart_7024656 baseEnd_7024656 := by
    simpa [prefixWord, tailWord_7024656, baseEnd_7024656] using wordTrace_append hprefix tailTrace_7024656
  have hstable : (prefixWord ++ tailWord_7024656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024656).length < 2 ^ (prefixWord ++ tailWord_7024656).sum := by decide
  have hdescent : baseEnd_7024656 < baseStart_7024656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024666 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 5, 4]
def baseStart_7024666 : Nat := 118140960795 + 7024666 * 2 ^ 59
def prefixEnd_7024666 : Nat := 4983230072969 + 3 ^ 40 * 7024666 * 2
def baseEnd_7024666 : Nat := 1202343365098839398556385

theorem tailTrace_7024666 : CollatzResearch.WordTrace tailWord_7024666 prefixEnd_7024666 1202343365098839398556385 := by
  unfold tailWord_7024666
  simp only [CollatzResearch.WordTrace]
  refine ⟨64052654392210568570881463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170807078379228182855683901 64052654392210568570881463)
  ·
    refine ⟨96078981588315852856322195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64052654392210568570881463 96078981588315852856322195)
    ·
      refine ⟨144118472382473779284483293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96078981588315852856322195 144118472382473779284483293)
      ·
        refine ⟨54044427143427667231681235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144118472382473779284483293 54044427143427667231681235)
        ·
          refine ⟨81066640715141500847521853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54044427143427667231681235 81066640715141500847521853)
          ·
            refine ⟨30399990268178062817820695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81066640715141500847521853 30399990268178062817820695)
            ·
              refine ⟨45599985402267094226731043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30399990268178062817820695 45599985402267094226731043)
              ·
                refine ⟨68399978103400641340096565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45599985402267094226731043 68399978103400641340096565)
                ·
                  refine ⟨6412497947193810125634053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68399978103400641340096565 6412497947193810125634053)
                  ·
                    refine ⟨1202343365098839398556385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6412497947193810125634053 1202343365098839398556385)
                    ·
                      rfl

theorem cell23_7024666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_7024666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024666 prefixEnd_7024666 := by exact prefixLift 7024666
  have htrace : WordTrace (prefixWord ++ tailWord_7024666) baseStart_7024666 baseEnd_7024666 := by
    simpa [prefixWord, tailWord_7024666, baseEnd_7024666] using wordTrace_append hprefix tailTrace_7024666
  have hstable : (prefixWord ++ tailWord_7024666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024666).length < 2 ^ (prefixWord ++ tailWord_7024666).sum := by decide
  have hdescent : baseEnd_7024666 < baseStart_7024666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024686 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_7024686 : Nat := 118140960795 + 7024686 * 2 ^ 59
def prefixEnd_7024686 : Nat := 4983230072969 + 3 ^ 40 * 7024686 * 2
def baseEnd_7024686 : Nat := 3607040364909608117419063

theorem tailTrace_7024686 : CollatzResearch.WordTrace tailWord_7024686 prefixEnd_7024686 3607040364909608117419063 := by
  unfold tailWord_7024686
  simp only [CollatzResearch.WordTrace]
  refine ⟨32026418378596227212406739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170807564685846545132835941 32026418378596227212406739)
  ·
    refine ⟨48039627567894340818610109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32026418378596227212406739 48039627567894340818610109)
    ·
      refine ⟨18014860337960377806978791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48039627567894340818610109 18014860337960377806978791)
      ·
        refine ⟨27022290506940566710468187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18014860337960377806978791 27022290506940566710468187)
        ·
          refine ⟨40533435760410850065702281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27022290506940566710468187 40533435760410850065702281)
          ·
            refine ⟨30400076820308137549276711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40533435760410850065702281 30400076820308137549276711)
            ·
              refine ⟨45600115230462206323915067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30400076820308137549276711 45600115230462206323915067)
              ·
                refine ⟨68400172845693309485872601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45600115230462206323915067 68400172845693309485872601)
                ·
                  refine ⟨51300129634269982114404451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68400172845693309485872601 51300129634269982114404451)
                  ·
                    refine ⟨76950194451404973171606677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51300129634269982114404451 76950194451404973171606677)
                    ·
                      refine ⟨3607040364909608117419063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76950194451404973171606677 3607040364909608117419063)
                      ·
                        rfl

theorem cell23_7024686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_7024686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024686 prefixEnd_7024686 := by exact prefixLift 7024686
  have htrace : WordTrace (prefixWord ++ tailWord_7024686) baseStart_7024686 baseEnd_7024686 := by
    simpa [prefixWord, tailWord_7024686, baseEnd_7024686] using wordTrace_append hprefix tailTrace_7024686
  have hstable : (prefixWord ++ tailWord_7024686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024686).length < 2 ^ (prefixWord ++ tailWord_7024686).sum := by decide
  have hdescent : baseEnd_7024686 < baseStart_7024686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024696 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 8]
def baseStart_7024696 : Nat := 118140960795 + 7024696 * 2 ^ 59
def prefixEnd_7024696 : Nat := 4983230072969 + 3 ^ 40 * 7024696 * 2
def baseEnd_7024696 : Nat := 400782833301794786477113

theorem tailTrace_7024696 : CollatzResearch.WordTrace tailWord_7024696 prefixEnd_7024696 400782833301794786477113 := by
  unfold tailWord_7024696
  simp only [CollatzResearch.WordTrace]
  refine ⟨128105855879366794703558971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170807807839155726271411961 128105855879366794703558971)
  ·
    refine ⟨192158783819050192055338457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128105855879366794703558971 192158783819050192055338457)
    ·
      refine ⟨144119087864287644041503843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192158783819050192055338457 144119087864287644041503843)
      ·
        refine ⟨216178631796431466062255765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144119087864287644041503843 216178631796431466062255765)
        ·
          refine ⟨10133373365457724971668239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 216178631796431466062255765 10133373365457724971668239)
          ·
            refine ⟨15200060048186587457502359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10133373365457724971668239 15200060048186587457502359)
            ·
              refine ⟨22800090072279881186253539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15200060048186587457502359 22800090072279881186253539)
              ·
                refine ⟨34200135108419821779380309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22800090072279881186253539 34200135108419821779380309)
                ·
                  refine ⟨400782833301794786477113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34200135108419821779380309 400782833301794786477113)
                  ·
                    rfl

theorem cell23_7024696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 8].length) (baseStart_7024696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024696 prefixEnd_7024696 := by exact prefixLift 7024696
  have htrace : WordTrace (prefixWord ++ tailWord_7024696) baseStart_7024696 baseEnd_7024696 := by
    simpa [prefixWord, tailWord_7024696, baseEnd_7024696] using wordTrace_append hprefix tailTrace_7024696
  have hstable : (prefixWord ++ tailWord_7024696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024696).length < 2 ^ (prefixWord ++ tailWord_7024696).sum := by decide
  have hdescent : baseEnd_7024696 < baseStart_7024696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024750 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_7024750 : Nat := 118140960795 + 7024750 * 2 ^ 59
def prefixEnd_7024750 : Nat := 4983230072969 + 3 ^ 40 * 7024750 * 2
def baseEnd_7024750 : Nat := 3607073227671495867018769

theorem tailTrace_7024750 : CollatzResearch.WordTrace tailWord_7024750 prefixEnd_7024750 3607073227671495867018769 := by
  unfold tailWord_7024750
  simp only [CollatzResearch.WordTrace]
  refine ⟨32026710162567244578697963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170809120867025304419722469 32026710162567244578697963)
  ·
    refine ⟨48040065243850866868046945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32026710162567244578697963 48040065243850866868046945)
    ·
      refine ⟨36030048932888150151035209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48040065243850866868046945 36030048932888150151035209)
      ·
        refine ⟨27022536699666112613276407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36030048932888150151035209 27022536699666112613276407)
        ·
          refine ⟨40533805049499168919914611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27022536699666112613276407 40533805049499168919914611)
          ·
            refine ⟨60800707574248753379871917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40533805049499168919914611 60800707574248753379871917)
            ·
              refine ⟨22800265340343282517451969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60800707574248753379871917 22800265340343282517451969)
              ·
                refine ⟨17100199005257461888088977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22800265340343282517451969 17100199005257461888088977)
                ·
                  refine ⟨12825149253943096416066733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17100199005257461888088977 12825149253943096416066733)
                  ·
                    refine ⟨4809430970228661156025025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12825149253943096416066733 4809430970228661156025025)
                    ·
                      refine ⟨3607073227671495867018769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809430970228661156025025 3607073227671495867018769)
                      ·
                        rfl

theorem cell23_7024750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_7024750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024750 prefixEnd_7024750 := by exact prefixLift 7024750
  have htrace : WordTrace (prefixWord ++ tailWord_7024750) baseStart_7024750 baseEnd_7024750 := by
    simpa [prefixWord, tailWord_7024750, baseEnd_7024750] using wordTrace_append hprefix tailTrace_7024750
  have hstable : (prefixWord ++ tailWord_7024750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024750).length < 2 ^ (prefixWord ++ tailWord_7024750).sum := by decide
  have hdescent : baseEnd_7024750 < baseStart_7024750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024786 : List Nat := [3, 2, 3, 1, 1, 1, 1, 11]
def baseStart_7024786 : Nat := 118140960795 + 7024786 * 2 ^ 59
def prefixEnd_7024786 : Nat := 4983230072969 + 3 ^ 40 * 7024786 * 2
def baseEnd_7024786 : Nat := 133595989369446582450689

theorem tailTrace_7024786 : CollatzResearch.WordTrace tailWord_7024786 prefixEnd_7024786 133595989369446582450689 := by
  unfold tailWord_7024786
  simp only [CollatzResearch.WordTrace]
  refine ⟨64053748582101883694473553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170809996218938356518596141 64053748582101883694473553)
  ·
    refine ⟨48040311436576412770855165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64053748582101883694473553 48040311436576412770855165)
    ·
      refine ⟨18015116788716154789070687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48040311436576412770855165 18015116788716154789070687)
      ·
        refine ⟨27022675183074232183606031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18015116788716154789070687 27022675183074232183606031)
        ·
          refine ⟨40534012774611348275409047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27022675183074232183606031 40534012774611348275409047)
          ·
            refine ⟨60801019161917022413113571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40534012774611348275409047 60801019161917022413113571)
            ·
              refine ⟨91201528742875533619670357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60801019161917022413113571 91201528742875533619670357)
              ·
                refine ⟨133595989369446582450689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 91201528742875533619670357 133595989369446582450689)
                ·
                  rfl

theorem cell23_7024786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 11].length) (baseStart_7024786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024786 prefixEnd_7024786 := by exact prefixLift 7024786
  have htrace : WordTrace (prefixWord ++ tailWord_7024786) baseStart_7024786 baseEnd_7024786 := by
    simpa [prefixWord, tailWord_7024786, baseEnd_7024786] using wordTrace_append hprefix tailTrace_7024786
  have hstable : (prefixWord ++ tailWord_7024786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024786).length < 2 ^ (prefixWord ++ tailWord_7024786).sum := by decide
  have hdescent : baseEnd_7024786 < baseStart_7024786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024807 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 2, 4]
def baseStart_7024807 : Nat := 118140960795 + 7024807 * 2 ^ 59
def prefixEnd_7024807 : Nat := 4983230072969 + 3 ^ 40 * 7024807 * 2
def baseEnd_7024807 : Nat := 1202367498689600714668669

theorem tailTrace_7024807 : CollatzResearch.WordTrace tailWord_7024807 prefixEnd_7024807 1202367498689600714668669 := by
  unfold tailWord_7024807
  simp only [CollatzResearch.WordTrace]
  refine ⟨256215760261331455364408675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170810506840887636909605783 256215760261331455364408675)
  ·
    refine ⟨384323640391997183046613013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256215760261331455364408675 384323640391997183046613013)
    ·
      refine ⟨18015170643374867955309985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 384323640391997183046613013 18015170643374867955309985)
      ·
        refine ⟨13511377982531150966482489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18015170643374867955309985 13511377982531150966482489)
        ·
          refine ⟨10133533486898363224861867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13511377982531150966482489 10133533486898363224861867)
          ·
            refine ⟨15200300230347544837292801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10133533486898363224861867 15200300230347544837292801)
            ·
              refine ⟨11400225172760658627969601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15200300230347544837292801 11400225172760658627969601)
              ·
                refine ⟨8550168879570493970977201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11400225172760658627969601 8550168879570493970977201)
                ·
                  refine ⟨6412626659677870478232901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8550168879570493970977201 6412626659677870478232901)
                  ·
                    refine ⟨1202367498689600714668669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6412626659677870478232901 1202367498689600714668669)
                    ·
                      rfl

theorem cell23_7024807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_7024807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024807 prefixEnd_7024807 := by exact prefixLift 7024807
  have htrace : WordTrace (prefixWord ++ tailWord_7024807) baseStart_7024807 baseEnd_7024807 := by
    simpa [prefixWord, tailWord_7024807, baseEnd_7024807] using wordTrace_append hprefix tailTrace_7024807
  have hstable : (prefixWord ++ tailWord_7024807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024807).length < 2 ^ (prefixWord ++ tailWord_7024807).sum := by decide
  have hdescent : baseEnd_7024807 < baseStart_7024807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024840 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 1, 3, 2]
def baseStart_7024840 : Nat := 118140960795 + 7024840 * 2 ^ 59
def prefixEnd_7024840 : Nat := 4983230072969 + 3 ^ 40 * 7024840 * 2
def baseEnd_7024840 : Nat := 3607119440930400514893355

theorem tailTrace_7024840 : CollatzResearch.WordTrace tailWord_7024840 prefixEnd_7024840 3607119440930400514893355 := by
  unfold tailWord_7024840
  simp only [CollatzResearch.WordTrace]
  refine ⟨128108481935105951000179987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170811309246807934666906649 128108481935105951000179987)
  ·
    refine ⟨192162722902658926500269981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128108481935105951000179987 192162722902658926500269981)
    ·
      refine ⟨72061021088497097437601243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192162722902658926500269981 72061021088497097437601243)
      ·
        refine ⟨108091531632745646156401865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72061021088497097437601243 108091531632745646156401865)
        ·
          refine ⟨81068648724559234617301399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108091531632745646156401865 81068648724559234617301399)
          ·
            refine ⟨121602973086838851925952099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81068648724559234617301399 121602973086838851925952099)
            ·
              refine ⟨182404459630258277888928149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121602973086838851925952099 182404459630258277888928149)
              ·
                refine ⟨8550209045168356776043507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182404459630258277888928149 8550209045168356776043507)
                ·
                  refine ⟨12825313567752535164065261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8550209045168356776043507 12825313567752535164065261)
                  ·
                    refine ⟨4809492587907200686524473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12825313567752535164065261 4809492587907200686524473)
                    ·
                      refine ⟨3607119440930400514893355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809492587907200686524473 3607119440930400514893355)
                      ·
                        rfl

theorem cell23_7024840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_7024840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024840 prefixEnd_7024840 := by exact prefixLift 7024840
  have htrace : WordTrace (prefixWord ++ tailWord_7024840) baseStart_7024840 baseEnd_7024840 := by
    simpa [prefixWord, tailWord_7024840, baseEnd_7024840] using wordTrace_append hprefix tailTrace_7024840
  have hstable : (prefixWord ++ tailWord_7024840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024840).length < 2 ^ (prefixWord ++ tailWord_7024840).sum := by decide
  have hdescent : baseEnd_7024840 < baseStart_7024840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024857 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 1, 3, 2]
def baseStart_7024857 : Nat := 118140960795 + 7024857 * 2 ^ 59
def prefixEnd_7024857 : Nat := 4983230072969 + 3 ^ 40 * 7024857 * 2
def baseEnd_7024857 : Nat := 3607128170101526948380777

theorem tailTrace_7024857 : CollatzResearch.WordTrace tailWord_7024857 prefixEnd_7024857 3607128170101526948380777 := by
  unfold tailWord_7024857
  simp only [CollatzResearch.WordTrace]
  refine ⟨256217583911150313903728825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170811722607433542602485883 256217583911150313903728825)
  ·
    refine ⟨192163187933362735427796619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256217583911150313903728825 192163187933362735427796619)
    ·
      refine ⟨288244781900044103141694929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192163187933362735427796619 288244781900044103141694929)
      ·
        refine ⟨216183586425033077356271197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288244781900044103141694929 216183586425033077356271197)
        ·
          refine ⟨81068844909387404008601699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216183586425033077356271197 81068844909387404008601699)
          ·
            refine ⟨121603267364081106012902549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81068844909387404008601699 121603267364081106012902549)
            ·
              refine ⟨5700153157691301844354807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121603267364081106012902549 5700153157691301844354807)
              ·
                refine ⟨8550229736536952766532211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5700153157691301844354807 8550229736536952766532211)
                ·
                  refine ⟨12825344604805429149798317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8550229736536952766532211 12825344604805429149798317)
                  ·
                    refine ⟨4809504226802035931174369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12825344604805429149798317 4809504226802035931174369)
                    ·
                      refine ⟨3607128170101526948380777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809504226802035931174369 3607128170101526948380777)
                      ·
                        rfl

theorem cell23_7024857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 3, 2].length) (baseStart_7024857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024857 prefixEnd_7024857 := by exact prefixLift 7024857
  have htrace : WordTrace (prefixWord ++ tailWord_7024857) baseStart_7024857 baseEnd_7024857 := by
    simpa [prefixWord, tailWord_7024857, baseEnd_7024857] using wordTrace_append hprefix tailTrace_7024857
  have hstable : (prefixWord ++ tailWord_7024857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024857).length < 2 ^ (prefixWord ++ tailWord_7024857).sum := by decide
  have hdescent : baseEnd_7024857 < baseStart_7024857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024927 : List Nat := [1, 1, 2, 4, 3, 2, 3, 2, 5]
def baseStart_7024927 : Nat := 118140960795 + 7024927 * 2 ^ 59
def prefixEnd_7024927 : Nat := 4983230072969 + 3 ^ 40 * 7024927 * 2
def baseEnd_7024927 : Nat := 400796012638593519389495

theorem tailTrace_7024927 : CollatzResearch.WordTrace tailWord_7024927 prefixEnd_7024927 400796012638593519389495 := by
  unfold tailWord_7024927
  simp only [CollatzResearch.WordTrace]
  refine ⟨256220137020896715858777035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170813424680597810572518023 256220137020896715858777035)
  ·
    refine ⟨384330205531345073788165553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256220137020896715858777035 384330205531345073788165553)
    ·
      refine ⟨288247654148508805341124165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384330205531345073788165553 288247654148508805341124165)
      ·
        refine ⟨54046435152845401001460781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288247654148508805341124165 54046435152845401001460781)
        ·
          refine ⟨20267413182317025375547793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54046435152845401001460781 20267413182317025375547793)
          ·
            refine ⟨15200559886737769031660845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20267413182317025375547793 15200559886737769031660845)
            ·
              refine ⟨5700209957526663386872817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15200559886737769031660845 5700209957526663386872817)
              ·
                refine ⟨4275157468144997540154613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5700209957526663386872817 4275157468144997540154613)
                ·
                  refine ⟨400796012638593519389495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4275157468144997540154613 400796012638593519389495)
                  ·
                    rfl

theorem cell23_7024927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 2, 5].length) (baseStart_7024927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024927 prefixEnd_7024927 := by exact prefixLift 7024927
  have htrace : WordTrace (prefixWord ++ tailWord_7024927) baseStart_7024927 baseEnd_7024927 := by
    simpa [prefixWord, tailWord_7024927, baseEnd_7024927] using wordTrace_append hprefix tailTrace_7024927
  have hstable : (prefixWord ++ tailWord_7024927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024927).length < 2 ^ (prefixWord ++ tailWord_7024927).sum := by decide
  have hdescent : baseEnd_7024927 < baseStart_7024927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024938 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_7024938 : Nat := 118140960795 + 7024938 * 2 ^ 59
def prefixEnd_7024938 : Nat := 4983230072969 + 3 ^ 40 * 7024938 * 2
def baseEnd_7024938 : Nat := 3607169762034541131467905

theorem tailTrace_7024938 : CollatzResearch.WordTrace tailWord_7024938 prefixEnd_7024938 3607169762034541131467905 := by
  unfold tailWord_7024938
  simp only [CollatzResearch.WordTrace]
  refine ⟨64055134555964216184356867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170813692149237909824951645 64055134555964216184356867)
  ·
    refine ⟨96082701833946324276535301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64055134555964216184356867 96082701833946324276535301)
    ·
      refine ⟨18015506593864935801850369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96082701833946324276535301 18015506593864935801850369)
      ·
        refine ⟨13511629945398701851387777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18015506593864935801850369 13511629945398701851387777)
        ·
          refine ⟨10133722459049026388540833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13511629945398701851387777 10133722459049026388540833)
          ·
            refine ⟨7600291844286769791405625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10133722459049026388540833 7600291844286769791405625)
            ·
              refine ⟨5700218883215077343554219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7600291844286769791405625 5700218883215077343554219)
              ·
                refine ⟨8550328324822616015331329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5700218883215077343554219 8550328324822616015331329)
                ·
                  refine ⟨6412746243616962011498497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8550328324822616015331329 6412746243616962011498497)
                  ·
                    refine ⟨4809559682712721508623873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6412746243616962011498497 4809559682712721508623873)
                    ·
                      refine ⟨3607169762034541131467905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809559682712721508623873 3607169762034541131467905)
                      ·
                        rfl

theorem cell23_7024938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_7024938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024938 prefixEnd_7024938 := by exact prefixLift 7024938
  have htrace : WordTrace (prefixWord ++ tailWord_7024938) baseStart_7024938 baseEnd_7024938 := by
    simpa [prefixWord, tailWord_7024938, baseEnd_7024938] using wordTrace_append hprefix tailTrace_7024938
  have hstable : (prefixWord ++ tailWord_7024938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024938).length < 2 ^ (prefixWord ++ tailWord_7024938).sum := by decide
  have hdescent : baseEnd_7024938 < baseStart_7024938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024963 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 3]
def baseStart_7024963 : Nat := 118140960795 + 7024963 * 2 ^ 59
def prefixEnd_7024963 : Nat := 4983230072969 + 3 ^ 40 * 7024963 * 2
def baseEnd_7024963 : Nat := 3607182599050903533655289

theorem tailTrace_7024963 : CollatzResearch.WordTrace tailWord_7024963 prefixEnd_7024963 3607182599050903533655289 := by
  unfold tailWord_7024963
  simp only [CollatzResearch.WordTrace]
  refine ⟨256221450048766294007087543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170814300032510862671391695 256221450048766294007087543)
  ·
    refine ⟨384332175073149441010631315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256221450048766294007087543 384332175073149441010631315)
    ·
      refine ⟨576498262609724161515946973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384332175073149441010631315 576498262609724161515946973)
      ·
        refine ⟨216186848478646560568480115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 576498262609724161515946973 216186848478646560568480115)
        ·
          refine ⟨324280272717969840852720173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216186848478646560568480115 324280272717969840852720173)
          ·
            refine ⟨121605102269238690319770065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 324280272717969840852720173 121605102269238690319770065)
            ·
              refine ⟨91203826701929017739827549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121605102269238690319770065 91203826701929017739827549)
              ·
                refine ⟨34201435013223381652435331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91203826701929017739827549 34201435013223381652435331)
                ·
                  refine ⟨51302152519835072478652997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34201435013223381652435331 51302152519835072478652997)
                  ·
                    refine ⟨9619153597469076089747437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51302152519835072478652997 9619153597469076089747437)
                    ·
                      refine ⟨3607182599050903533655289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9619153597469076089747437 3607182599050903533655289)
                      ·
                        rfl

theorem cell23_7024963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_7024963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024963 prefixEnd_7024963 := by exact prefixLift 7024963
  have htrace : WordTrace (prefixWord ++ tailWord_7024963) baseStart_7024963 baseEnd_7024963 := by
    simpa [prefixWord, tailWord_7024963, baseEnd_7024963] using wordTrace_append hprefix tailTrace_7024963
  have hstable : (prefixWord ++ tailWord_7024963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024963).length < 2 ^ (prefixWord ++ tailWord_7024963).sum := by decide
  have hdescent : baseEnd_7024963 < baseStart_7024963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7024993 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_7024993 : Nat := 118140960795 + 7024993 * 2 ^ 59
def prefixEnd_7024993 : Nat := 4983230072969 + 3 ^ 40 * 7024993 * 2
def baseEnd_7024993 : Nat := 3607198003470538416280151

theorem tailTrace_7024993 : CollatzResearch.WordTrace tailWord_7024993 prefixEnd_7024993 3607198003470538416280151 := by
  unfold tailWord_7024993
  simp only [CollatzResearch.WordTrace]
  refine ⟨256222544238657609130679633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170815029492438406087119755 256222544238657609130679633)
  ·
    refine ⟨192166908178993206848009725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256222544238657609130679633 192166908178993206848009725)
    ·
      refine ⟨72062590567122452568003647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192166908178993206848009725 72062590567122452568003647)
      ·
        refine ⟨108093885850683678852005471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72062590567122452568003647 108093885850683678852005471)
        ·
          refine ⟨162140828776025518278008207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108093885850683678852005471 162140828776025518278008207)
          ·
            refine ⟨243211243164038277417012311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162140828776025518278008207 243211243164038277417012311)
            ·
              refine ⟨364816864746057416125518467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243211243164038277417012311 364816864746057416125518467)
              ·
                refine ⟨547225297119086124188277701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364816864746057416125518467 547225297119086124188277701)
                ·
                  refine ⟨102604743209828648285302069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547225297119086124188277701 102604743209828648285302069)
                  ·
                    refine ⟨9619194675921435776747069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102604743209828648285302069 9619194675921435776747069)
                    ·
                      refine ⟨3607198003470538416280151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9619194675921435776747069 3607198003470538416280151)
                      ·
                        rfl

theorem cell23_7024993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_7024993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7024993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7024993 prefixEnd_7024993 := by exact prefixLift 7024993
  have htrace : WordTrace (prefixWord ++ tailWord_7024993) baseStart_7024993 baseEnd_7024993 := by
    simpa [prefixWord, tailWord_7024993, baseEnd_7024993] using wordTrace_append hprefix tailTrace_7024993
  have hstable : (prefixWord ++ tailWord_7024993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7024993).length < 2 ^ (prefixWord ++ tailWord_7024993).sum := by decide
  have hdescent : baseEnd_7024993 < baseStart_7024993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7024993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025000 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 6]
def baseStart_7025000 : Nat := 118140960795 + 7025000 * 2 ^ 59
def prefixEnd_7025000 : Nat := 4983230072969 + 3 ^ 40 * 7025000 * 2
def baseEnd_7025000 : Nat := 400800177537235543210291

theorem tailTrace_7025000 : CollatzResearch.WordTrace tailWord_7025000 prefixEnd_7025000 400800177537235543210291 := by
  unfold tailWord_7025000
  simp only [CollatzResearch.WordTrace]
  refine ⟨128111399774816124663092227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170815199699754832884122969 128111399774816124663092227)
  ·
    refine ⟨192167099662224186994638341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128111399774816124663092227 192167099662224186994638341)
    ·
      refine ⟨36031331186667035061494689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192167099662224186994638341 36031331186667035061494689)
      ·
        refine ⟨27023498390000276296121017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36031331186667035061494689 27023498390000276296121017)
        ·
          refine ⟨20267623792500207222090763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27023498390000276296121017 20267623792500207222090763)
          ·
            refine ⟨30401435688750310833136145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20267623792500207222090763 30401435688750310833136145)
            ·
              refine ⟨22801076766562733124852109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30401435688750310833136145 22801076766562733124852109)
              ·
                refine ⟨8550403787461024921819541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22801076766562733124852109 8550403787461024921819541)
                ·
                  refine ⟨400800177537235543210291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8550403787461024921819541 400800177537235543210291)
                  ·
                    rfl

theorem cell23_7025000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 6].length) (baseStart_7025000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025000 prefixEnd_7025000 := by exact prefixLift 7025000
  have htrace : WordTrace (prefixWord ++ tailWord_7025000) baseStart_7025000 baseEnd_7025000 := by
    simpa [prefixWord, tailWord_7025000, baseEnd_7025000] using wordTrace_append hprefix tailTrace_7025000
  have hstable : (prefixWord ++ tailWord_7025000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025000).length < 2 ^ (prefixWord ++ tailWord_7025000).sum := by decide
  have hdescent : baseEnd_7025000 < baseStart_7025000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025014 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7025014 : Nat := 118140960795 + 7025014 * 2 ^ 59
def prefixEnd_7025014 : Nat := 4983230072969 + 3 ^ 40 * 7025014 * 2
def baseEnd_7025014 : Nat := 3607208786564282834117555

theorem tailTrace_7025014 : CollatzResearch.WordTrace tailWord_7025014 prefixEnd_7025014 3607208786564282834117555 := by
  unfold tailWord_7025014
  simp only [CollatzResearch.WordTrace]
  refine ⟨16013956885723845607324631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170815540114387686478129397 16013956885723845607324631)
  ·
    refine ⟨24020935328585768410986947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16013956885723845607324631 24020935328585768410986947)
    ·
      refine ⟨36031402992878652616480421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24020935328585768410986947 36031402992878652616480421)
      ·
        refine ⟨6755888061164747365590079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36031402992878652616480421 6755888061164747365590079)
        ·
          refine ⟨10133832091747121048385119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6755888061164747365590079 10133832091747121048385119)
          ·
            refine ⟨15200748137620681572577679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10133832091747121048385119 15200748137620681572577679)
            ·
              refine ⟨22801122206431022358866519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15200748137620681572577679 22801122206431022358866519)
              ·
                refine ⟨34201683309646533538299779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22801122206431022358866519 34201683309646533538299779)
                ·
                  refine ⟨51302524964469800307449669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34201683309646533538299779 51302524964469800307449669)
                  ·
                    refine ⟨9619223430838087557646813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51302524964469800307449669 9619223430838087557646813)
                    ·
                      refine ⟨3607208786564282834117555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9619223430838087557646813 3607208786564282834117555)
                      ·
                        rfl

theorem cell23_7025014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7025014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025014 prefixEnd_7025014 := by exact prefixLift 7025014
  have htrace : WordTrace (prefixWord ++ tailWord_7025014) baseStart_7025014 baseEnd_7025014 := by
    simpa [prefixWord, tailWord_7025014, baseEnd_7025014] using wordTrace_append hprefix tailTrace_7025014
  have hstable : (prefixWord ++ tailWord_7025014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025014).length < 2 ^ (prefixWord ++ tailWord_7025014).sum := by decide
  have hdescent : baseEnd_7025014 < baseStart_7025014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025034 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 6]
def baseStart_7025034 : Nat := 118140960795 + 7025034 * 2 ^ 59
def prefixEnd_7025034 : Nat := 4983230072969 + 3 ^ 40 * 7025034 * 2
def baseEnd_7025034 : Nat := 400802117353041417318607

theorem tailTrace_7025034 : CollatzResearch.WordTrace tailWord_7025034 prefixEnd_7025034 400802117353041417318607 := by
  unfold tailWord_7025034
  simp only [CollatzResearch.WordTrace]
  refine ⟨64056009907877268283230539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170816026421006048755281437 64056009907877268283230539)
  ·
    refine ⟨96084014861815902424845809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64056009907877268283230539 96084014861815902424845809)
    ·
      refine ⟨72063011146361926818634357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96084014861815902424845809 72063011146361926818634357)
      ·
        refine ⟨6755907294971430639246971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72063011146361926818634357 6755907294971430639246971)
        ·
          refine ⟨10133860942457145958870457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6755907294971430639246971 10133860942457145958870457)
          ·
            refine ⟨7600395706842859469152843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10133860942457145958870457 7600395706842859469152843)
            ·
              refine ⟨11400593560264289203729265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7600395706842859469152843 11400593560264289203729265)
              ·
                refine ⟨8550445170198216902796949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11400593560264289203729265 8550445170198216902796949)
                ·
                  refine ⟨400802117353041417318607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8550445170198216902796949 400802117353041417318607)
                  ·
                    rfl

theorem cell23_7025034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_7025034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025034 prefixEnd_7025034 := by exact prefixLift 7025034
  have htrace : WordTrace (prefixWord ++ tailWord_7025034) baseStart_7025034 baseEnd_7025034 := by
    simpa [prefixWord, tailWord_7025034, baseEnd_7025034] using wordTrace_append hprefix tailTrace_7025034
  have hstable : (prefixWord ++ tailWord_7025034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025034).length < 2 ^ (prefixWord ++ tailWord_7025034).sum := by decide
  have hdescent : baseEnd_7025034 < baseStart_7025034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025054 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_7025054 : Nat := 118140960795 + 7025054 * 2 ^ 59
def prefixEnd_7025054 : Nat := 4983230072969 + 3 ^ 40 * 7025054 * 2
def baseEnd_7025054 : Nat := 3607229325790462677617371

theorem tailTrace_7025054 : CollatzResearch.WordTrace tailWord_7025054 prefixEnd_7025054 3607229325790462677617371 := by
  unfold tailWord_7025054
  simp only [CollatzResearch.WordTrace]
  refine ⟨32028096136429577068581277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170816512727624411032433477 32028096136429577068581277)
  ·
    refine ⟨12010536051161091400717979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32028096136429577068581277 12010536051161091400717979)
    ·
      refine ⟨18015804076741637101076969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12010536051161091400717979 18015804076741637101076969)
      ·
        refine ⟨13511853057556227825807727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18015804076741637101076969 13511853057556227825807727)
        ·
          refine ⟨20267779586334341738711591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13511853057556227825807727 20267779586334341738711591)
          ·
            refine ⟨30401669379501512608067387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20267779586334341738711591 30401669379501512608067387)
            ·
              refine ⟨45602504069252268912101081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30401669379501512608067387 45602504069252268912101081)
              ·
                refine ⟨34201878051939201684075811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45602504069252268912101081 34201878051939201684075811)
                ·
                  refine ⟨51302817077908802526113717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34201878051939201684075811 51302817077908802526113717)
                  ·
                    refine ⟨4809639101053950236823161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51302817077908802526113717 4809639101053950236823161)
                    ·
                      refine ⟨3607229325790462677617371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809639101053950236823161 3607229325790462677617371)
                      ·
                        rfl

theorem cell23_7025054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_7025054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025054 prefixEnd_7025054 := by exact prefixLift 7025054
  have htrace : WordTrace (prefixWord ++ tailWord_7025054) baseStart_7025054 baseEnd_7025054 := by
    simpa [prefixWord, tailWord_7025054, baseEnd_7025054] using wordTrace_append hprefix tailTrace_7025054
  have hstable : (prefixWord ++ tailWord_7025054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025054).length < 2 ^ (prefixWord ++ tailWord_7025054).sum := by decide
  have hdescent : baseEnd_7025054 < baseStart_7025054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025060 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_7025060 : Nat := 118140960795 + 7025060 * 2 ^ 59
def prefixEnd_7025060 : Nat := 4983230072969 + 3 ^ 40 * 7025060 * 2
def baseEnd_7025060 : Nat := 1202410802224796551380781

theorem tailTrace_7025060 : CollatzResearch.WordTrace tailWord_7025060 prefixEnd_7025060 1202410802224796551380781 := by
  unfold tailWord_7025060
  simp only [CollatzResearch.WordTrace]
  refine ⟨128112493964707439786684317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170816658619609919715579089 128112493964707439786684317)
  ·
    refine ⟨48042185236765289920006619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128112493964707439786684317 48042185236765289920006619)
    ·
      refine ⟨72063277855147934880009929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48042185236765289920006619 72063277855147934880009929)
      ·
        refine ⟨54047458391360951160007447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72063277855147934880009929 54047458391360951160007447)
        ·
          refine ⟨81071187587041426740011171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54047458391360951160007447 81071187587041426740011171)
          ·
            refine ⟨121606781380562140110016757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81071187587041426740011171 121606781380562140110016757)
            ·
              refine ⟨11400635754427700635314071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121606781380562140110016757 11400635754427700635314071)
              ·
                refine ⟨17100953631641550952971107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11400635754427700635314071 17100953631641550952971107)
                ·
                  refine ⟨25651430447462326429456661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17100953631641550952971107 25651430447462326429456661)
                  ·
                    refine ⟨1202410802224796551380781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25651430447462326429456661 1202410802224796551380781)
                    ·
                      rfl

theorem cell23_7025060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_7025060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025060 prefixEnd_7025060 := by exact prefixLift 7025060
  have htrace : WordTrace (prefixWord ++ tailWord_7025060) baseStart_7025060 baseEnd_7025060 := by
    simpa [prefixWord, tailWord_7025060, baseEnd_7025060] using wordTrace_append hprefix tailTrace_7025060
  have hstable : (prefixWord ++ tailWord_7025060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025060).length < 2 ^ (prefixWord ++ tailWord_7025060).sum := by decide
  have hdescent : baseEnd_7025060 < baseStart_7025060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025064 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 1, 5]
def baseStart_7025064 : Nat := 118140960795 + 7025064 * 2 ^ 59
def prefixEnd_7025064 : Nat := 4983230072969 + 3 ^ 40 * 7025064 * 2
def baseEnd_7025064 : Nat := 1202411486865669212830775

theorem tailTrace_7025064 : CollatzResearch.WordTrace tailWord_7025064 prefixEnd_7025064 1202411486865669212830775 := by
  unfold tailWord_7025064
  simp only [CollatzResearch.WordTrace]
  refine ⟨128112566910700194128257123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170816755880933592171009497 128112566910700194128257123)
  ·
    refine ⟨192168850366050291192385685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128112566910700194128257123 192168850366050291192385685)
    ·
      refine ⟨9007914860908607399643079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192168850366050291192385685 9007914860908607399643079)
      ·
        refine ⟨13511872291362911099464619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9007914860908607399643079 13511872291362911099464619)
        ·
          refine ⟨20267808437044366649196929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13511872291362911099464619 20267808437044366649196929)
          ·
            refine ⟨15200856327783274986897697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20267808437044366649196929 15200856327783274986897697)
            ·
              refine ⟨11400642245837456240173273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15200856327783274986897697 11400642245837456240173273)
              ·
                refine ⟨8550481684378092180129955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11400642245837456240173273 8550481684378092180129955)
                ·
                  refine ⟨12825722526567138270194933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8550481684378092180129955 12825722526567138270194933)
                  ·
                    refine ⟨1202411486865669212830775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12825722526567138270194933 1202411486865669212830775)
                    ·
                      rfl

theorem cell23_7025064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_7025064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025064 prefixEnd_7025064 := by exact prefixLift 7025064
  have htrace : WordTrace (prefixWord ++ tailWord_7025064) baseStart_7025064 baseEnd_7025064 := by
    simpa [prefixWord, tailWord_7025064, baseEnd_7025064] using wordTrace_append hprefix tailTrace_7025064
  have hstable : (prefixWord ++ tailWord_7025064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025064).length < 2 ^ (prefixWord ++ tailWord_7025064).sum := by decide
  have hdescent : baseEnd_7025064 < baseStart_7025064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025103 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 2, 7]
def baseStart_7025103 : Nat := 118140960795 + 7025103 * 2 ^ 59
def prefixEnd_7025103 : Nat := 4983230072969 + 3 ^ 40 * 7025103 * 2
def baseEnd_7025103 : Nat := 1202418162114177661968215

theorem tailTrace_7025103 : CollatzResearch.WordTrace tailWord_7025103 prefixEnd_7025103 1202418162114177661968215 := by
  unfold tailWord_7025103
  simp only [CollatzResearch.WordTrace]
  refine ⟨256226556268259097917183963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170817704178839398611455975 256226556268259097917183963)
  ·
    refine ⟨384339834402388646875775945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256226556268259097917183963 384339834402388646875775945)
    ·
      refine ⟨288254875801791485156831959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384339834402388646875775945 288254875801791485156831959)
      ·
        refine ⟨432382313702687227735247939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288254875801791485156831959 432382313702687227735247939)
        ·
          refine ⟨648573470554030841602871909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432382313702687227735247939 648573470554030841602871909)
          ·
            refine ⟨121607525728880782800538483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 648573470554030841602871909 121607525728880782800538483)
            ·
              refine ⟨182411288593321174200807725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121607525728880782800538483 182411288593321174200807725)
              ·
                refine ⟨68404233222495440325302897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182411288593321174200807725 68404233222495440325302897)
                ·
                  refine ⟨51303174916871580243977173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68404233222495440325302897 51303174916871580243977173)
                  ·
                    refine ⟨1202418162114177661968215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51303174916871580243977173 1202418162114177661968215)
                    ·
                      rfl

theorem cell23_7025103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_7025103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025103 prefixEnd_7025103 := by exact prefixLift 7025103
  have htrace : WordTrace (prefixWord ++ tailWord_7025103) baseStart_7025103 baseEnd_7025103 := by
    simpa [prefixWord, tailWord_7025103, baseEnd_7025103] using wordTrace_append hprefix tailTrace_7025103
  have hstable : (prefixWord ++ tailWord_7025103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025103).length < 2 ^ (prefixWord ++ tailWord_7025103).sum := by decide
  have hdescent : baseEnd_7025103 < baseStart_7025103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025117 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 1, 3, 3]
def baseStart_7025117 : Nat := 118140960795 + 7025117 * 2 ^ 59
def prefixEnd_7025117 : Nat := 4983230072969 + 3 ^ 40 * 7025117 * 2
def baseEnd_7025117 : Nat := 3607261675071695931129581

theorem tailTrace_7025117 : CollatzResearch.WordTrace tailWord_7025117 prefixEnd_7025117 3607261675071695931129581 := by
  unfold tailWord_7025117
  simp only [CollatzResearch.WordTrace]
  refine ⟨256227066890208378308193605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170818044593472252205462403 256227066890208378308193605)
  ·
    refine ⟨48042575041914070932786301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256227066890208378308193605 48042575041914070932786301)
    ·
      refine ⟨18015965640717776599794863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48042575041914070932786301 18015965640717776599794863)
      ·
        refine ⟨27023948461076664899692295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18015965640717776599794863 27023948461076664899692295)
        ·
          refine ⟨40535922691614997349538443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27023948461076664899692295 40535922691614997349538443)
          ·
            refine ⟨60803884037422496024307665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40535922691614997349538443 60803884037422496024307665)
            ·
              refine ⟨45602913028066872018230749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60803884037422496024307665 45602913028066872018230749)
              ·
                refine ⟨17101092385525077006836531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45602913028066872018230749 17101092385525077006836531)
                ·
                  refine ⟨25651638578287615510254797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17101092385525077006836531 25651638578287615510254797)
                  ·
                    refine ⟨9619364466857855816345549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25651638578287615510254797 9619364466857855816345549)
                    ·
                      refine ⟨3607261675071695931129581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9619364466857855816345549 3607261675071695931129581)
                      ·
                        rfl

theorem cell23_7025117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_7025117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025117 prefixEnd_7025117 := by exact prefixLift 7025117
  have htrace : WordTrace (prefixWord ++ tailWord_7025117) baseStart_7025117 baseEnd_7025117 := by
    simpa [prefixWord, tailWord_7025117, baseEnd_7025117] using wordTrace_append hprefix tailTrace_7025117
  have hstable : (prefixWord ++ tailWord_7025117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025117).length < 2 ^ (prefixWord ++ tailWord_7025117).sum := by decide
  have hdescent : baseEnd_7025117 < baseStart_7025117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025180 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 9]
def baseStart_7025180 : Nat := 118140960795 + 7025180 * 2 ^ 59
def prefixEnd_7025180 : Nat := 4983230072969 + 3 ^ 40 * 7025180 * 2
def baseEnd_7025180 : Nat := 400810447150325464960199

theorem tailTrace_7025180 : CollatzResearch.WordTrace tailWord_7025180 prefixEnd_7025180 400810447150325464960199 := by
  unfold tailWord_7025180
  simp only [CollatzResearch.WordTrace]
  refine ⟨128114682344490070033868497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170819576459320093378491329 128114682344490070033868497)
  ·
    refine ⟨96086011758367552525401373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128114682344490070033868497 96086011758367552525401373)
    ·
      refine ⟨36032254409387832197025515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96086011758367552525401373 36032254409387832197025515)
      ·
        refine ⟨54048381614081748295538273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36032254409387832197025515 54048381614081748295538273)
        ·
          refine ⟨40536286210561311221653705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54048381614081748295538273 40536286210561311221653705)
          ·
            refine ⟨30402214657920983416240279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40536286210561311221653705 30402214657920983416240279)
            ·
              refine ⟨45603321986881475124360419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30402214657920983416240279 45603321986881475124360419)
              ·
                refine ⟨68404982980322212686540629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45603321986881475124360419 68404982980322212686540629)
                ·
                  refine ⟨400810447150325464960199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68404982980322212686540629 400810447150325464960199)
                  ·
                    rfl

theorem cell23_7025180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_7025180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025180 prefixEnd_7025180 := by exact prefixLift 7025180
  have htrace : WordTrace (prefixWord ++ tailWord_7025180) baseStart_7025180 baseEnd_7025180 := by
    simpa [prefixWord, tailWord_7025180, baseEnd_7025180] using wordTrace_append hprefix tailTrace_7025180
  have hstable : (prefixWord ++ tailWord_7025180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025180).length < 2 ^ (prefixWord ++ tailWord_7025180).sum := by decide
  have hdescent : baseEnd_7025180 < baseStart_7025180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025247 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 1, 6, 2]
def baseStart_7025247 : Nat := 118140960795 + 7025247 * 2 ^ 59
def prefixEnd_7025247 : Nat := 4983230072969 + 3 ^ 40 * 7025247 * 2
def baseEnd_7025247 : Nat := 3607328427556780422503983

theorem tailTrace_7025247 : CollatzResearch.WordTrace tailWord_7025247 prefixEnd_7025247 3607328427556780422503983 := by
  unfold tailWord_7025247
  simp only [CollatzResearch.WordTrace]
  refine ⟨256231808379737410510425995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170821205586491607006950663 256231808379737410510425995)
  ·
    refine ⟨384347712569606115765638993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256231808379737410510425995 384347712569606115765638993)
    ·
      refine ⟨288260784427204586824229245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384347712569606115765638993 288260784427204586824229245)
      ·
        refine ⟨108097794160201720059085967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288260784427204586824229245 108097794160201720059085967)
        ·
          refine ⟨162146691240302580088628951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108097794160201720059085967 162146691240302580088628951)
          ·
            refine ⟨243220036860453870132943427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162146691240302580088628951 243220036860453870132943427)
            ·
              refine ⟨364830055290680805199415141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243220036860453870132943427 364830055290680805199415141)
              ·
                refine ⟨68405635367002650974890339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364830055290680805199415141 68405635367002650974890339)
                ·
                  refine ⟨102608453050503976462335509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68405635367002650974890339 102608453050503976462335509)
                  ·
                    refine ⟨4809771236742373896671977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102608453050503976462335509 4809771236742373896671977)
                    ·
                      refine ⟨3607328427556780422503983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809771236742373896671977 3607328427556780422503983)
                      ·
                        rfl

theorem cell23_7025247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_7025247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025247 prefixEnd_7025247 := by exact prefixLift 7025247
  have htrace : WordTrace (prefixWord ++ tailWord_7025247) baseStart_7025247 baseEnd_7025247 := by
    simpa [prefixWord, tailWord_7025247, baseEnd_7025247] using wordTrace_append hprefix tailTrace_7025247
  have hstable : (prefixWord ++ tailWord_7025247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025247).length < 2 ^ (prefixWord ++ tailWord_7025247).sum := by decide
  have hdescent : baseEnd_7025247 < baseStart_7025247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025260 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_7025260 : Nat := 118140960795 + 7025260 * 2 ^ 59
def prefixEnd_7025260 : Nat := 4983230072969 + 3 ^ 40 * 7025260 * 2
def baseEnd_7025260 : Nat := 3607335102805288871641423

theorem tailTrace_7025260 : CollatzResearch.WordTrace tailWord_7025260 prefixEnd_7025260 3607335102805288871641423 := by
  unfold tailWord_7025260
  simp only [CollatzResearch.WordTrace]
  refine ⟨128116141264345156865324617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170821521685793542487099489 128116141264345156865324617)
  ·
    refine ⟨96087105948258867648993463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128116141264345156865324617 96087105948258867648993463)
    ·
      refine ⟨144130658922388301473490195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96087105948258867648993463 144130658922388301473490195)
      ·
        refine ⟨216195988383582452210235293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144130658922388301473490195 216195988383582452210235293)
        ·
          refine ⟨81073495643843419578838235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216195988383582452210235293 81073495643843419578838235)
          ·
            refine ⟨121610243465765129368257353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81073495643843419578838235 121610243465765129368257353)
            ·
              refine ⟨91207682599323847026193015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121610243465765129368257353 91207682599323847026193015)
              ·
                refine ⟨136811523898985770539289523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91207682599323847026193015 136811523898985770539289523)
                ·
                  refine ⟨205217285848478655808934285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136811523898985770539289523 205217285848478655808934285)
                  ·
                    refine ⟨76956482193179495928350357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 205217285848478655808934285 76956482193179495928350357)
                    ·
                      refine ⟨3607335102805288871641423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76956482193179495928350357 3607335102805288871641423)
                      ·
                        rfl

theorem cell23_7025260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_7025260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025260 prefixEnd_7025260 := by exact prefixLift 7025260
  have htrace : WordTrace (prefixWord ++ tailWord_7025260) baseStart_7025260 baseEnd_7025260 := by
    simpa [prefixWord, tailWord_7025260, baseEnd_7025260] using wordTrace_append hprefix tailTrace_7025260
  have hstable : (prefixWord ++ tailWord_7025260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025260).length < 2 ^ (prefixWord ++ tailWord_7025260).sum := by decide
  have hdescent : baseEnd_7025260 < baseStart_7025260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025264 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 4]
def baseStart_7025264 : Nat := 118140960795 + 7025264 * 2 ^ 59
def prefixEnd_7025264 : Nat := 4983230072969 + 3 ^ 40 * 7025264 * 2
def baseEnd_7025264 : Nat := 3607337156727906855991405

theorem tailTrace_7025264 : CollatzResearch.WordTrace tailWord_7025264 prefixEnd_7025264 3607337156727906855991405 := by
  unfold tailWord_7025264
  simp only [CollatzResearch.WordTrace]
  refine ⟨128116214210337911206897423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170821618947117214942529897 128116214210337911206897423)
  ·
    refine ⟨192174321315506866810346135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128116214210337911206897423 192174321315506866810346135)
    ·
      refine ⟨288261481973260300215519203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192174321315506866810346135 288261481973260300215519203)
      ·
        refine ⟨432392222959890450323278805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288261481973260300215519203 432392222959890450323278805)
        ·
          refine ⟨10134192725622432429451847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 432392222959890450323278805 10134192725622432429451847)
          ·
            refine ⟨15201289088433648644177771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10134192725622432429451847 15201289088433648644177771)
            ·
              refine ⟨22801933632650472966266657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15201289088433648644177771 22801933632650472966266657)
              ·
                refine ⟨17101450224487854724699993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22801933632650472966266657 17101450224487854724699993)
                ·
                  refine ⟨12826087668365891043524995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17101450224487854724699993 12826087668365891043524995)
                  ·
                    refine ⟨19239131502548836565287493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12826087668365891043524995 19239131502548836565287493)
                    ·
                      refine ⟨3607337156727906855991405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19239131502548836565287493 3607337156727906855991405)
                      ·
                        rfl

theorem cell23_7025264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 4].length) (baseStart_7025264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025264 prefixEnd_7025264 := by exact prefixLift 7025264
  have htrace : WordTrace (prefixWord ++ tailWord_7025264) baseStart_7025264 baseEnd_7025264 := by
    simpa [prefixWord, tailWord_7025264, baseEnd_7025264] using wordTrace_append hprefix tailTrace_7025264
  have hstable : (prefixWord ++ tailWord_7025264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025264).length < 2 ^ (prefixWord ++ tailWord_7025264).sum := by decide
  have hdescent : baseEnd_7025264 < baseStart_7025264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025287 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 6]
def baseStart_7025287 : Nat := 118140960795 + 7025287 * 2 ^ 59
def prefixEnd_7025287 : Nat := 4983230072969 + 3 ^ 40 * 7025287 * 2
def baseEnd_7025287 : Nat := 400816551864773362889311

theorem tailTrace_7025287 : CollatzResearch.WordTrace tailWord_7025287 prefixEnd_7025287 400816551864773362889311 := by
  unfold tailWord_7025287
  simp only [CollatzResearch.WordTrace]
  refine ⟨256233267299592497341882115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170822178199728331561254743 256233267299592497341882115)
  ·
    refine ⟨384349900949388746012823173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256233267299592497341882115 384349900949388746012823173)
    ·
      refine ⟨72065606428010389877404345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384349900949388746012823173 72065606428010389877404345)
      ·
        refine ⟨54049204821007792408053259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72065606428010389877404345 54049204821007792408053259)
        ·
          refine ⟨81073807231511688612079889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54049204821007792408053259 81073807231511688612079889)
          ·
            refine ⟨60805355423633766459059917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81073807231511688612079889 60805355423633766459059917)
            ·
              refine ⟨22802008283862662422147469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60805355423633766459059917 22802008283862662422147469)
              ·
                refine ⟨8550753106448498408305301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22802008283862662422147469 8550753106448498408305301)
                ·
                  refine ⟨400816551864773362889311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8550753106448498408305301 400816551864773362889311)
                  ·
                    rfl

theorem cell23_7025287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 6].length) (baseStart_7025287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025287 prefixEnd_7025287 := by exact prefixLift 7025287
  have htrace : WordTrace (prefixWord ++ tailWord_7025287) baseStart_7025287 baseEnd_7025287 := by
    simpa [prefixWord, tailWord_7025287, baseEnd_7025287] using wordTrace_append hprefix tailTrace_7025287
  have hstable : (prefixWord ++ tailWord_7025287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025287).length < 2 ^ (prefixWord ++ tailWord_7025287).sum := by decide
  have hdescent : baseEnd_7025287 < baseStart_7025287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025325 : List Nat := [1, 5, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_7025325 : Nat := 118140960795 + 7025325 * 2 ^ 59
def prefixEnd_7025325 : Nat := 4983230072969 + 3 ^ 40 * 7025325 * 2
def baseEnd_7025325 : Nat := 1202456159682610372442875

theorem tailTrace_7025325 : CollatzResearch.WordTrace tailWord_7025325 prefixEnd_7025325 1202456159682610372442875 := by
  unfold tailWord_7025325
  simp only [CollatzResearch.WordTrace]
  refine ⟨256234653273454829831765429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170823102182303219887843619 256234653273454829831765429)
  ·
    refine ⟨24021998744386390296728009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256234653273454829831765429 24021998744386390296728009)
    ·
      refine ⟨18016499058289792722546007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24021998744386390296728009 18016499058289792722546007)
      ·
        refine ⟨27024748587434689083819011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18016499058289792722546007 27024748587434689083819011)
        ·
          refine ⟨40537122881152033625728517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27024748587434689083819011 40537122881152033625728517)
          ·
            refine ⟨7600710540216006304824097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40537122881152033625728517 7600710540216006304824097)
            ·
              refine ⟨5700532905162004728618073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7600710540216006304824097 5700532905162004728618073)
              ·
                refine ⟨4275399678871503546463555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5700532905162004728618073 4275399678871503546463555)
                ·
                  refine ⟨6413099518307255319695333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4275399678871503546463555 6413099518307255319695333)
                  ·
                    refine ⟨1202456159682610372442875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6413099518307255319695333 1202456159682610372442875)
                    ·
                      rfl

theorem cell23_7025325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_7025325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025325 prefixEnd_7025325 := by exact prefixLift 7025325
  have htrace : WordTrace (prefixWord ++ tailWord_7025325) baseStart_7025325 baseEnd_7025325 := by
    simpa [prefixWord, tailWord_7025325, baseEnd_7025325] using wordTrace_append hprefix tailTrace_7025325
  have hstable : (prefixWord ++ tailWord_7025325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025325).length < 2 ^ (prefixWord ++ tailWord_7025325).sum := by decide
  have hdescent : baseEnd_7025325 < baseStart_7025325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025354 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_7025354 : Nat := 118140960795 + 7025354 * 2 ^ 59
def prefixEnd_7025354 : Nat := 4983230072969 + 3 ^ 40 * 7025354 * 2
def baseEnd_7025354 : Nat := 3607383369986811503865991

theorem tailTrace_7025354 : CollatzResearch.WordTrace tailWord_7025354 prefixEnd_7025354 3607383369986811503865991 := by
  unfold tailWord_7025354
  simp only [CollatzResearch.WordTrace]
  refine ⟨64058927747587441946142779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170823807326899845189714077 64058927747587441946142779)
  ·
    refine ⟨96088391621381162919214169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64058927747587441946142779 96088391621381162919214169)
    ·
      refine ⟨72066293716035872189410627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96088391621381162919214169 72066293716035872189410627)
      ·
        refine ⟨108099440574053808284115941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72066293716035872189410627 108099440574053808284115941)
        ·
          refine ⟨20268645107635089053271739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108099440574053808284115941 20268645107635089053271739)
          ·
            refine ⟨30402967661452633579907609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20268645107635089053271739 30402967661452633579907609)
            ·
              refine ⟨22802225746089475184930707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30402967661452633579907609 22802225746089475184930707)
              ·
                refine ⟨34203338619134212777396061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22802225746089475184930707 34203338619134212777396061)
                ·
                  refine ⟨12826251982175329791523523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34203338619134212777396061 12826251982175329791523523)
                  ·
                    refine ⟨19239377973262994687285285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12826251982175329791523523 19239377973262994687285285)
                    ·
                      refine ⟨3607383369986811503865991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19239377973262994687285285 3607383369986811503865991)
                      ·
                        rfl

theorem cell23_7025354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_7025354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025354 prefixEnd_7025354 := by exact prefixLift 7025354
  have htrace : WordTrace (prefixWord ++ tailWord_7025354) baseStart_7025354 baseEnd_7025354 := by
    simpa [prefixWord, tailWord_7025354, baseEnd_7025354] using wordTrace_append hprefix tailTrace_7025354
  have hstable : (prefixWord ++ tailWord_7025354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025354).length < 2 ^ (prefixWord ++ tailWord_7025354).sum := by decide
  have hdescent : baseEnd_7025354 < baseStart_7025354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025358 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2]
def baseStart_7025358 : Nat := 118140960795 + 7025358 * 2 ^ 59
def prefixEnd_7025358 : Nat := 4983230072969 + 3 ^ 40 * 7025358 * 2
def baseEnd_7025358 : Nat := 3607385423909429488215973

theorem tailTrace_7025358 : CollatzResearch.WordTrace tailWord_7025358 prefixEnd_7025358 3607385423909429488215973 := by
  unfold tailWord_7025358
  simp only [CollatzResearch.WordTrace]
  refine ⟨32029482110291909558464591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170823904588223517645144485 32029482110291909558464591)
  ·
    refine ⟨48044223165437864337696887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32029482110291909558464591 48044223165437864337696887)
    ·
      refine ⟨72066334748156796506545331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48044223165437864337696887 72066334748156796506545331)
      ·
        refine ⟨108099502122235194759817997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72066334748156796506545331 108099502122235194759817997)
        ·
          refine ⟨40537313295838198034931749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108099502122235194759817997 40537313295838198034931749)
          ·
            refine ⟨7600746242969662131549703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40537313295838198034931749 7600746242969662131549703)
            ·
              refine ⟨11401119364454493197324555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7600746242969662131549703 11401119364454493197324555)
              ·
                refine ⟨17101679046681739795986833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11401119364454493197324555 17101679046681739795986833)
                ·
                  refine ⟨12826259285011304846990125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17101679046681739795986833 12826259285011304846990125)
                  ·
                    refine ⟨4809847231879239317621297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12826259285011304846990125 4809847231879239317621297)
                    ·
                      refine ⟨3607385423909429488215973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809847231879239317621297 3607385423909429488215973)
                      ·
                        rfl

theorem cell23_7025358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_7025358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025358 prefixEnd_7025358 := by exact prefixLift 7025358
  have htrace : WordTrace (prefixWord ++ tailWord_7025358) baseStart_7025358 baseEnd_7025358 := by
    simpa [prefixWord, tailWord_7025358, baseEnd_7025358] using wordTrace_append hprefix tailTrace_7025358
  have hstable : (prefixWord ++ tailWord_7025358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025358).length < 2 ^ (prefixWord ++ tailWord_7025358).sum := by decide
  have hdescent : baseEnd_7025358 < baseStart_7025358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025377 : List Nat := [1, 2, 3, 1, 4, 2, 10]
def baseStart_7025377 : Nat := 118140960795 + 7025377 * 2 ^ 59
def prefixEnd_7025377 : Nat := 4983230072969 + 3 ^ 40 * 7025377 * 2
def baseEnd_7025377 : Nat := 44535742963479813751585

theorem tailTrace_7025377 : CollatzResearch.WordTrace tailWord_7025377 prefixEnd_7025377 44535742963479813751585 := by
  unfold tailWord_7025377
  simp only [CollatzResearch.WordTrace]
  refine ⟨256236549869266442712658385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170824366579510961808438923 256236549869266442712658385)
  ·
    refine ⟨192177412401949832034493789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256236549869266442712658385 192177412401949832034493789)
    ·
      refine ⟨72066529650731187012935171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192177412401949832034493789 72066529650731187012935171)
      ·
        refine ⟨108099794476096780519402757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72066529650731187012935171 108099794476096780519402757)
        ·
          refine ⟨20268711464268146347388017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108099794476096780519402757 20268711464268146347388017)
          ·
            refine ⟨15201533598201109760541013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20268711464268146347388017 15201533598201109760541013)
            ·
              refine ⟨44535742963479813751585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15201533598201109760541013 44535742963479813751585)
              ·
                rfl

theorem cell23_7025377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 10].length) (baseStart_7025377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025377 prefixEnd_7025377 := by exact prefixLift 7025377
  have htrace : WordTrace (prefixWord ++ tailWord_7025377) baseStart_7025377 baseEnd_7025377 := by
    simpa [prefixWord, tailWord_7025377, baseEnd_7025377] using wordTrace_append hprefix tailTrace_7025377
  have hstable : (prefixWord ++ tailWord_7025377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025377).length < 2 ^ (prefixWord ++ tailWord_7025377).sum := by decide
  have hdescent : baseEnd_7025377 < baseStart_7025377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025381 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 2, 4]
def baseStart_7025381 : Nat := 118140960795 + 7025381 * 2 ^ 59
def prefixEnd_7025381 : Nat := 4983230072969 + 3 ^ 40 * 7025381 * 2
def baseEnd_7025381 : Nat := 1202465744654827632742789

theorem tailTrace_7025381 : CollatzResearch.WordTrace tailWord_7025381 prefixEnd_7025381 1202465744654827632742789 := by
  unfold tailWord_7025381
  simp only [CollatzResearch.WordTrace]
  refine ⟨256236695761251951395803997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170824463840834634263869331 256236695761251951395803997)
  ·
    refine ⟨96088760910469481773426499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256236695761251951395803997 96088760910469481773426499)
    ·
      refine ⟨144133141365704222660139749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96088760910469481773426499 144133141365704222660139749)
      ·
        refine ⟨27024964006069541748776203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144133141365704222660139749 27024964006069541748776203)
        ·
          refine ⟨40537446009104312623164305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27024964006069541748776203 40537446009104312623164305)
          ·
            refine ⟨30403084506828234467373229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40537446009104312623164305 30403084506828234467373229)
            ·
              refine ⟨11401156690060587925264961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30403084506828234467373229 11401156690060587925264961)
              ·
                refine ⟨8550867517545440943948721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11401156690060587925264961 8550867517545440943948721)
                ·
                  refine ⟨6413150638159080707961541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8550867517545440943948721 6413150638159080707961541)
                  ·
                    refine ⟨1202465744654827632742789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6413150638159080707961541 1202465744654827632742789)
                    ·
                      rfl

theorem cell23_7025381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_7025381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025381 prefixEnd_7025381 := by exact prefixLift 7025381
  have htrace : WordTrace (prefixWord ++ tailWord_7025381) baseStart_7025381 baseEnd_7025381 := by
    simpa [prefixWord, tailWord_7025381, baseEnd_7025381] using wordTrace_append hprefix tailTrace_7025381
  have hstable : (prefixWord ++ tailWord_7025381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025381).length < 2 ^ (prefixWord ++ tailWord_7025381).sum := by decide
  have hdescent : baseEnd_7025381 < baseStart_7025381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025398 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_7025398 : Nat := 118140960795 + 7025398 * 2 ^ 59
def prefixEnd_7025398 : Nat := 4983230072969 + 3 ^ 40 * 7025398 * 2
def baseEnd_7025398 : Nat := 1202468654378536443905263

theorem tailTrace_7025398 : CollatzResearch.WordTrace tailWord_7025398 prefixEnd_7025398 1202468654378536443905263 := by
  unfold tailWord_7025398
  simp only [CollatzResearch.WordTrace]
  refine ⟨16014832237636897706198303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170824877201460242199448565 16014832237636897706198303)
  ·
    refine ⟨24022248356455346559297455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16014832237636897706198303 24022248356455346559297455)
    ·
      refine ⟨36033372534683019838946183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24022248356455346559297455 36033372534683019838946183)
      ·
        refine ⟨54050058802024529758419275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36033372534683019838946183 54050058802024529758419275)
        ·
          refine ⟨81075088203036794637628913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54050058802024529758419275 81075088203036794637628913)
          ·
            refine ⟨60806316152277595978221685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81075088203036794637628913 60806316152277595978221685)
            ·
              refine ⟨5700592139276024622958283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60806316152277595978221685 5700592139276024622958283)
              ·
                refine ⟨8550888208914036934437425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5700592139276024622958283 8550888208914036934437425)
                ·
                  refine ⟨6413166156685527700828069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8550888208914036934437425 6413166156685527700828069)
                  ·
                    refine ⟨1202468654378536443905263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6413166156685527700828069 1202468654378536443905263)
                    ·
                      rfl

theorem cell23_7025398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_7025398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025398 prefixEnd_7025398 := by exact prefixLift 7025398
  have htrace : WordTrace (prefixWord ++ tailWord_7025398) baseStart_7025398 baseEnd_7025398 := by
    simpa [prefixWord, tailWord_7025398, baseEnd_7025398] using wordTrace_append hprefix tailTrace_7025398
  have hstable : (prefixWord ++ tailWord_7025398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025398).length < 2 ^ (prefixWord ++ tailWord_7025398).sum := by decide
  have hdescent : baseEnd_7025398 < baseStart_7025398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025417 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 5]
def baseStart_7025417 : Nat := 118140960795 + 7025417 * 2 ^ 59
def prefixEnd_7025417 : Nat := 4983230072969 + 3 ^ 40 * 7025417 * 2
def baseEnd_7025417 : Nat := 3607415719268044757378201

theorem tailTrace_7025417 : CollatzResearch.WordTrace tailWord_7025417 prefixEnd_7025417 3607415719268044757378201 := by
  unfold tailWord_7025417
  simp only [CollatzResearch.WordTrace]
  refine ⟨256238008789121529544114505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170825339192747686362743003 256238008789121529544114505)
  ·
    refine ⟨192178506591841147158085879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256238008789121529544114505 192178506591841147158085879)
    ·
      refine ⟨288267759887761720737128819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192178506591841147158085879 288267759887761720737128819)
      ·
        refine ⟨432401639831642581105693229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288267759887761720737128819 432401639831642581105693229)
        ·
          refine ⟨162150614936865967914634961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432401639831642581105693229 162150614936865967914634961)
          ·
            refine ⟨121612961202649475935976221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162150614936865967914634961 121612961202649475935976221)
            ·
              refine ⟨45604860450993553475991083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121612961202649475935976221 45604860450993553475991083)
              ·
                refine ⟨68407290676490330213986625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45604860450993553475991083 68407290676490330213986625)
                ·
                  refine ⟨51305468007367747660489969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68407290676490330213986625 51305468007367747660489969)
                  ·
                    refine ⟨38479101005525810745367477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51305468007367747660489969 38479101005525810745367477)
                    ·
                      refine ⟨3607415719268044757378201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38479101005525810745367477 3607415719268044757378201)
                      ·
                        rfl

theorem cell23_7025417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_7025417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025417 prefixEnd_7025417 := by exact prefixLift 7025417
  have htrace : WordTrace (prefixWord ++ tailWord_7025417) baseStart_7025417 baseEnd_7025417 := by
    simpa [prefixWord, tailWord_7025417, baseEnd_7025417] using wordTrace_append hprefix tailTrace_7025417
  have hstable : (prefixWord ++ tailWord_7025417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025417).length < 2 ^ (prefixWord ++ tailWord_7025417).sum := by decide
  have hdescent : baseEnd_7025417 < baseStart_7025417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025477 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_7025477 : Nat := 118140960795 + 7025477 * 2 ^ 59
def prefixEnd_7025477 : Nat := 4983230072969 + 3 ^ 40 * 7025477 * 2
def baseEnd_7025477 : Nat := 3607446528107314522627925

theorem tailTrace_7025477 : CollatzResearch.WordTrace tailWord_7025477 prefixEnd_7025477 3607446528107314522627925 := by
  unfold tailWord_7025477
  simp only [CollatzResearch.WordTrace]
  refine ⟨256240197168904159791298685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170826798112602773194199123 256240197168904159791298685)
  ·
    refine ⟨96090073938339059921737007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256240197168904159791298685 96090073938339059921737007)
    ·
      refine ⟨144135110907508589882605511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96090073938339059921737007 144135110907508589882605511)
      ·
        refine ⟨216202666361262884823908267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144135110907508589882605511 216202666361262884823908267)
        ·
          refine ⟨324303999541894327235862401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216202666361262884823908267 324303999541894327235862401)
          ·
            refine ⟨243227999656420745426896801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324303999541894327235862401 243227999656420745426896801)
            ·
              refine ⟨182420999742315559070172601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243227999656420745426896801 182420999742315559070172601)
              ·
                refine ⟨136815749806736669302629451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182420999742315559070172601 136815749806736669302629451)
                ·
                  refine ⟨205223624710105003953944177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136815749806736669302629451 205223624710105003953944177)
                  ·
                    refine ⟨153917718532578752965458133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 205223624710105003953944177 153917718532578752965458133)
                    ·
                      refine ⟨3607446528107314522627925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153917718532578752965458133 3607446528107314522627925)
                      ·
                        rfl

theorem cell23_7025477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_7025477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025477 prefixEnd_7025477 := by exact prefixLift 7025477
  have htrace : WordTrace (prefixWord ++ tailWord_7025477) baseStart_7025477 baseEnd_7025477 := by
    simpa [prefixWord, tailWord_7025477, baseEnd_7025477] using wordTrace_append hprefix tailTrace_7025477
  have hstable : (prefixWord ++ tailWord_7025477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025477).length < 2 ^ (prefixWord ++ tailWord_7025477).sum := by decide
  have hdescent : baseEnd_7025477 < baseStart_7025477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025495 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 2, 2, 2]
def baseStart_7025495 : Nat := 118140960795 + 7025495 * 2 ^ 59
def prefixEnd_7025495 : Nat := 4983230072969 + 3 ^ 40 * 7025495 * 2
def baseEnd_7025495 : Nat := 3607455770759095452202843

theorem tailTrace_7025495 : CollatzResearch.WordTrace tailWord_7025495 prefixEnd_7025495 3607455770759095452202843 := by
  unfold tailWord_7025495
  simp only [CollatzResearch.WordTrace]
  refine ⟨256240853682838948865453939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170827235788559299243635959 256240853682838948865453939)
  ·
    refine ⟨384361280524258423298180909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256240853682838948865453939 384361280524258423298180909)
    ·
      refine ⟨144135480196596908736817841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384361280524258423298180909 144135480196596908736817841)
      ·
        refine ⟨108101610147447681552613381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144135480196596908736817841 108101610147447681552613381)
        ·
          refine ⟨20269051902646440291115009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108101610147447681552613381 20269051902646440291115009)
          ·
            refine ⟨15201788926984830218336257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20269051902646440291115009 15201788926984830218336257)
            ·
              refine ⟨11401341695238622663752193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15201788926984830218336257 11401341695238622663752193)
              ·
                refine ⟨8551006271428966997814145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11401341695238622663752193 8551006271428966997814145)
                ·
                  refine ⟨6413254703571725248360609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8551006271428966997814145 6413254703571725248360609)
                  ·
                    refine ⟨4809941027678793936270457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6413254703571725248360609 4809941027678793936270457)
                    ·
                      refine ⟨3607455770759095452202843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4809941027678793936270457 3607455770759095452202843)
                      ·
                        rfl

theorem cell23_7025495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_7025495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025495 prefixEnd_7025495 := by exact prefixLift 7025495
  have htrace : WordTrace (prefixWord ++ tailWord_7025495) baseStart_7025495 baseEnd_7025495 := by
    simpa [prefixWord, tailWord_7025495, baseEnd_7025495] using wordTrace_append hprefix tailTrace_7025495
  have hstable : (prefixWord ++ tailWord_7025495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025495).length < 2 ^ (prefixWord ++ tailWord_7025495).sum := by decide
  have hdescent : baseEnd_7025495 < baseStart_7025495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025511 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_7025511 : Nat := 118140960795 + 7025511 * 2 ^ 59
def prefixEnd_7025511 : Nat := 4983230072969 + 3 ^ 40 * 7025511 * 2
def baseEnd_7025511 : Nat := 3607463986449567389602769

theorem tailTrace_7025511 : CollatzResearch.WordTrace tailWord_7025511 prefixEnd_7025511 3607463986449567389602769 := by
  unfold tailWord_7025511
  simp only [CollatzResearch.WordTrace]
  refine ⟨256241437250780983598036387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170827624833853989065357591 256241437250780983598036387)
  ·
    refine ⟨384362155876171475397054581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256241437250780983598036387 384362155876171475397054581)
    ·
      refine ⟨36033952113391075818473867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 384362155876171475397054581 36033952113391075818473867)
      ·
        refine ⟨54050928170086613727710801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36033952113391075818473867 54050928170086613727710801)
        ·
          refine ⟨40538196127564960295783101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54050928170086613727710801 40538196127564960295783101)
          ·
            refine ⟨15201823547836860110918663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40538196127564960295783101 15201823547836860110918663)
            ·
              refine ⟨22802735321755290166377995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15201823547836860110918663 22802735321755290166377995)
              ·
                refine ⟨34204102982632935249566993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22802735321755290166377995 34204102982632935249566993)
                ·
                  refine ⟨25653077236974701437175245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34204102982632935249566993 25653077236974701437175245)
                  ·
                    refine ⟨9619903963865513038940717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25653077236974701437175245 9619903963865513038940717)
                    ·
                      refine ⟨3607463986449567389602769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9619903963865513038940717 3607463986449567389602769)
                      ·
                        rfl

theorem cell23_7025511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_7025511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025511 prefixEnd_7025511 := by exact prefixLift 7025511
  have htrace : WordTrace (prefixWord ++ tailWord_7025511) baseStart_7025511 baseEnd_7025511 := by
    simpa [prefixWord, tailWord_7025511, baseEnd_7025511] using wordTrace_append hprefix tailTrace_7025511
  have hstable : (prefixWord ++ tailWord_7025511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025511).length < 2 ^ (prefixWord ++ tailWord_7025511).sum := by decide
  have hdescent : baseEnd_7025511 < baseStart_7025511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025644 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_7025644 : Nat := 118140960795 + 7025644 * 2 ^ 59
def prefixEnd_7025644 : Nat := 4983230072969 + 3 ^ 40 * 7025644 * 2
def baseEnd_7025644 : Nat := 3607532279376615369239657

theorem tailTrace_7025644 : CollatzResearch.WordTrace tailWord_7025644 prefixEnd_7025644 3607532279376615369239657 := by
  unfold tailWord_7025644
  simp only [CollatzResearch.WordTrace]
  refine ⟨128123144079649573656313993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170830858772866098208418657 128123144079649573656313993)
  ·
    refine ⟨96092358059737180242235495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128123144079649573656313993 96092358059737180242235495)
    ·
      refine ⟨144138537089605770363353243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96092358059737180242235495 144138537089605770363353243)
      ·
        refine ⟨216207805634408655545029865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144138537089605770363353243 216207805634408655545029865)
        ·
          refine ⟨162155854225806491658772399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216207805634408655545029865 162155854225806491658772399)
          ·
            refine ⟨243233781338709737488158599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162155854225806491658772399 243233781338709737488158599)
            ·
              refine ⟨364850672008064606232237899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243233781338709737488158599 364850672008064606232237899)
              ·
                refine ⟨547276008012096909348356849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364850672008064606232237899 547276008012096909348356849)
                ·
                  refine ⟨410457006009072682011267637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547276008012096909348356849 410457006009072682011267637)
                  ·
                    refine ⟨38480344313350563938556341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 410457006009072682011267637 38480344313350563938556341)
                    ·
                      refine ⟨3607532279376615369239657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38480344313350563938556341 3607532279376615369239657)
                      ·
                        rfl

theorem cell23_7025644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_7025644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025644 prefixEnd_7025644 := by exact prefixLift 7025644
  have htrace : WordTrace (prefixWord ++ tailWord_7025644) baseStart_7025644 baseEnd_7025644 := by
    simpa [prefixWord, tailWord_7025644, baseEnd_7025644] using wordTrace_append hprefix tailTrace_7025644
  have hstable : (prefixWord ++ tailWord_7025644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025644).length < 2 ^ (prefixWord ++ tailWord_7025644).sum := by decide
  have hdescent : baseEnd_7025644 < baseStart_7025644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025671 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_7025671 : Nat := 118140960795 + 7025671 * 2 ^ 59
def prefixEnd_7025671 : Nat := 4983230072969 + 3 ^ 40 * 7025671 * 2
def baseEnd_7025671 : Nat := 3607546143354286763602033

theorem tailTrace_7025671 : CollatzResearch.WordTrace tailWord_7025671 prefixEnd_7025671 3607546143354286763602033 := by
  unfold tailWord_7025671
  simp only [CollatzResearch.WordTrace]
  refine ⟨256247272930201330923860867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170831515286800887282573911 256247272930201330923860867)
  ·
    refine ⟨384370909395301996385791301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256247272930201330923860867 384370909395301996385791301)
    ·
      refine ⟨72069545511619124322335869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384370909395301996385791301 72069545511619124322335869)
      ·
        refine ⟨27026079566857171620875951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72069545511619124322335869 27026079566857171620875951)
        ·
          refine ⟨40539119350285757431313927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27026079566857171620875951 40539119350285757431313927)
          ·
            refine ⟨60808679025428636146970891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40539119350285757431313927 60808679025428636146970891)
            ·
              refine ⟨91213018538142954220456337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60808679025428636146970891 91213018538142954220456337)
              ·
                refine ⟨68409763903607215665342253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91213018538142954220456337 68409763903607215665342253)
                ·
                  refine ⟨25653661463852705874503345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68409763903607215665342253 25653661463852705874503345)
                  ·
                    refine ⟨19240246097889529405877509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25653661463852705874503345 19240246097889529405877509)
                    ·
                      refine ⟨3607546143354286763602033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19240246097889529405877509 3607546143354286763602033)
                      ·
                        rfl

theorem cell23_7025671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_7025671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025671 prefixEnd_7025671 := by exact prefixLift 7025671
  have htrace : WordTrace (prefixWord ++ tailWord_7025671) baseStart_7025671 baseEnd_7025671 := by
    simpa [prefixWord, tailWord_7025671, baseEnd_7025671] using wordTrace_append hprefix tailTrace_7025671
  have hstable : (prefixWord ++ tailWord_7025671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025671).length < 2 ^ (prefixWord ++ tailWord_7025671).sum := by decide
  have hdescent : baseEnd_7025671 < baseStart_7025671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025678 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_7025678 : Nat := 118140960795 + 7025678 * 2 ^ 59
def prefixEnd_7025678 : Nat := 4983230072969 + 3 ^ 40 * 7025678 * 2
def baseEnd_7025678 : Nat := 3607549737718868236214501

theorem tailTrace_7025678 : CollatzResearch.WordTrace tailWord_7025678 prefixEnd_7025678 3607549737718868236214501 := by
  unfold tailWord_7025678
  simp only [CollatzResearch.WordTrace]
  refine ⟨32030941030146996389920711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170831685494117314079577125 32030941030146996389920711)
  ·
    refine ⟨48046411545220494584881067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32030941030146996389920711 48046411545220494584881067)
    ·
      refine ⟨72069617317830741877321601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48046411545220494584881067 72069617317830741877321601)
      ·
        refine ⟨54052212988373056407991201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72069617317830741877321601 54052212988373056407991201)
        ·
          refine ⟨40539159741279792305993401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54052212988373056407991201 40539159741279792305993401)
          ·
            refine ⟨30404369805959844229495051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40539159741279792305993401 30404369805959844229495051)
            ·
              refine ⟨45606554708939766344242577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30404369805959844229495051 45606554708939766344242577)
              ·
                refine ⟨34204916031704824758181933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45606554708939766344242577 34204916031704824758181933)
                ·
                  refine ⟨12826843511889309284318225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34204916031704824758181933 12826843511889309284318225)
                  ·
                    refine ⟨9620132633916981963238669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12826843511889309284318225 9620132633916981963238669)
                    ·
                      refine ⟨3607549737718868236214501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9620132633916981963238669 3607549737718868236214501)
                      ·
                        rfl

theorem cell23_7025678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_7025678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025678 prefixEnd_7025678 := by exact prefixLift 7025678
  have htrace : WordTrace (prefixWord ++ tailWord_7025678) baseStart_7025678 baseEnd_7025678 := by
    simpa [prefixWord, tailWord_7025678, baseEnd_7025678] using wordTrace_append hprefix tailTrace_7025678
  have hstable : (prefixWord ++ tailWord_7025678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025678).length < 2 ^ (prefixWord ++ tailWord_7025678).sum := by decide
  have hdescent : baseEnd_7025678 < baseStart_7025678 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025688 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 1, 2, 4]
def baseStart_7025688 : Nat := 118140960795 + 7025688 * 2 ^ 59
def prefixEnd_7025688 : Nat := 4983230072969 + 3 ^ 40 * 7025688 * 2
def baseEnd_7025688 : Nat := 3607554872525413197089455

theorem tailTrace_7025688 : CollatzResearch.WordTrace tailWord_7025688 prefixEnd_7025688 3607554872525413197089455 := by
  unfold tailWord_7025688
  simp only [CollatzResearch.WordTrace]
  refine ⟨128123946485569871413614859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170831928647426495218153145 128123946485569871413614859)
  ·
    refine ⟨192185919728354807120422289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128123946485569871413614859 192185919728354807120422289)
    ·
      refine ⟨144139439796266105340316717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192185919728354807120422289 144139439796266105340316717)
      ·
        refine ⟨54052289923599789502618769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144139439796266105340316717 54052289923599789502618769)
        ·
          refine ⟨40539217442699842126964077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54052289923599789502618769 40539217442699842126964077)
          ·
            refine ⟨15202206541012440797611529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40539217442699842126964077 15202206541012440797611529)
            ·
              refine ⟨11401654905759330598208647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15202206541012440797611529 11401654905759330598208647)
              ·
                refine ⟨17102482358638995897312971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11401654905759330598208647 17102482358638995897312971)
                ·
                  refine ⟨25653723537958493845969457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17102482358638995897312971 25653723537958493845969457)
                  ·
                    refine ⟨19240292653468870384477093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25653723537958493845969457 19240292653468870384477093)
                    ·
                      refine ⟨3607554872525413197089455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19240292653468870384477093 3607554872525413197089455)
                      ·
                        rfl

theorem cell23_7025688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_7025688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025688 prefixEnd_7025688 := by exact prefixLift 7025688
  have htrace : WordTrace (prefixWord ++ tailWord_7025688) baseStart_7025688 baseEnd_7025688 := by
    simpa [prefixWord, tailWord_7025688, baseEnd_7025688] using wordTrace_append hprefix tailTrace_7025688
  have hstable : (prefixWord ++ tailWord_7025688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025688).length < 2 ^ (prefixWord ++ tailWord_7025688).sum := by decide
  have hdescent : baseEnd_7025688 < baseStart_7025688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025692 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_7025692 : Nat := 118140960795 + 7025692 * 2 ^ 59
def prefixEnd_7025692 : Nat := 4983230072969 + 3 ^ 40 * 7025692 * 2
def baseEnd_7025692 : Nat := 3607556926448031181439437

theorem tailTrace_7025692 : CollatzResearch.WordTrace tailWord_7025692 prefixEnd_7025692 3607556926448031181439437 := by
  unfold tailWord_7025692
  simp only [CollatzResearch.WordTrace]
  refine ⟨128124019431562625755187665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170832025908750167673583553 128124019431562625755187665)
  ·
    refine ⟨96093014573671969316390749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128124019431562625755187665 96093014573671969316390749)
    ·
      refine ⟨36034880465126988493646531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96093014573671969316390749 36034880465126988493646531)
      ·
        refine ⟨54052320697690482740469797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36034880465126988493646531 54052320697690482740469797)
        ·
          refine ⟨10134810130816965513838087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54052320697690482740469797 10134810130816965513838087)
          ·
            refine ⟨15202215196225448270757131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10134810130816965513838087 15202215196225448270757131)
            ·
              refine ⟨22803322794338172406135697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15202215196225448270757131 22803322794338172406135697)
              ·
                refine ⟨17102492095753629304601773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22803322794338172406135697 17102492095753629304601773)
                ·
                  refine ⟨6413434535907610989225665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17102492095753629304601773 6413434535907610989225665)
                  ·
                    refine ⟨4810075901930708241919249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6413434535907610989225665 4810075901930708241919249)
                    ·
                      refine ⟨3607556926448031181439437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4810075901930708241919249 3607556926448031181439437)
                      ·
                        rfl

theorem cell23_7025692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_7025692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025692 prefixEnd_7025692 := by exact prefixLift 7025692
  have htrace : WordTrace (prefixWord ++ tailWord_7025692) baseStart_7025692 baseEnd_7025692 := by
    simpa [prefixWord, tailWord_7025692, baseEnd_7025692] using wordTrace_append hprefix tailTrace_7025692
  have hstable : (prefixWord ++ tailWord_7025692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025692).length < 2 ^ (prefixWord ++ tailWord_7025692).sum := by decide
  have hdescent : baseEnd_7025692 < baseStart_7025692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025698 : List Nat := [3, 3, 1, 1, 1, 4, 3, 7]
def baseStart_7025698 : Nat := 118140960795 + 7025698 * 2 ^ 59
def prefixEnd_7025698 : Nat := 4983230072969 + 3 ^ 40 * 7025698 * 2
def baseEnd_7025698 : Nat := 133613333604887339183867

theorem tailTrace_7025698 : CollatzResearch.WordTrace tailWord_7025698 prefixEnd_7025698 133613333604887339183867 := by
  unfold tailWord_7025698
  simp only [CollatzResearch.WordTrace]
  refine ⟨64062064425275878633773437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170832171800735676356729165 64062064425275878633773437)
  ·
    refine ⟨24023274159478454487665039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64062064425275878633773437 24023274159478454487665039)
    ·
      refine ⟨36034911239217681731497559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24023274159478454487665039 36034911239217681731497559)
      ·
        refine ⟨54052366858826522597246339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36034911239217681731497559 54052366858826522597246339)
        ·
          refine ⟨81078550288239783895869509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54052366858826522597246339 81078550288239783895869509)
          ·
            refine ⟨15202228179044959480475533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81078550288239783895869509 15202228179044959480475533)
            ·
              refine ⟨5700835567141859805178325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15202228179044959480475533 5700835567141859805178325)
              ·
                refine ⟨133613333604887339183867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5700835567141859805178325 133613333604887339183867)
                ·
                  rfl

theorem cell23_7025698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 7].length) (baseStart_7025698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025698 prefixEnd_7025698 := by exact prefixLift 7025698
  have htrace : WordTrace (prefixWord ++ tailWord_7025698) baseStart_7025698 baseEnd_7025698 := by
    simpa [prefixWord, tailWord_7025698, baseEnd_7025698] using wordTrace_append hprefix tailTrace_7025698
  have hstable : (prefixWord ++ tailWord_7025698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025698).length < 2 ^ (prefixWord ++ tailWord_7025698).sum := by decide
  have hdescent : baseEnd_7025698 < baseStart_7025698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025708 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 3]
def baseStart_7025708 : Nat := 118140960795 + 7025708 * 2 ^ 59
def prefixEnd_7025708 : Nat := 4983230072969 + 3 ^ 40 * 7025708 * 2
def baseEnd_7025708 : Nat := 3607565142138503118839363

theorem tailTrace_7025708 : CollatzResearch.WordTrace tailWord_7025708 prefixEnd_7025708 3607565142138503118839363 := by
  unfold tailWord_7025708
  simp only [CollatzResearch.WordTrace]
  refine ⟨128124311215533643121478889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170832414954044857495305185 128124311215533643121478889)
  ·
    refine ⟨96093233411650232341109167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128124311215533643121478889 96093233411650232341109167)
    ·
      refine ⟨144139850117475348511663751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96093233411650232341109167 144139850117475348511663751)
      ·
        refine ⟨216209775176213022767495627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144139850117475348511663751 216209775176213022767495627)
        ·
          refine ⟨324314662764319534151243441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216209775176213022767495627 324314662764319534151243441)
          ·
            refine ⟨243235997073239650613432581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324314662764319534151243441 243235997073239650613432581)
            ·
              refine ⟨45606749451232434490018609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243235997073239650613432581 45606749451232434490018609)
              ·
                refine ⟨34205062088424325867513957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45606749451232434490018609 34205062088424325867513957)
                ·
                  refine ⟨6413449141579561100158867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34205062088424325867513957 6413449141579561100158867)
                  ·
                    refine ⟨9620173712369341650238301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6413449141579561100158867 9620173712369341650238301)
                    ·
                      refine ⟨3607565142138503118839363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9620173712369341650238301 3607565142138503118839363)
                      ·
                        rfl

theorem cell23_7025708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_7025708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025708 prefixEnd_7025708 := by exact prefixLift 7025708
  have htrace : WordTrace (prefixWord ++ tailWord_7025708) baseStart_7025708 baseEnd_7025708 := by
    simpa [prefixWord, tailWord_7025708, baseEnd_7025708] using wordTrace_append hprefix tailTrace_7025708
  have hstable : (prefixWord ++ tailWord_7025708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025708).length < 2 ^ (prefixWord ++ tailWord_7025708).sum := by decide
  have hdescent : baseEnd_7025708 < baseStart_7025708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025725 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 4, 1, 3]
def baseStart_7025725 : Nat := 118140960795 + 7025725 * 2 ^ 59
def prefixEnd_7025725 : Nat := 4983230072969 + 3 ^ 40 * 7025725 * 2
def baseEnd_7025725 : Nat := 3607573871309629552326785

theorem tailTrace_7025725 : CollatzResearch.WordTrace tailWord_7025725 prefixEnd_7025725 3607573871309629552326785 := by
  unfold tailWord_7025725
  simp only [CollatzResearch.WordTrace]
  refine ⟨256249242472005698146326629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170832828314670465430884419 256249242472005698146326629)
  ·
    refine ⟨48046732963501068402436243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256249242472005698146326629 48046732963501068402436243)
    ·
      refine ⟨72070099445251602603654365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48046732963501068402436243 72070099445251602603654365)
      ·
        refine ⟨27026287291969350976370387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72070099445251602603654365 27026287291969350976370387)
        ·
          refine ⟨40539430937954026464555581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27026287291969350976370387 40539430937954026464555581)
          ·
            refine ⟨15202286601732759924208343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40539430937954026464555581 15202286601732759924208343)
            ·
              refine ⟨22803429902599139886312515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15202286601732759924208343 22803429902599139886312515)
              ·
                refine ⟨34205144853898709829468773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22803429902599139886312515 34205144853898709829468773)
                ·
                  refine ⟨6413464660106008093025395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34205144853898709829468773 6413464660106008093025395)
                  ·
                    refine ⟨9620196990159012139538093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6413464660106008093025395 9620196990159012139538093)
                    ·
                      refine ⟨3607573871309629552326785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9620196990159012139538093 3607573871309629552326785)
                      ·
                        rfl

theorem cell23_7025725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_7025725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025725 prefixEnd_7025725 := by exact prefixLift 7025725
  have htrace : WordTrace (prefixWord ++ tailWord_7025725) baseStart_7025725 baseEnd_7025725 := by
    simpa [prefixWord, tailWord_7025725, baseEnd_7025725] using wordTrace_append hprefix tailTrace_7025725
  have hstable : (prefixWord ++ tailWord_7025725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025725).length < 2 ^ (prefixWord ++ tailWord_7025725).sum := by decide
  have hdescent : baseEnd_7025725 < baseStart_7025725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025742 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3]
def baseStart_7025742 : Nat := 118140960795 + 7025742 * 2 ^ 59
def prefixEnd_7025742 : Nat := 4983230072969 + 3 ^ 40 * 7025742 * 2
def baseEnd_7025742 : Nat := 3607582600480755985814207

theorem tailTrace_7025742 : CollatzResearch.WordTrace tailWord_7025742 prefixEnd_7025742 3607582600480755985814207 := by
  unfold tailWord_7025742
  simp only [CollatzResearch.WordTrace]
  refine ⟨32031232814118013756211935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170833241675296073366463653 32031232814118013756211935)
  ·
    refine ⟨48046849221177020634317903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32031232814118013756211935 48046849221177020634317903)
    ·
      refine ⟨72070273831765530951476855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48046849221177020634317903 72070273831765530951476855)
      ·
        refine ⟨108105410747648296427215283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72070273831765530951476855 108105410747648296427215283)
        ·
          refine ⟨162158116121472444640822925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108105410747648296427215283 162158116121472444640822925)
          ·
            refine ⟨60809293545552166740308597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162158116121472444640822925 60809293545552166740308597)
            ·
              refine ⟨5700871269895515631903931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60809293545552166740308597 5700871269895515631903931)
              ·
                refine ⟨8551306904843273447855897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5700871269895515631903931 8551306904843273447855897)
                ·
                  refine ⟨6413480178632455085891923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8551306904843273447855897 6413480178632455085891923)
                  ·
                    refine ⟨9620220267948682628837885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6413480178632455085891923 9620220267948682628837885)
                    ·
                      refine ⟨3607582600480755985814207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9620220267948682628837885 3607582600480755985814207)
                      ·
                        rfl

theorem cell23_7025742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_7025742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025742 prefixEnd_7025742 := by exact prefixLift 7025742
  have htrace : WordTrace (prefixWord ++ tailWord_7025742) baseStart_7025742 baseEnd_7025742 := by
    simpa [prefixWord, tailWord_7025742, baseEnd_7025742] using wordTrace_append hprefix tailTrace_7025742
  have hstable : (prefixWord ++ tailWord_7025742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025742).length < 2 ^ (prefixWord ++ tailWord_7025742).sum := by decide
  have hdescent : baseEnd_7025742 < baseStart_7025742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025751 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_7025751 : Nat := 118140960795 + 7025751 * 2 ^ 59
def prefixEnd_7025751 : Nat := 4983230072969 + 3 ^ 40 * 7025751 * 2
def baseEnd_7025751 : Nat := 3607587221806646450601665

theorem tailTrace_7025751 : CollatzResearch.WordTrace tailWord_7025751 prefixEnd_7025751 3607587221806646450601665 := by
  unfold tailWord_7025751
  simp only [CollatzResearch.WordTrace]
  refine ⟨256250190769911504586773107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170833460513274336391182071 256250190769911504586773107)
  ·
    refine ⟨384375286154867256880159661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256250190769911504586773107 384375286154867256880159661)
    ·
      refine ⟨144140732308075221330059873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384375286154867256880159661 144140732308075221330059873)
      ·
        refine ⟨108105549231056415997544905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144140732308075221330059873 108105549231056415997544905)
        ·
          refine ⟨81079161923292311998158679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108105549231056415997544905 81079161923292311998158679)
          ·
            refine ⟨121618742884938467997238019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81079161923292311998158679 121618742884938467997238019)
            ·
              refine ⟨182428114327407701995857029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121618742884938467997238019 182428114327407701995857029)
              ·
                refine ⟨34205271436388944124223193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182428114327407701995857029 34205271436388944124223193)
                ·
                  refine ⟨25653953577291708093167395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34205271436388944124223193 25653953577291708093167395)
                  ·
                    refine ⟨38480930365937562139751093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25653953577291708093167395 38480930365937562139751093)
                    ·
                      refine ⟨3607587221806646450601665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38480930365937562139751093 3607587221806646450601665)
                      ·
                        rfl

theorem cell23_7025751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_7025751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025751 prefixEnd_7025751 := by exact prefixLift 7025751
  have htrace : WordTrace (prefixWord ++ tailWord_7025751) baseStart_7025751 baseEnd_7025751 := by
    simpa [prefixWord, tailWord_7025751, baseEnd_7025751] using wordTrace_append hprefix tailTrace_7025751
  have hstable : (prefixWord ++ tailWord_7025751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025751).length < 2 ^ (prefixWord ++ tailWord_7025751).sum := by decide
  have hdescent : baseEnd_7025751 < baseStart_7025751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025761 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_7025761 : Nat := 118140960795 + 7025761 * 2 ^ 59
def prefixEnd_7025761 : Nat := 4983230072969 + 3 ^ 40 * 7025761 * 2
def baseEnd_7025761 : Nat := 3607592356613191411476619

theorem tailTrace_7025761 : CollatzResearch.WordTrace tailWord_7025761 prefixEnd_7025761 3607592356613191411476619 := by
  unfold tailWord_7025761
  simp only [CollatzResearch.WordTrace]
  refine ⟨256250555499875276294637137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170833703666583517529758091 256250555499875276294637137)
  ·
    refine ⟨192187916624906457220977853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256250555499875276294637137 192187916624906457220977853)
    ·
      refine ⟨72070468734339921457866695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192187916624906457220977853 72070468734339921457866695)
      ·
        refine ⟨108105703101509882186800043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72070468734339921457866695 108105703101509882186800043)
        ·
          refine ⟨162158554652264823280200065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108105703101509882186800043 162158554652264823280200065)
          ·
            refine ⟨121618915989198617460150049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162158554652264823280200065 121618915989198617460150049)
            ·
              refine ⟨91214186991898963095112537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121618915989198617460150049 91214186991898963095112537)
              ·
                refine ⟨68410640243924222321334403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91214186991898963095112537 68410640243924222321334403)
                ·
                  refine ⟨102615960365886333482001605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68410640243924222321334403 102615960365886333482001605)
                  ·
                    refine ⟨19240492568603687527875301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102615960365886333482001605 19240492568603687527875301)
                    ·
                      refine ⟨3607592356613191411476619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19240492568603687527875301 3607592356613191411476619)
                      ·
                        rfl

theorem cell23_7025761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_7025761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025761 prefixEnd_7025761 := by exact prefixLift 7025761
  have htrace : WordTrace (prefixWord ++ tailWord_7025761) baseStart_7025761 baseEnd_7025761 := by
    simpa [prefixWord, tailWord_7025761, baseEnd_7025761] using wordTrace_append hprefix tailTrace_7025761
  have hstable : (prefixWord ++ tailWord_7025761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025761).length < 2 ^ (prefixWord ++ tailWord_7025761).sum := by decide
  have hdescent : baseEnd_7025761 < baseStart_7025761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025765 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 6, 2, 2]
def baseStart_7025765 : Nat := 118140960795 + 7025765 * 2 ^ 59
def prefixEnd_7025765 : Nat := 4983230072969 + 3 ^ 40 * 7025765 * 2
def baseEnd_7025765 : Nat := 3607594410535809395826601

theorem tailTrace_7025765 : CollatzResearch.WordTrace tailWord_7025765 prefixEnd_7025765 3607594410535809395826601 := by
  unfold tailWord_7025765
  simp only [CollatzResearch.WordTrace]
  refine ⟨256250701391860784977782749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170833800927907189985188499 256250701391860784977782749)
  ·
    refine ⟨96094013021947794366668531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256250701391860784977782749 96094013021947794366668531)
    ·
      refine ⟨144141019532921691550002797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96094013021947794366668531 144141019532921691550002797)
      ·
        refine ⟨54052882324845634331251049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144141019532921691550002797 54052882324845634331251049)
        ·
          refine ⟨40539661743634225748438287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54052882324845634331251049 40539661743634225748438287)
          ·
            refine ⟨60809492615451338622657431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40539661743634225748438287 60809492615451338622657431)
            ·
              refine ⟨91214238923177007933986147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60809492615451338622657431 91214238923177007933986147)
              ·
                refine ⟨136821358384765511900979221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91214238923177007933986147 136821358384765511900979221)
                ·
                  refine ⟨6413501174285883370358401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136821358384765511900979221 6413501174285883370358401)
                  ·
                    refine ⟨4810125880714412527768801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6413501174285883370358401 4810125880714412527768801)
                    ·
                      refine ⟨3607594410535809395826601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4810125880714412527768801 3607594410535809395826601)
                      ·
                        rfl

theorem cell23_7025765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_7025765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025765 prefixEnd_7025765 := by exact prefixLift 7025765
  have htrace : WordTrace (prefixWord ++ tailWord_7025765) baseStart_7025765 baseEnd_7025765 := by
    simpa [prefixWord, tailWord_7025765, baseEnd_7025765] using wordTrace_append hprefix tailTrace_7025765
  have hstable : (prefixWord ++ tailWord_7025765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025765).length < 2 ^ (prefixWord ++ tailWord_7025765).sum := by decide
  have hdescent : baseEnd_7025765 < baseStart_7025765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025782 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_7025782 : Nat := 118140960795 + 7025782 * 2 ^ 59
def prefixEnd_7025782 : Nat := 4983230072969 + 3 ^ 40 * 7025782 * 2
def baseEnd_7025782 : Nat := 3607603139706935829314023

theorem tailTrace_7025782 : CollatzResearch.WordTrace tailWord_7025782 prefixEnd_7025782 3607603139706935829314023 := by
  unfold tailWord_7025782
  simp only [CollatzResearch.WordTrace]
  refine ⟨16015707589549949805071975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170834214288532797920767733 16015707589549949805071975)
  ·
    refine ⟨24023561384324924707607963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16015707589549949805071975 24023561384324924707607963)
    ·
      refine ⟨36035342076487387061411945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24023561384324924707607963 36035342076487387061411945)
      ·
        refine ⟨27026506557365540296058959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36035342076487387061411945 27026506557365540296058959)
        ·
          refine ⟨40539759836048310444088439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27026506557365540296058959 40539759836048310444088439)
          ·
            refine ⟨60809639754072465666132659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40539759836048310444088439 60809639754072465666132659)
            ·
              refine ⟨91214459631108698499198989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60809639754072465666132659 91214459631108698499198989)
              ·
                refine ⟨34205422361665761937199621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91214459631108698499198989 34205422361665761937199621)
                ·
                  refine ⟨6413516692812330363224929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34205422361665761937199621 6413516692812330363224929)
                  ·
                    refine ⟨4810137519609247772418697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6413516692812330363224929 4810137519609247772418697)
                    ·
                      refine ⟨3607603139706935829314023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4810137519609247772418697 3607603139706935829314023)
                      ·
                        rfl

theorem cell23_7025782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_7025782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025782 prefixEnd_7025782 := by exact prefixLift 7025782
  have htrace : WordTrace (prefixWord ++ tailWord_7025782) baseStart_7025782 baseEnd_7025782 := by
    simpa [prefixWord, tailWord_7025782, baseEnd_7025782] using wordTrace_append hprefix tailTrace_7025782
  have hstable : (prefixWord ++ tailWord_7025782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025782).length < 2 ^ (prefixWord ++ tailWord_7025782).sum := by decide
  have hdescent : baseEnd_7025782 < baseStart_7025782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025808 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 4, 5, 2]
def baseStart_7025808 : Nat := 118140960795 + 7025808 * 2 ^ 59
def prefixEnd_7025808 : Nat := 4983230072969 + 3 ^ 40 * 7025808 * 2
def baseEnd_7025808 : Nat := 3607616490203952727588903

theorem tailTrace_7025808 : CollatzResearch.WordTrace tailWord_7025808 prefixEnd_7025808 3607616490203952727588903 := by
  unfold tailWord_7025808
  simp only [CollatzResearch.WordTrace]
  refine ⟨128126134865352501660799039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170834846487136668881065385 128126134865352501660799039)
  ·
    refine ⟨192189202298028752491198559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128126134865352501660799039 192189202298028752491198559)
    ·
      refine ⟨288283803447043128736797839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192189202298028752491198559 288283803447043128736797839)
      ·
        refine ⟨432425705170564693105196759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288283803447043128736797839 432425705170564693105196759)
        ·
          refine ⟨648638557755847039657795139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432425705170564693105196759 648638557755847039657795139)
          ·
            refine ⟨972957836633770559486692709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648638557755847039657795139 972957836633770559486692709)
            ·
              refine ⟨182429594368831979903754883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 972957836633770559486692709 182429594368831979903754883)
              ·
                refine ⟨273644391553247969855632325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182429594368831979903754883 273644391553247969855632325)
                ·
                  refine ⟨51308323416233994347931061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273644391553247969855632325 51308323416233994347931061)
                  ·
                    refine ⟨4810155320271936970118537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51308323416233994347931061 4810155320271936970118537)
                    ·
                      refine ⟨3607616490203952727588903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4810155320271936970118537 3607616490203952727588903)
                      ·
                        rfl

theorem cell23_7025808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 5, 2].length) (baseStart_7025808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025808 prefixEnd_7025808 := by exact prefixLift 7025808
  have htrace : WordTrace (prefixWord ++ tailWord_7025808) baseStart_7025808 baseEnd_7025808 := by
    simpa [prefixWord, tailWord_7025808, baseEnd_7025808] using wordTrace_append hprefix tailTrace_7025808
  have hstable : (prefixWord ++ tailWord_7025808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025808).length < 2 ^ (prefixWord ++ tailWord_7025808).sum := by decide
  have hdescent : baseEnd_7025808 < baseStart_7025808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025828 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_7025828 : Nat := 118140960795 + 7025828 * 2 ^ 59
def prefixEnd_7025828 : Nat := 4983230072969 + 3 ^ 40 * 7025828 * 2
def baseEnd_7025828 : Nat := 3607626759817042649338811

theorem tailTrace_7025828 : CollatzResearch.WordTrace tailWord_7025828 prefixEnd_7025828 3607626759817042649338811 := by
  unfold tailWord_7025828
  simp only [CollatzResearch.WordTrace]
  refine ⟨128126499595316273368663069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170835332793755031158217425 128126499595316273368663069)
  ·
    refine ⟨48047437348243602513248651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128126499595316273368663069 48047437348243602513248651)
    ·
      refine ⟨72071156022365403769872977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48047437348243602513248651 72071156022365403769872977)
      ·
        refine ⟨54053367016774052827404733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72071156022365403769872977 54053367016774052827404733)
        ·
          refine ⟨20270012631290269810276775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54053367016774052827404733 20270012631290269810276775)
          ·
            refine ⟨30405018946935404715415163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20270012631290269810276775 30405018946935404715415163)
            ·
              refine ⟨45607528420403107073122745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30405018946935404715415163 45607528420403107073122745)
              ·
                refine ⟨34205646315302330304842059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45607528420403107073122745 34205646315302330304842059)
                ·
                  refine ⟨51308469472953495457263089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34205646315302330304842059 51308469472953495457263089)
                  ·
                    refine ⟨38481352104715121592947317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51308469472953495457263089 38481352104715121592947317)
                    ·
                      refine ⟨3607626759817042649338811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38481352104715121592947317 3607626759817042649338811)
                      ·
                        rfl

theorem cell23_7025828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_7025828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025828 prefixEnd_7025828 := by exact prefixLift 7025828
  have htrace : WordTrace (prefixWord ++ tailWord_7025828) baseStart_7025828 baseEnd_7025828 := by
    simpa [prefixWord, tailWord_7025828, baseEnd_7025828] using wordTrace_append hprefix tailTrace_7025828
  have hstable : (prefixWord ++ tailWord_7025828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025828).length < 2 ^ (prefixWord ++ tailWord_7025828).sum := by decide
  have hdescent : baseEnd_7025828 < baseStart_7025828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025851 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 6]
def baseStart_7025851 : Nat := 118140960795 + 7025851 * 2 ^ 59
def prefixEnd_7025851 : Nat := 4983230072969 + 3 ^ 40 * 7025851 * 2
def baseEnd_7025851 : Nat := 3607638569872096059351205

theorem tailTrace_7025851 : CollatzResearch.WordTrace tailWord_7025851 prefixEnd_7025851 3607638569872096059351205 := by
  unfold tailWord_7025851
  simp only [CollatzResearch.WordTrace]
  refine ⟨256253838069549221665413407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170835892046366147776942271 256253838069549221665413407)
  ·
    refine ⟨384380757104323832498120111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256253838069549221665413407 384380757104323832498120111)
    ·
      refine ⟨576571135656485748747180167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384380757104323832498120111 576571135656485748747180167)
      ·
        refine ⟨864856703484728623120770251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576571135656485748747180167 864856703484728623120770251)
        ·
          refine ⟨1297285055227092934681155377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864856703484728623120770251 1297285055227092934681155377)
          ·
            refine ⟨972963791420319701010866533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297285055227092934681155377 972963791420319701010866533)
            ·
              refine ⟨182430710891309943939537475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 972963791420319701010866533 182430710891309943939537475)
              ·
                refine ⟨273646066336964915909306213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182430710891309943939537475 273646066336964915909306213)
                ·
                  refine ⟨51308637438180921732994915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273646066336964915909306213 51308637438180921732994915)
                  ·
                    refine ⟨76962956157271382599492373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51308637438180921732994915 76962956157271382599492373)
                    ·
                      refine ⟨3607638569872096059351205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76962956157271382599492373 3607638569872096059351205)
                      ·
                        rfl

theorem cell23_7025851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_7025851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025851 prefixEnd_7025851 := by exact prefixLift 7025851
  have htrace : WordTrace (prefixWord ++ tailWord_7025851) baseStart_7025851 baseEnd_7025851 := by
    simpa [prefixWord, tailWord_7025851, baseEnd_7025851] using wordTrace_append hprefix tailTrace_7025851
  have hstable : (prefixWord ++ tailWord_7025851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025851).length < 2 ^ (prefixWord ++ tailWord_7025851).sum := by decide
  have hdescent : baseEnd_7025851 < baseStart_7025851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025861 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 10]
def baseStart_7025861 : Nat := 118140960795 + 7025861 * 2 ^ 59
def prefixEnd_7025861 : Nat := 4983230072969 + 3 ^ 40 * 7025861 * 2
def baseEnd_7025861 : Nat := 400849300519849002247351

theorem tailTrace_7025861 : CollatzResearch.WordTrace tailWord_7025861 prefixEnd_7025861 400849300519849002247351 := by
  unfold tailWord_7025861
  simp only [CollatzResearch.WordTrace]
  refine ⟨256254202799512993373277437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170836135199675328915518291 256254202799512993373277437)
  ·
    refine ⟨96095326049817372514979039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256254202799512993373277437 96095326049817372514979039)
    ·
      refine ⟨144142989074726058772468559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96095326049817372514979039 144142989074726058772468559)
      ·
        refine ⟨216214483612089088158702839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144142989074726058772468559 216214483612089088158702839)
        ·
          refine ⟨324321725418133632238054259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216214483612089088158702839 324321725418133632238054259)
          ·
            refine ⟨486482588127200448357081389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324321725418133632238054259 486482588127200448357081389)
            ·
              refine ⟨182430970547700168133905521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 486482588127200448357081389 182430970547700168133905521)
              ·
                refine ⟨136823227910775126100429141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182430970547700168133905521 136823227910775126100429141)
                ·
                  refine ⟨400849300519849002247351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 136823227910775126100429141 400849300519849002247351)
                  ·
                    rfl

theorem cell23_7025861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_7025861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025861 prefixEnd_7025861 := by exact prefixLift 7025861
  have htrace : WordTrace (prefixWord ++ tailWord_7025861) baseStart_7025861 baseEnd_7025861 := by
    simpa [prefixWord, tailWord_7025861, baseEnd_7025861] using wordTrace_append hprefix tailTrace_7025861
  have hstable : (prefixWord ++ tailWord_7025861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025861).length < 2 ^ (prefixWord ++ tailWord_7025861).sum := by decide
  have hdescent : baseEnd_7025861 < baseStart_7025861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025895 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 8]
def baseStart_7025895 : Nat := 118140960795 + 7025895 * 2 ^ 59
def prefixEnd_7025895 : Nat := 4983230072969 + 3 ^ 40 * 7025895 * 2
def baseEnd_7025895 : Nat := 400851240335654876355667

theorem tailTrace_7025895 : CollatzResearch.WordTrace tailWord_7025895 prefixEnd_7025895 400851240335654876355667 := by
  unfold tailWord_7025895
  simp only [CollatzResearch.WordTrace]
  refine ⟨256255442881389817180015139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170836961920926544786676759 256255442881389817180015139)
  ·
    refine ⟨384383164322084725770022709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256255442881389817180015139 384383164322084725770022709)
    ·
      refine ⟨36035921655195443040939629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 384383164322084725770022709 36035921655195443040939629)
      ·
        refine ⟨13513470620698291140352361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36035921655195443040939629 13513470620698291140352361)
        ·
          refine ⟨10135102965523718355264271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13513470620698291140352361 10135102965523718355264271)
          ·
            refine ⟨15202654448285577532896407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10135102965523718355264271 15202654448285577532896407)
            ·
              refine ⟨22803981672428366299344611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15202654448285577532896407 22803981672428366299344611)
              ·
                refine ⟨34205972508642549449016917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22803981672428366299344611 34205972508642549449016917)
                ·
                  refine ⟨400851240335654876355667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34205972508642549449016917 400851240335654876355667)
                  ·
                    rfl

theorem cell23_7025895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 8].length) (baseStart_7025895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025895 prefixEnd_7025895 := by exact prefixLift 7025895
  have htrace : WordTrace (prefixWord ++ tailWord_7025895) baseStart_7025895 baseEnd_7025895 := by
    simpa [prefixWord, tailWord_7025895, baseEnd_7025895] using wordTrace_append hprefix tailTrace_7025895
  have hstable : (prefixWord ++ tailWord_7025895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025895).length < 2 ^ (prefixWord ++ tailWord_7025895).sum := by decide
  have hdescent : baseEnd_7025895 < baseStart_7025895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025898 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_7025898 : Nat := 118140960795 + 7025898 * 2 ^ 59
def prefixEnd_7025898 : Nat := 4983230072969 + 3 ^ 40 * 7025898 * 2
def baseEnd_7025898 : Nat := 3607662703462857375463489

theorem tailTrace_7025898 : CollatzResearch.WordTrace tailWord_7025898 prefixEnd_7025898 3607662703462857375463489 := by
  unfold tailWord_7025898
  simp only [CollatzResearch.WordTrace]
  refine ⟨64063888075094737173093587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170837034866919299128249565 64063888075094737173093587)
  ·
    refine ⟨96095832112642105759640381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64063888075094737173093587 96095832112642105759640381)
    ·
      refine ⟨36035937042240789659865143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96095832112642105759640381 36035937042240789659865143)
      ·
        refine ⟨54053905563361184489797715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36035937042240789659865143 54053905563361184489797715)
        ·
          refine ⟨81080858345041776734696573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54053905563361184489797715 81080858345041776734696573)
          ·
            refine ⟨30405321879390666275511215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81080858345041776734696573 30405321879390666275511215)
            ·
              refine ⟨45607982819085999413266823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30405321879390666275511215 45607982819085999413266823)
              ·
                refine ⟨68411974228628999119900235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45607982819085999413266823 68411974228628999119900235)
                ·
                  refine ⟨102617961342943498679850353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68411974228628999119900235 102617961342943498679850353)
                  ·
                    refine ⟨76963471007207624009887765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102617961342943498679850353 76963471007207624009887765)
                    ·
                      refine ⟨3607662703462857375463489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76963471007207624009887765 3607662703462857375463489)
                      ·
                        rfl

theorem cell23_7025898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_7025898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025898 prefixEnd_7025898 := by exact prefixLift 7025898
  have htrace : WordTrace (prefixWord ++ tailWord_7025898) baseStart_7025898 baseEnd_7025898 := by
    simpa [prefixWord, tailWord_7025898, baseEnd_7025898] using wordTrace_append hprefix tailTrace_7025898
  have hstable : (prefixWord ++ tailWord_7025898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025898).length < 2 ^ (prefixWord ++ tailWord_7025898).sum := by decide
  have hdescent : baseEnd_7025898 < baseStart_7025898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025925 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 1, 5]
def baseStart_7025925 : Nat := 118140960795 + 7025925 * 2 ^ 59
def prefixEnd_7025925 : Nat := 4983230072969 + 3 ^ 40 * 7025925 * 2
def baseEnd_7025925 : Nat := 1202558855813509589941955

theorem tailTrace_7025925 : CollatzResearch.WordTrace tailWord_7025925 prefixEnd_7025925 1202558855813509589941955 := by
  unfold tailWord_7025925
  simp only [CollatzResearch.WordTrace]
  refine ⟨256256537071281132303607229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170837691380854088202404819 256256537071281132303607229)
  ·
    refine ⟨96096201401730424613852711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256256537071281132303607229 96096201401730424613852711)
    ·
      refine ⟨144144302102595636920779067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96096201401730424613852711 144144302102595636920779067)
      ·
        refine ⟨216216453153893455381168601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144144302102595636920779067 216216453153893455381168601)
        ·
          refine ⟨162162339865420091535876451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216216453153893455381168601 162162339865420091535876451)
          ·
            refine ⟨243243509798130137303814677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162162339865420091535876451 243243509798130137303814677)
            ·
              refine ⟨11402039521787350186116313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 243243509798130137303814677 11402039521787350186116313)
              ·
                refine ⟨8551529641340512639587235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11402039521787350186116313 8551529641340512639587235)
                ·
                  refine ⟨12827294462010768959380853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8551529641340512639587235 12827294462010768959380853)
                  ·
                    refine ⟨1202558855813509589941955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12827294462010768959380853 1202558855813509589941955)
                    ·
                      rfl

theorem cell23_7025925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_7025925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025925 prefixEnd_7025925 := by exact prefixLift 7025925
  have htrace : WordTrace (prefixWord ++ tailWord_7025925) baseStart_7025925 baseEnd_7025925 := by
    simpa [prefixWord, tailWord_7025925, baseEnd_7025925] using wordTrace_append hprefix tailTrace_7025925
  have hstable : (prefixWord ++ tailWord_7025925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025925).length < 2 ^ (prefixWord ++ tailWord_7025925).sum := by decide
  have hdescent : baseEnd_7025925 < baseStart_7025925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025949 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 2, 3, 2]
def baseStart_7025949 : Nat := 118140960795 + 7025949 * 2 ^ 59
def prefixEnd_7025949 : Nat := 4983230072969 + 3 ^ 40 * 7025949 * 2
def baseEnd_7025949 : Nat := 3607688890976236675925755

theorem tailTrace_7025949 : CollatzResearch.WordTrace tailWord_7025949 prefixEnd_7025949 3607688890976236675925755 := by
  unfold tailWord_7025949
  simp only [CollatzResearch.WordTrace]
  refine ⟨256257412423194184402480901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170838274948796122934987267 256257412423194184402480901)
  ·
    refine ⟨48048264829348909575465169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256257412423194184402480901 48048264829348909575465169)
    ·
      refine ⟨36036198622011682181598877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48048264829348909575465169 36036198622011682181598877)
      ·
        refine ⟨13513574483254380818099579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36036198622011682181598877 13513574483254380818099579)
        ·
          refine ⟨20270361724881571227149369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13513574483254380818099579 20270361724881571227149369)
          ·
            refine ⟨15202771293661178420362027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20270361724881571227149369 15202771293661178420362027)
            ·
              refine ⟨22804156940491767630543041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15202771293661178420362027 22804156940491767630543041)
              ·
                refine ⟨17103117705368825722907281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22804156940491767630543041 17103117705368825722907281)
                ·
                  refine ⟨12827338279026619292180461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17103117705368825722907281 12827338279026619292180461)
                  ·
                    refine ⟨4810251854634982234567673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12827338279026619292180461 4810251854634982234567673)
                    ·
                      refine ⟨3607688890976236675925755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4810251854634982234567673 3607688890976236675925755)
                      ·
                        rfl

theorem cell23_7025949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_7025949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025949 prefixEnd_7025949 := by exact prefixLift 7025949
  have htrace : WordTrace (prefixWord ++ tailWord_7025949) baseStart_7025949 baseEnd_7025949 := by
    simpa [prefixWord, tailWord_7025949, baseEnd_7025949] using wordTrace_append hprefix tailTrace_7025949
  have hstable : (prefixWord ++ tailWord_7025949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025949).length < 2 ^ (prefixWord ++ tailWord_7025949).sum := by decide
  have hdescent : baseEnd_7025949 < baseStart_7025949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025955 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 4, 4]
def baseStart_7025955 : Nat := 118140960795 + 7025955 * 2 ^ 59
def prefixEnd_7025955 : Nat := 4983230072969 + 3 ^ 40 * 7025955 * 2
def baseEnd_7025955 : Nat := 1202563990620054550816909

theorem tailTrace_7025955 : CollatzResearch.WordTrace tailWord_7025955 prefixEnd_7025955 1202563990620054550816909 := by
  unfold tailWord_7025955
  simp only [CollatzResearch.WordTrace]
  refine ⟨256257631261172447427199319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170838420840781631618132879 256257631261172447427199319)
  ·
    refine ⟨384386446891758671140798979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256257631261172447427199319 384386446891758671140798979)
    ·
      refine ⟨576579670337638006711198469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384386446891758671140798979 576579670337638006711198469)
      ·
        refine ⟨108108688188307126258349713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 576579670337638006711198469 108108688188307126258349713)
        ·
          refine ⟨81081516141230344693762285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108108688188307126258349713 81081516141230344693762285)
          ·
            refine ⟨30405568552961379260160857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81081516141230344693762285 30405568552961379260160857)
            ·
              refine ⟨22804176414721034445120643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30405568552961379260160857 22804176414721034445120643)
              ·
                refine ⟨34206264622081551667680965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22804176414721034445120643 34206264622081551667680965)
                ·
                  refine ⟨6413674616640290937690181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34206264622081551667680965 6413674616640290937690181)
                  ·
                    refine ⟨1202563990620054550816909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6413674616640290937690181 1202563990620054550816909)
                    ·
                      rfl

theorem cell23_7025955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 4].length) (baseStart_7025955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025955 prefixEnd_7025955 := by exact prefixLift 7025955
  have htrace : WordTrace (prefixWord ++ tailWord_7025955) baseStart_7025955 baseEnd_7025955 := by
    simpa [prefixWord, tailWord_7025955, baseEnd_7025955] using wordTrace_append hprefix tailTrace_7025955
  have hstable : (prefixWord ++ tailWord_7025955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025955).length < 2 ^ (prefixWord ++ tailWord_7025955).sum := by decide
  have hdescent : baseEnd_7025955 < baseStart_7025955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025956 : List Nat := [2, 3, 1, 3, 1, 1, 5, 2, 1, 1, 3]
def baseStart_7025956 : Nat := 118140960795 + 7025956 * 2 ^ 59
def prefixEnd_7025956 : Nat := 4983230072969 + 3 ^ 40 * 7025956 * 2
def baseEnd_7025956 : Nat := 3607692485340818148538223

theorem tailTrace_7025956 : CollatzResearch.WordTrace tailWord_7025956 prefixEnd_7025956 3607692485340818148538223 := by
  unfold tailWord_7025956
  simp only [CollatzResearch.WordTrace]
  refine ⟨128128833867084412298992861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170838445156112549731990481 128128833867084412298992861)
  ·
    refine ⟨48048312700156654612122323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128128833867084412298992861 48048312700156654612122323)
    ·
      refine ⟨72072469050234981918183485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48048312700156654612122323 72072469050234981918183485)
      ·
        refine ⟨27027175893838118219318807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72072469050234981918183485 27027175893838118219318807)
        ·
          refine ⟨40540763840757177328978211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27027175893838118219318807 40540763840757177328978211)
          ·
            refine ⟨60811145761135765993467317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40540763840757177328978211 60811145761135765993467317)
            ·
              refine ⟨5701044915106478061887561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60811145761135765993467317 5701044915106478061887561)
              ·
                refine ⟨4275783686329858546415671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5701044915106478061887561 4275783686329858546415671)
                ·
                  refine ⟨6413675529494787819623507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4275783686329858546415671 6413675529494787819623507)
                  ·
                    refine ⟨9620513294242181729435261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6413675529494787819623507 9620513294242181729435261)
                    ·
                      refine ⟨3607692485340818148538223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9620513294242181729435261 3607692485340818148538223)
                      ·
                        rfl

theorem cell23_7025956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_7025956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025956 prefixEnd_7025956 := by exact prefixLift 7025956
  have htrace : WordTrace (prefixWord ++ tailWord_7025956) baseStart_7025956 baseEnd_7025956 := by
    simpa [prefixWord, tailWord_7025956, baseEnd_7025956] using wordTrace_append hprefix tailTrace_7025956
  have hstable : (prefixWord ++ tailWord_7025956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025956).length < 2 ^ (prefixWord ++ tailWord_7025956).sum := by decide
  have hdescent : baseEnd_7025956 < baseStart_7025956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025968 : List Nat := [2, 1, 1, 1, 2, 2, 6, 8]
def baseStart_7025968 : Nat := 118140960795 + 7025968 * 2 ^ 59
def prefixEnd_7025968 : Nat := 4983230072969 + 3 ^ 40 * 7025968 * 2
def baseEnd_7025968 : Nat := 133618468411432300058821

theorem tailTrace_7025968 : CollatzResearch.WordTrace tailWord_7025968 prefixEnd_7025968 133618468411432300058821 := by
  unfold tailWord_7025968
  simp only [CollatzResearch.WordTrace]
  refine ⟨128129052705062675323711279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170838736940083567098281705 128129052705062675323711279)
  ·
    refine ⟨192193579057594012985566919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128129052705062675323711279 192193579057594012985566919)
    ·
      refine ⟨288290368586391019478350379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192193579057594012985566919 288290368586391019478350379)
      ·
        refine ⟨432435552879586529217525569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288290368586391019478350379 432435552879586529217525569)
        ·
          refine ⟨324326664659689896913144177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 432435552879586529217525569 324326664659689896913144177)
          ·
            refine ⟨243244998494767422684858133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324326664659689896913144177 243244998494767422684858133)
            ·
              refine ⟨11402109304442222938352725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 243244998494767422684858133 11402109304442222938352725)
              ·
                refine ⟨133618468411432300058821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11402109304442222938352725 133618468411432300058821)
                ·
                  rfl

theorem cell23_7025968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 8].length) (baseStart_7025968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025968 prefixEnd_7025968 := by exact prefixLift 7025968
  have htrace : WordTrace (prefixWord ++ tailWord_7025968) baseStart_7025968 baseEnd_7025968 := by
    simpa [prefixWord, tailWord_7025968, baseEnd_7025968] using wordTrace_append hprefix tailTrace_7025968
  have hstable : (prefixWord ++ tailWord_7025968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025968).length < 2 ^ (prefixWord ++ tailWord_7025968).sum := by decide
  have hdescent : baseEnd_7025968 < baseStart_7025968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025982 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_7025982 : Nat := 118140960795 + 7025982 * 2 ^ 59
def prefixEnd_7025982 : Nat := 4983230072969 + 3 ^ 40 * 7025982 * 2
def baseEnd_7025982 : Nat := 3607705835837835046813103

theorem tailTrace_7025982 : CollatzResearch.WordTrace tailWord_7025982 prefixEnd_7025982 3607705835837835046813103 := by
  unfold tailWord_7025982
  simp only [CollatzResearch.WordTrace]
  refine ⟨32032327004009328879804025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170839077354716420692288133 32032327004009328879804025)
  ·
    refine ⟨24024245253006996659853019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32032327004009328879804025 24024245253006996659853019)
    ·
      refine ⟨36036367879510494989779529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24024245253006996659853019 36036367879510494989779529)
      ·
        refine ⟨27027275909632871242334647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36036367879510494989779529 27027275909632871242334647)
        ·
          refine ⟨40540913864449306863501971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27027275909632871242334647 40540913864449306863501971)
          ·
            refine ⟨60811370796673960295252957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40540913864449306863501971 60811370796673960295252957)
            ·
              refine ⟨22804264048752735110719859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60811370796673960295252957 22804264048752735110719859)
              ·
                refine ⟨34206396073129102666079789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22804264048752735110719859 34206396073129102666079789)
                ·
                  refine ⟨12827398527423413499779921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34206396073129102666079789 12827398527423413499779921)
                  ·
                    refine ⟨9620548895567560124834941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12827398527423413499779921 9620548895567560124834941)
                    ·
                      refine ⟨3607705835837835046813103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9620548895567560124834941 3607705835837835046813103)
                      ·
                        rfl

theorem cell23_7025982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_7025982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025982 prefixEnd_7025982 := by exact prefixLift 7025982
  have htrace : WordTrace (prefixWord ++ tailWord_7025982) baseStart_7025982 baseEnd_7025982 := by
    simpa [prefixWord, tailWord_7025982, baseEnd_7025982] using wordTrace_append hprefix tailTrace_7025982
  have hstable : (prefixWord ++ tailWord_7025982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025982).length < 2 ^ (prefixWord ++ tailWord_7025982).sum := by decide
  have hdescent : baseEnd_7025982 < baseStart_7025982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7025985 : List Nat := [1, 2, 5, 2, 1, 1, 2, 9]
def baseStart_7025985 : Nat := 118140960795 + 7025985 * 2 ^ 59
def prefixEnd_7025985 : Nat := 4983230072969 + 3 ^ 40 * 7025985 * 2
def baseEnd_7025985 : Nat := 133618791714066612410207

theorem tailTrace_7025985 : CollatzResearch.WordTrace tailWord_7025985 prefixEnd_7025985 133618791714066612410207 := by
  unfold tailWord_7025985
  simp only [CollatzResearch.WordTrace]
  refine ⟨256258725451063762550791409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170839150300709175033860939 256258725451063762550791409)
  ·
    refine ⟨192194044088297821913093557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256258725451063762550791409 192194044088297821913093557)
    ·
      refine ⟨18018191633277920804352521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192194044088297821913093557 18018191633277920804352521)
      ·
        refine ⟨13513643724958440603264391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18018191633277920804352521 13513643724958440603264391)
        ·
          refine ⟨20270465587437660904896587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13513643724958440603264391 20270465587437660904896587)
          ·
            refine ⟨30405698381156491357344881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20270465587437660904896587 30405698381156491357344881)
            ·
              refine ⟨22804273785867368518008661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30405698381156491357344881 22804273785867368518008661)
              ·
                refine ⟨133618791714066612410207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22804273785867368518008661 133618791714066612410207)
                ·
                  rfl

theorem cell23_7025985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 9].length) (baseStart_7025985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7025985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7025985 prefixEnd_7025985 := by exact prefixLift 7025985
  have htrace : WordTrace (prefixWord ++ tailWord_7025985) baseStart_7025985 baseEnd_7025985 := by
    simpa [prefixWord, tailWord_7025985, baseEnd_7025985] using wordTrace_append hprefix tailTrace_7025985
  have hstable : (prefixWord ++ tailWord_7025985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7025985).length < 2 ^ (prefixWord ++ tailWord_7025985).sum := by decide
  have hdescent : baseEnd_7025985 < baseStart_7025985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7025985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026029 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 2, 1, 3]
def baseStart_7026029 : Nat := 118140960795 + 7026029 * 2 ^ 59
def prefixEnd_7026029 : Nat := 4983230072969 + 3 ^ 40 * 7026029 * 2
def baseEnd_7026029 : Nat := 3607729969428596362925387

theorem tailTrace_7026029 : CollatzResearch.WordTrace tailWord_7026029 prefixEnd_7026029 3607729969428596362925387 := by
  unfold tailWord_7026029
  simp only [CollatzResearch.WordTrace]
  refine ⟨256260330262904358065393141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170840220175269572043595427 256260330262904358065393141)
  ·
    refine ⟨24024405962147283568630607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256260330262904358065393141 24024405962147283568630607)
    ·
      refine ⟨36036608943220925352945911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24024405962147283568630607 36036608943220925352945911)
      ·
        refine ⟨54054913414831388029418867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36036608943220925352945911 54054913414831388029418867)
        ·
          refine ⟨81082370122247082044128301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54054913414831388029418867 81082370122247082044128301)
          ·
            refine ⟨30405888795842655766548113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81082370122247082044128301 30405888795842655766548113)
            ·
              refine ⟨22804416596881991824911085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30405888795842655766548113 22804416596881991824911085)
              ·
                refine ⟨8551656223830746934341657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22804416596881991824911085 8551656223830746934341657)
                ·
                  refine ⟨6413742167873060200756243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8551656223830746934341657 6413742167873060200756243)
                  ·
                    refine ⟨9620613251809590301134365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6413742167873060200756243 9620613251809590301134365)
                    ·
                      refine ⟨3607729969428596362925387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9620613251809590301134365 3607729969428596362925387)
                      ·
                        rfl

theorem cell23_7026029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_7026029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026029 prefixEnd_7026029 := by exact prefixLift 7026029
  have htrace : WordTrace (prefixWord ++ tailWord_7026029) baseStart_7026029 baseEnd_7026029 := by
    simpa [prefixWord, tailWord_7026029, baseEnd_7026029] using wordTrace_append hprefix tailTrace_7026029
  have hstable : (prefixWord ++ tailWord_7026029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026029).length < 2 ^ (prefixWord ++ tailWord_7026029).sum := by decide
  have hdescent : baseEnd_7026029 < baseStart_7026029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026056 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 1, 3, 2]
def baseStart_7026056 : Nat := 118140960795 + 7026056 * 2 ^ 59
def prefixEnd_7026056 : Nat := 4983230072969 + 3 ^ 40 * 7026056 * 2
def baseEnd_7026056 : Nat := 3607743833406267757287763

theorem tailTrace_7026056 : CollatzResearch.WordTrace tailWord_7026056 prefixEnd_7026056 3607743833406267757287763 := by
  unfold tailWord_7026056
  simp only [CollatzResearch.WordTrace]
  refine ⟨128130657516903270838313011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170840876689204361117750681 128130657516903270838313011)
  ·
    refine ⟨192195986275354906257469517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128130657516903270838313011 192195986275354906257469517)
    ·
      refine ⟨72073494853258089846551069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192195986275354906257469517 72073494853258089846551069)
      ·
        refine ⟨27027560569971783692456651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72073494853258089846551069 27027560569971783692456651)
        ·
          refine ⟨40541340854957675538684977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27027560569971783692456651 40541340854957675538684977)
          ·
            refine ⟨30406005641218256654013733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40541340854957675538684977 30406005641218256654013733)
            ·
              refine ⟨5701126057728423122627575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30406005641218256654013733 5701126057728423122627575)
              ·
                refine ⟨8551689086592634683941363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5701126057728423122627575 8551689086592634683941363)
                ·
                  refine ⟨12827533629888952025912045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8551689086592634683941363 12827533629888952025912045)
                  ·
                    refine ⟨4810325111208357009717017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12827533629888952025912045 4810325111208357009717017)
                    ·
                      refine ⟨3607743833406267757287763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4810325111208357009717017 3607743833406267757287763)
                      ·
                        rfl

theorem cell23_7026056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_7026056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026056 prefixEnd_7026056 := by exact prefixLift 7026056
  have htrace : WordTrace (prefixWord ++ tailWord_7026056) baseStart_7026056 baseEnd_7026056 := by
    simpa [prefixWord, tailWord_7026056, baseEnd_7026056] using wordTrace_append hprefix tailTrace_7026056
  have hstable : (prefixWord ++ tailWord_7026056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026056).length < 2 ^ (prefixWord ++ tailWord_7026056).sum := by decide
  have hdescent : baseEnd_7026056 < baseStart_7026056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026082 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_7026082 : Nat := 118140960795 + 7026082 * 2 ^ 59
def prefixEnd_7026082 : Nat := 4983230072969 + 3 ^ 40 * 7026082 * 2
def baseEnd_7026082 : Nat := 3607757183903284655562643

theorem tailTrace_7026082 : CollatzResearch.WordTrace tailWord_7026082 prefixEnd_7026082 3607757183903284655562643 := by
  unfold tailWord_7026082
  simp only [CollatzResearch.WordTrace]
  refine ⟨64065565832928087029268125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170841508887808232078048333 64065565832928087029268125)
  ·
    refine ⟨24024587187348032635975547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64065565832928087029268125 24024587187348032635975547)
    ·
      refine ⟨36036880781022048953963321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24024587187348032635975547 36036880781022048953963321)
      ·
        refine ⟨27027660585766536715472491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36036880781022048953963321 27027660585766536715472491)
        ·
          refine ⟨40541490878649805073208737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27027660585766536715472491 40541490878649805073208737)
          ·
            refine ⟨30406118158987353804906553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40541490878649805073208737 30406118158987353804906553)
            ·
              refine ⟨22804588619240515353679915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30406118158987353804906553 22804588619240515353679915)
              ·
                refine ⟨34206882928860773030519873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22804588619240515353679915 34206882928860773030519873)
                ·
                  refine ⟨25655162196645579772889905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34206882928860773030519873 25655162196645579772889905)
                  ·
                    refine ⟨19241371647484184829667429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25655162196645579772889905 19241371647484184829667429)
                    ·
                      refine ⟨3607757183903284655562643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19241371647484184829667429 3607757183903284655562643)
                      ·
                        rfl

theorem cell23_7026082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_7026082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026082 prefixEnd_7026082 := by exact prefixLift 7026082
  have htrace : WordTrace (prefixWord ++ tailWord_7026082) baseStart_7026082 baseEnd_7026082 := by
    simpa [prefixWord, tailWord_7026082, baseEnd_7026082] using wordTrace_append hprefix tailTrace_7026082
  have hstable : (prefixWord ++ tailWord_7026082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026082).length < 2 ^ (prefixWord ++ tailWord_7026082).sum := by decide
  have hdescent : baseEnd_7026082 < baseStart_7026082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026085 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 1, 5, 3]
def baseStart_7026085 : Nat := 118140960795 + 7026085 * 2 ^ 59
def prefixEnd_7026085 : Nat := 4983230072969 + 3 ^ 40 * 7026085 * 2
def baseEnd_7026085 : Nat := 3607758724345248143825129

theorem tailTrace_7026085 : CollatzResearch.WordTrace tailWord_7026085 prefixEnd_7026085 3607758724345248143825129 := by
  unfold tailWord_7026085
  simp only [CollatzResearch.WordTrace]
  refine ⟨256262372750701479629431709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170841581833800986419621139 256262372750701479629431709)
  ·
    refine ⟨96098389781513054861036891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256262372750701479629431709 96098389781513054861036891)
    ·
      refine ⟨144147584672269582291555337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96098389781513054861036891 144147584672269582291555337)
      ·
        refine ⟨108110688504202186718666503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144147584672269582291555337 108110688504202186718666503)
        ·
          refine ⟨162166032756303280077999755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108110688504202186718666503 162166032756303280077999755)
          ·
            refine ⟨243249049134454920116999633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162166032756303280077999755 243249049134454920116999633)
            ·
              refine ⟨182436786850841190087749725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243249049134454920116999633 182436786850841190087749725)
              ·
                refine ⟨68413795069065446282906147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182436786850841190087749725 68413795069065446282906147)
                ·
                  refine ⟨102620692603598169424359221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68413795069065446282906147 102620692603598169424359221)
                  ·
                    refine ⟨9620689931587328383533677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102620692603598169424359221 9620689931587328383533677)
                    ·
                      refine ⟨3607758724345248143825129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9620689931587328383533677 3607758724345248143825129)
                      ·
                        rfl

theorem cell23_7026085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_7026085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026085 prefixEnd_7026085 := by exact prefixLift 7026085
  have htrace : WordTrace (prefixWord ++ tailWord_7026085) baseStart_7026085 baseEnd_7026085 := by
    simpa [prefixWord, tailWord_7026085, baseEnd_7026085] using wordTrace_append hprefix tailTrace_7026085
  have hstable : (prefixWord ++ tailWord_7026085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026085).length < 2 ^ (prefixWord ++ tailWord_7026085).sum := by decide
  have hdescent : baseEnd_7026085 < baseStart_7026085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026122 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_7026122 : Nat := 118140960795 + 7026122 * 2 ^ 59
def prefixEnd_7026122 : Nat := 4983230072969 + 3 ^ 40 * 7026122 * 2
def baseEnd_7026122 : Nat := 1202592574376488166354153

theorem tailTrace_7026122 : CollatzResearch.WordTrace tailWord_7026122 prefixEnd_7026122 1202592574376488166354153 := by
  unfold tailWord_7026122
  simp only [CollatzResearch.WordTrace]
  refine ⟨64065930562891858737132155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170842481501044956632352413 64065930562891858737132155)
  ·
    refine ⟨96098895844337788105698233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64065930562891858737132155 96098895844337788105698233)
    ·
      refine ⟨72074171883253341079273675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96098895844337788105698233 72074171883253341079273675)
      ·
        refine ⟨108111257824880011618910513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72074171883253341079273675 108111257824880011618910513)
        ·
          refine ⟨81083443368660008714182885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108111257824880011618910513 81083443368660008714182885)
          ·
            refine ⟨15203145631623751633909291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81083443368660008714182885 15203145631623751633909291)
            ·
              refine ⟨22804718447435627450863937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15203145631623751633909291 22804718447435627450863937)
              ·
                refine ⟨17103538835576720588147953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22804718447435627450863937 17103538835576720588147953)
                ·
                  refine ⟨12827654126682540441110965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17103538835576720588147953 12827654126682540441110965)
                  ·
                    refine ⟨1202592574376488166354153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12827654126682540441110965 1202592574376488166354153)
                    ·
                      rfl

theorem cell23_7026122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_7026122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026122 prefixEnd_7026122 := by exact prefixLift 7026122
  have htrace : WordTrace (prefixWord ++ tailWord_7026122) baseStart_7026122 baseEnd_7026122 := by
    simpa [prefixWord, tailWord_7026122, baseEnd_7026122] using wordTrace_append hprefix tailTrace_7026122
  have hstable : (prefixWord ++ tailWord_7026122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026122).length < 2 ^ (prefixWord ++ tailWord_7026122).sum := by decide
  have hdescent : baseEnd_7026122 < baseStart_7026122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026152 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 5, 4]
def baseStart_7026152 : Nat := 118140960795 + 7026152 * 2 ^ 59
def prefixEnd_7026152 : Nat := 4983230072969 + 3 ^ 40 * 7026152 * 2
def baseEnd_7026152 : Nat := 1202597709183033127229107

theorem tailTrace_7026152 : CollatzResearch.WordTrace tailWord_7026152 prefixEnd_7026152 1202597709183033127229107 := by
  unfold tailWord_7026152
  simp only [CollatzResearch.WordTrace]
  refine ⟨128132408220729375036060355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170843210960972500048080473 128132408220729375036060355)
  ·
    refine ⟨192198612331094062554090533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128132408220729375036060355 192198612331094062554090533)
    ·
      refine ⟨36037239812080136728891975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192198612331094062554090533 36037239812080136728891975)
      ·
        refine ⟨54055859718120205093337963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36037239812080136728891975 54055859718120205093337963)
        ·
          refine ⟨81083789577180307640006945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54055859718120205093337963 81083789577180307640006945)
          ·
            refine ⟨60812842182885230730005209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81083789577180307640006945 60812842182885230730005209)
            ·
              refine ⟨45609631637163923047503907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60812842182885230730005209 45609631637163923047503907)
              ·
                refine ⟨68414447455745884571255861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45609631637163923047503907 68414447455745884571255861)
                ·
                  refine ⟨6413854448976176678555237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68414447455745884571255861 6413854448976176678555237)
                  ·
                    refine ⟨1202597709183033127229107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6413854448976176678555237 1202597709183033127229107)
                    ·
                      rfl

theorem cell23_7026152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_7026152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026152 prefixEnd_7026152 := by exact prefixLift 7026152
  have htrace : WordTrace (prefixWord ++ tailWord_7026152) baseStart_7026152 baseEnd_7026152 := by
    simpa [prefixWord, tailWord_7026152, baseEnd_7026152] using wordTrace_append hprefix tailTrace_7026152
  have hstable : (prefixWord ++ tailWord_7026152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026152).length < 2 ^ (prefixWord ++ tailWord_7026152).sum := by decide
  have hdescent : baseEnd_7026152 < baseStart_7026152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026169 : List Nat := [1, 2, 1, 3, 1, 2, 1, 7, 1, 4]
def baseStart_7026169 : Nat := 118140960795 + 7026169 * 2 ^ 59
def prefixEnd_7026169 : Nat := 4983230072969 + 3 ^ 40 * 7026169 * 2
def baseEnd_7026169 : Nat := 1202600618906741938391581

theorem tailTrace_7026169 : CollatzResearch.WordTrace tailWord_7026169 prefixEnd_7026169 1202600618906741938391581 := by
  unfold tailWord_7026169
  simp only [CollatzResearch.WordTrace]
  refine ⟨256265436482397161975489561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170843624321598107983659707 256265436482397161975489561)
  ·
    refine ⟨192199077361797871481617171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256265436482397161975489561 192199077361797871481617171)
    ·
      refine ⟨288298616042696807222425757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192199077361797871481617171 288298616042696807222425757)
      ·
        refine ⟨108111981016011302708409659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288298616042696807222425757 108111981016011302708409659)
        ·
          refine ⟨162167971524016954062614489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108111981016011302708409659 162167971524016954062614489)
          ·
            refine ⟨121625978643012715546960867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162167971524016954062614489 121625978643012715546960867)
            ·
              refine ⟨182438967964519073320441301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121625978643012715546960867 182438967964519073320441301)
              ·
                refine ⟨4275913311668415780947843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 182438967964519073320441301 4275913311668415780947843)
                ·
                  refine ⟨6413869967502623671421765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4275913311668415780947843 6413869967502623671421765)
                  ·
                    refine ⟨1202600618906741938391581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6413869967502623671421765 1202600618906741938391581)
                    ·
                      rfl

theorem cell23_7026169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 1, 4].length) (baseStart_7026169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026169 prefixEnd_7026169 := by exact prefixLift 7026169
  have htrace : WordTrace (prefixWord ++ tailWord_7026169) baseStart_7026169 baseEnd_7026169 := by
    simpa [prefixWord, tailWord_7026169, baseEnd_7026169] using wordTrace_append hprefix tailTrace_7026169
  have hstable : (prefixWord ++ tailWord_7026169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026169).length < 2 ^ (prefixWord ++ tailWord_7026169).sum := by decide
  have hdescent : baseEnd_7026169 < baseStart_7026169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026185 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 6]
def baseStart_7026185 : Nat := 118140960795 + 7026185 * 2 ^ 59
def prefixEnd_7026185 : Nat := 4983230072969 + 3 ^ 40 * 7026185 * 2
def baseEnd_7026185 : Nat := 3607810072410697752574669

theorem tailTrace_7026185 : CollatzResearch.WordTrace tailWord_7026185 prefixEnd_7026185 3607810072410697752574669 := by
  unfold tailWord_7026185
  simp only [CollatzResearch.WordTrace]
  refine ⟨256266020050339196708072009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170844013366892797805381339 256266020050339196708072009)
  ·
    refine ⟨192199515037754397531054007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256266020050339196708072009 192199515037754397531054007)
    ·
      refine ⟨288299272556631596296581011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192199515037754397531054007 288299272556631596296581011)
      ·
        refine ⟨432448908834947394444871517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288299272556631596296581011 432448908834947394444871517)
        ·
          refine ⟨162168340813105272916826819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 432448908834947394444871517 162168340813105272916826819)
          ·
            refine ⟨243252511219657909375240229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162168340813105272916826819 243252511219657909375240229)
            ·
              refine ⟨45609845853685858007857543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 243252511219657909375240229 45609845853685858007857543)
              ·
                refine ⟨68414768780528787011786315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45609845853685858007857543 68414768780528787011786315)
                ·
                  refine ⟨102622153170793180517679473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68414768780528787011786315 102622153170793180517679473)
                  ·
                    refine ⟨76966614878094885388259605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102622153170793180517679473 76966614878094885388259605)
                    ·
                      refine ⟨3607810072410697752574669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76966614878094885388259605 3607810072410697752574669)
                      ·
                        rfl

theorem cell23_7026185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_7026185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026185 prefixEnd_7026185 := by exact prefixLift 7026185
  have htrace : WordTrace (prefixWord ++ tailWord_7026185) baseStart_7026185 baseEnd_7026185 := by
    simpa [prefixWord, tailWord_7026185, baseEnd_7026185] using wordTrace_append hprefix tailTrace_7026185
  have hstable : (prefixWord ++ tailWord_7026185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026185).length < 2 ^ (prefixWord ++ tailWord_7026185).sum := by decide
  have hdescent : baseEnd_7026185 < baseStart_7026185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026186 : List Nat := [3, 1, 2, 2, 2, 3, 1, 4, 1, 4]
def baseStart_7026186 : Nat := 118140960795 + 7026186 * 2 ^ 59
def prefixEnd_7026186 : Nat := 4983230072969 + 3 ^ 40 * 7026186 * 2
def baseEnd_7026186 : Nat := 1202603528630450749554055

theorem tailTrace_7026186 : CollatzResearch.WordTrace tailWord_7026186 prefixEnd_7026186 1202603528630450749554055 := by
  unfold tailWord_7026186
  simp only [CollatzResearch.WordTrace]
  refine ⟨64066514130833893469714603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170844037682223715919238941 64066514130833893469714603)
  ·
    refine ⟨96099771196250840204571905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64066514130833893469714603 96099771196250840204571905)
    ·
      refine ⟨72074828397188130153428929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96099771196250840204571905 72074828397188130153428929)
      ·
        refine ⟨54056121297891097615071697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72074828397188130153428929 54056121297891097615071697)
        ·
          refine ⟨40542090973418323211303773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54056121297891097615071697 40542090973418323211303773)
          ·
            refine ⟨15203284115031871204238915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40542090973418323211303773 15203284115031871204238915)
            ·
              refine ⟨22804926172547806806358373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15203284115031871204238915 22804926172547806806358373)
              ·
                refine ⟨4275923657352713776192195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22804926172547806806358373 4275923657352713776192195)
                ·
                  refine ⟨6413885486029070664288293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4275923657352713776192195 6413885486029070664288293)
                  ·
                    refine ⟨1202603528630450749554055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6413885486029070664288293 1202603528630450749554055)
                    ·
                      rfl

theorem cell23_7026186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_7026186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026186 prefixEnd_7026186 := by exact prefixLift 7026186
  have htrace : WordTrace (prefixWord ++ tailWord_7026186) baseStart_7026186 baseEnd_7026186 := by
    simpa [prefixWord, tailWord_7026186, baseEnd_7026186] using wordTrace_append hprefix tailTrace_7026186
  have hstable : (prefixWord ++ tailWord_7026186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026186).length < 2 ^ (prefixWord ++ tailWord_7026186).sum := by decide
  have hdescent : baseEnd_7026186 < baseStart_7026186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026209 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_7026209 : Nat := 118140960795 + 7026209 * 2 ^ 59
def prefixEnd_7026209 : Nat := 4983230072969 + 3 ^ 40 * 7026209 * 2
def baseEnd_7026209 : Nat := 3607822395946405658674559

theorem tailTrace_7026209 : CollatzResearch.WordTrace tailWord_7026209 prefixEnd_7026209 3607822395946405658674559 := by
  unfold tailWord_7026209
  simp only [CollatzResearch.WordTrace]
  refine ⟨256266895402252248806945681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170844596934834832537963787 256266895402252248806945681)
  ·
    refine ⟨192200171551689186605209261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256266895402252248806945681 192200171551689186605209261)
    ·
      refine ⟨72075064331883444976953473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192200171551689186605209261 72075064331883444976953473)
      ·
        refine ⟨54056298248912583732715105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72075064331883444976953473 54056298248912583732715105)
        ·
          refine ⟨40542223686684437799536329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54056298248912583732715105 40542223686684437799536329)
          ·
            refine ⟨30406667765013328349652247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40542223686684437799536329 30406667765013328349652247)
            ·
              refine ⟨45610001647519992524478371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30406667765013328349652247 45610001647519992524478371)
              ·
                refine ⟨68415002471279988786717557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45610001647519992524478371 68415002471279988786717557)
                ·
                  refine ⟨6413906481682498948754771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68415002471279988786717557 6413906481682498948754771)
                  ·
                    refine ⟨9620859722523748423132157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6413906481682498948754771 9620859722523748423132157)
                    ·
                      refine ⟨3607822395946405658674559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9620859722523748423132157 3607822395946405658674559)
                      ·
                        rfl

theorem cell23_7026209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_7026209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026209 prefixEnd_7026209 := by exact prefixLift 7026209
  have htrace : WordTrace (prefixWord ++ tailWord_7026209) baseStart_7026209 baseEnd_7026209 := by
    simpa [prefixWord, tailWord_7026209, baseEnd_7026209] using wordTrace_append hprefix tailTrace_7026209
  have hstable : (prefixWord ++ tailWord_7026209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026209).length < 2 ^ (prefixWord ++ tailWord_7026209).sum := by decide
  have hdescent : baseEnd_7026209 < baseStart_7026209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026229 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 1, 5]
def baseStart_7026229 : Nat := 118140960795 + 7026229 * 2 ^ 59
def prefixEnd_7026229 : Nat := 4983230072969 + 3 ^ 40 * 7026229 * 2
def baseEnd_7026229 : Nat := 1202610888519831860141489

theorem tailTrace_7026229 : CollatzResearch.WordTrace tailWord_7026229 prefixEnd_7026229 1202610888519831860141489 := by
  unfold tailWord_7026229
  simp only [CollatzResearch.WordTrace]
  refine ⟨256267624862179792222673741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170845083241453194815115827 256267624862179792222673741)
  ·
    refine ⟨96100359323317422083502653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256267624862179792222673741 96100359323317422083502653)
    ·
      refine ⟨36037634746244033281313495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96100359323317422083502653 36037634746244033281313495)
      ·
        refine ⟨54056452119366049921970243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36037634746244033281313495 54056452119366049921970243)
        ·
          refine ⟨81084678179049074882955365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54056452119366049921970243 81084678179049074882955365)
          ·
            refine ⟨15203377158571701540554131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81084678179049074882955365 15203377158571701540554131)
            ·
              refine ⟨22805065737857552310831197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15203377158571701540554131 22805065737857552310831197)
              ·
                refine ⟨8551899651696582116561699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22805065737857552310831197 8551899651696582116561699)
                ·
                  refine ⟨12827849477544873174842549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8551899651696582116561699 12827849477544873174842549)
                  ·
                    refine ⟨1202610888519831860141489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12827849477544873174842549 1202610888519831860141489)
                    ·
                      rfl

theorem cell23_7026229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_7026229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026229 prefixEnd_7026229 := by exact prefixLift 7026229
  have htrace : WordTrace (prefixWord ++ tailWord_7026229) baseStart_7026229 baseEnd_7026229 := by
    simpa [prefixWord, tailWord_7026229, baseEnd_7026229] using wordTrace_append hprefix tailTrace_7026229
  have hstable : (prefixWord ++ tailWord_7026229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026229).length < 2 ^ (prefixWord ++ tailWord_7026229).sum := by decide
  have hdescent : baseEnd_7026229 < baseStart_7026229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026235 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 5]
def baseStart_7026235 : Nat := 118140960795 + 7026235 * 2 ^ 59
def prefixEnd_7026235 : Nat := 4983230072969 + 3 ^ 40 * 7026235 * 2
def baseEnd_7026235 : Nat := 3607835746443422556949439

theorem tailTrace_7026235 : CollatzResearch.WordTrace tailWord_7026235 prefixEnd_7026235 3607835746443422556949439 := by
  unfold tailWord_7026235
  simp only [CollatzResearch.WordTrace]
  refine ⟨256267843700158055247392159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170845229133438703498261439 256267843700158055247392159)
  ·
    refine ⟨384401765550237082871088239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256267843700158055247392159 384401765550237082871088239)
    ·
      refine ⟨576602648325355624306632359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384401765550237082871088239 576602648325355624306632359)
      ·
        refine ⟨864903972488033436459948539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576602648325355624306632359 864903972488033436459948539)
        ·
          refine ⟨1297355958732050154689922809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864903972488033436459948539 1297355958732050154689922809)
          ·
            refine ⟨973016969049037616017442107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297355958732050154689922809 973016969049037616017442107)
            ·
              refine ⟨1459525453573556424026163161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 973016969049037616017442107 1459525453573556424026163161)
              ·
                refine ⟨1094644090180167318019622371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1459525453573556424026163161 1094644090180167318019622371)
                ·
                  refine ⟨1641966135270250977029433557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1094644090180167318019622371 1641966135270250977029433557)
                  ·
                    refine ⟨38483581295396507274127349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1641966135270250977029433557 38483581295396507274127349)
                    ·
                      refine ⟨3607835746443422556949439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38483581295396507274127349 3607835746443422556949439)
                      ·
                        rfl

theorem cell23_7026235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_7026235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026235 prefixEnd_7026235 := by exact prefixLift 7026235
  have htrace : WordTrace (prefixWord ++ tailWord_7026235) baseStart_7026235 baseEnd_7026235 := by
    simpa [prefixWord, tailWord_7026235, baseEnd_7026235] using wordTrace_append hprefix tailTrace_7026235
  have hstable : (prefixWord ++ tailWord_7026235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026235).length < 2 ^ (prefixWord ++ tailWord_7026235).sum := by decide
  have hdescent : baseEnd_7026235 < baseStart_7026235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026252 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_7026252 : Nat := 118140960795 + 7026252 * 2 ^ 59
def prefixEnd_7026252 : Nat := 4983230072969 + 3 ^ 40 * 7026252 * 2
def baseEnd_7026252 : Nat := 3607844475614548990436861

theorem tailTrace_7026252 : CollatzResearch.WordTrace tailWord_7026252 prefixEnd_7026252 3607844475614548990436861 := by
  unfold tailWord_7026252
  simp only [CollatzResearch.WordTrace]
  refine ⟨128134231870548233575380505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170845642494064311433840673 128134231870548233575380505)
  ·
    refine ⟨96100673902911175181535379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128134231870548233575380505 96100673902911175181535379)
    ·
      refine ⟨144151010854366762772303069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96100673902911175181535379 144151010854366762772303069)
      ·
        refine ⟨54056629070387536039613651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144151010854366762772303069 54056629070387536039613651)
        ·
          refine ⟨81084943605581304059420477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54056629070387536039613651 81084943605581304059420477)
          ·
            refine ⟨30406853852092989022282679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81084943605581304059420477 30406853852092989022282679)
            ·
              refine ⟨45610280778139483533424019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30406853852092989022282679 45610280778139483533424019)
              ·
                refine ⟨68415421167209225300136029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45610280778139483533424019 68415421167209225300136029)
                ·
                  refine ⟨25655782937703459487551011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68415421167209225300136029 25655782937703459487551011)
                  ·
                    refine ⟨38483674406555189231326517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25655782937703459487551011 38483674406555189231326517)
                    ·
                      refine ⟨3607844475614548990436861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38483674406555189231326517 3607844475614548990436861)
                      ·
                        rfl

theorem cell23_7026252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_7026252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026252 prefixEnd_7026252 := by exact prefixLift 7026252
  have htrace : WordTrace (prefixWord ++ tailWord_7026252) baseStart_7026252 baseEnd_7026252 := by
    simpa [prefixWord, tailWord_7026252, baseEnd_7026252] using wordTrace_append hprefix tailTrace_7026252
  have hstable : (prefixWord ++ tailWord_7026252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026252).length < 2 ^ (prefixWord ++ tailWord_7026252).sum := by decide
  have hdescent : baseEnd_7026252 < baseStart_7026252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026255 : List Nat := [1, 1, 2, 1, 1, 2, 3, 12]
def baseStart_7026255 : Nat := 118140960795 + 7026255 * 2 ^ 59
def prefixEnd_7026255 : Nat := 4983230072969 + 3 ^ 40 * 7026255 * 2
def baseEnd_7026255 : Nat := 133623926520611573285161

theorem tailTrace_7026255 : CollatzResearch.WordTrace tailWord_7026255 prefixEnd_7026255 133623926520611573285161 := by
  unfold tailWord_7026255
  simp only [CollatzResearch.WordTrace]
  refine ⟨256268573160085598663120219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170845715440057065775413479 256268573160085598663120219)
  ·
    refine ⟨384402859740128397994680329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256268573160085598663120219 384402859740128397994680329)
    ·
      refine ⟨288302144805096298496010247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 384402859740128397994680329 288302144805096298496010247)
      ·
        refine ⟨432453217207644447744015371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288302144805096298496010247 432453217207644447744015371)
        ·
          refine ⟨648679825811466671616023057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432453217207644447744015371 648679825811466671616023057)
          ·
            refine ⟨486509869358600003712017293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648679825811466671616023057 486509869358600003712017293)
            ·
              refine ⟨182441201009475001392006485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 486509869358600003712017293 182441201009475001392006485)
              ·
                refine ⟨133623926520611573285161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 182441201009475001392006485 133623926520611573285161)
                ·
                  rfl

theorem cell23_7026255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 12].length) (baseStart_7026255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026255 prefixEnd_7026255 := by exact prefixLift 7026255
  have htrace : WordTrace (prefixWord ++ tailWord_7026255) baseStart_7026255 baseEnd_7026255 := by
    simpa [prefixWord, tailWord_7026255, baseEnd_7026255] using wordTrace_append hprefix tailTrace_7026255
  have hstable : (prefixWord ++ tailWord_7026255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026255).length < 2 ^ (prefixWord ++ tailWord_7026255).sum := by decide
  have hdescent : baseEnd_7026255 < baseStart_7026255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026286 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_7026286 : Nat := 118140960795 + 7026286 * 2 ^ 59
def prefixEnd_7026286 : Nat := 4983230072969 + 3 ^ 40 * 7026286 * 2
def baseEnd_7026286 : Nat := 3607861933956801857411705

theorem tailTrace_7026286 : CollatzResearch.WordTrace tailWord_7026286 prefixEnd_7026286 3607861933956801857411705 := by
  unfold tailWord_7026286
  simp only [CollatzResearch.WordTrace]
  refine ⟨32033712977871661369687339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170846469215315527304999141 32033712977871661369687339)
  ·
    refine ⟨48050569466807492054531009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32033712977871661369687339 48050569466807492054531009)
    ·
      refine ⟨36037927100105619040898257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48050569466807492054531009 36037927100105619040898257)
      ·
        refine ⟨27028445325079214280673693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36037927100105619040898257 27028445325079214280673693)
        ·
          refine ⟨10135666996904705355252635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27028445325079214280673693 10135666996904705355252635)
          ·
            refine ⟨15203500495357058032878953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10135666996904705355252635 15203500495357058032878953)
            ·
              refine ⟨11402625371517793524659215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15203500495357058032878953 11402625371517793524659215)
              ·
                refine ⟨17103938057276690286988823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11402625371517793524659215 17103938057276690286988823)
                ·
                  refine ⟨25655907085915035430483235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17103938057276690286988823 25655907085915035430483235)
                  ·
                    refine ⟨38483860628872553145724853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25655907085915035430483235 38483860628872553145724853)
                    ·
                      refine ⟨3607861933956801857411705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38483860628872553145724853 3607861933956801857411705)
                      ·
                        rfl

theorem cell23_7026286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_7026286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026286 prefixEnd_7026286 := by exact prefixLift 7026286
  have htrace : WordTrace (prefixWord ++ tailWord_7026286) baseStart_7026286 baseEnd_7026286 := by
    simpa [prefixWord, tailWord_7026286, baseEnd_7026286] using wordTrace_append hprefix tailTrace_7026286
  have hstable : (prefixWord ++ tailWord_7026286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026286).length < 2 ^ (prefixWord ++ tailWord_7026286).sum := by decide
  have hdescent : baseEnd_7026286 < baseStart_7026286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026299 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 4, 1, 3]
def baseStart_7026299 : Nat := 118140960795 + 7026299 * 2 ^ 59
def prefixEnd_7026299 : Nat := 4983230072969 + 3 ^ 40 * 7026299 * 2
def baseEnd_7026299 : Nat := 3607868609205310306549145

theorem tailTrace_7026299 : CollatzResearch.WordTrace tailWord_7026299 prefixEnd_7026299 3607868609205310306549145 := by
  unfold tailWord_7026299
  simp only [CollatzResearch.WordTrace]
  refine ⟨256270177971926194177721951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170846785314617462785147967 256270177971926194177721951)
  ·
    refine ⟨384405266957889291266582927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256270177971926194177721951 384405266957889291266582927)
    ·
      refine ⟨576607900436833936899874391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384405266957889291266582927 576607900436833936899874391)
      ·
        refine ⟨864911850655250905349811587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576607900436833936899874391 864911850655250905349811587)
        ·
          refine ⟨1297367775982876358024717381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864911850655250905349811587 1297367775982876358024717381)
          ·
            refine ⟨243256457996789317129634509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1297367775982876358024717381 243256457996789317129634509)
            ·
              refine ⟨91221171748795993923612941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243256457996789317129634509 91221171748795993923612941)
              ·
                refine ⟨34207939405798497721354853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91221171748795993923612941 34207939405798497721354853)
                ·
                  refine ⟨6413988638587218322754035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34207939405798497721354853 6413988638587218322754035)
                  ·
                    refine ⟨9620982957880827484131053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6413988638587218322754035 9620982957880827484131053)
                    ·
                      refine ⟨3607868609205310306549145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9620982957880827484131053 3607868609205310306549145)
                      ·
                        rfl

theorem cell23_7026299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 4, 1, 3].length) (baseStart_7026299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026299 prefixEnd_7026299 := by exact prefixLift 7026299
  have htrace : WordTrace (prefixWord ++ tailWord_7026299) baseStart_7026299 baseEnd_7026299 := by
    simpa [prefixWord, tailWord_7026299, baseEnd_7026299] using wordTrace_append hprefix tailTrace_7026299
  have hstable : (prefixWord ++ tailWord_7026299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026299).length < 2 ^ (prefixWord ++ tailWord_7026299).sum := by decide
  have hdescent : baseEnd_7026299 < baseStart_7026299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026316 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 2, 1, 3]
def baseStart_7026316 : Nat := 118140960795 + 7026316 * 2 ^ 59
def prefixEnd_7026316 : Nat := 4983230072969 + 3 ^ 40 * 7026316 * 2
def baseEnd_7026316 : Nat := 3607877338376436740036567

theorem tailTrace_7026316 : CollatzResearch.WordTrace tailWord_7026316 prefixEnd_7026316 3607877338376436740036567 := by
  unfold tailWord_7026316
  simp only [CollatzResearch.WordTrace]
  refine ⟨128135399006432303040545401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170847198675243070720727201 128135399006432303040545401)
  ·
    refine ⟨96101549254824227280409051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128135399006432303040545401 96101549254824227280409051)
    ·
      refine ⟨144152323882236340920613577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96101549254824227280409051 144152323882236340920613577)
      ·
        refine ⟨108114242911677255690460183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144152323882236340920613577 108114242911677255690460183)
        ·
          refine ⟨162171364367515883535690275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108114242911677255690460183 162171364367515883535690275)
          ·
            refine ⟨243257046551273825303535413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162171364367515883535690275 243257046551273825303535413)
            ·
              refine ⟨22805348114181921122206445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 243257046551273825303535413 22805348114181921122206445)
              ·
                refine ⟨8552005542818220420827417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22805348114181921122206445 8552005542818220420827417)
                ·
                  refine ⟨6414004157113665315620563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8552005542818220420827417 6414004157113665315620563)
                  ·
                    refine ⟨9621006235670497973430845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6414004157113665315620563 9621006235670497973430845)
                    ·
                      refine ⟨3607877338376436740036567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9621006235670497973430845 3607877338376436740036567)
                      ·
                        rfl

theorem cell23_7026316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_7026316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026316 prefixEnd_7026316 := by exact prefixLift 7026316
  have htrace : WordTrace (prefixWord ++ tailWord_7026316) baseStart_7026316 baseEnd_7026316 := by
    simpa [prefixWord, tailWord_7026316, baseEnd_7026316] using wordTrace_append hprefix tailTrace_7026316
  have hstable : (prefixWord ++ tailWord_7026316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026316).length < 2 ^ (prefixWord ++ tailWord_7026316).sum := by decide
  have hdescent : baseEnd_7026316 < baseStart_7026316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026349 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7026349 : Nat := 118140960795 + 7026349 * 2 ^ 59
def prefixEnd_7026349 : Nat := 4983230072969 + 3 ^ 40 * 7026349 * 2
def baseEnd_7026349 : Nat := 1202631427746011703641305

theorem tailTrace_7026349 : CollatzResearch.WordTrace tailWord_7026349 prefixEnd_7026349 1202631427746011703641305 := by
  unfold tailWord_7026349
  simp only [CollatzResearch.WordTrace]
  refine ⟨256272001621745052717042101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170848001081163368478028067 256272001621745052717042101)
  ·
    refine ⟨24025500152038598692222697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 256272001621745052717042101 24025500152038598692222697)
    ·
      refine ⟨18019125114028949019167023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24025500152038598692222697 18019125114028949019167023)
      ·
        refine ⟨27028687671043423528750535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18019125114028949019167023 27028687671043423528750535)
        ·
          refine ⟨40543031506565135293125803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27028687671043423528750535 40543031506565135293125803)
          ·
            refine ⟨60814547259847702939688705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40543031506565135293125803 60814547259847702939688705)
            ·
              refine ⟨45610910444885777204766529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60814547259847702939688705 45610910444885777204766529)
              ·
                refine ⟨34208182833664332903574897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45610910444885777204766529 34208182833664332903574897)
                ·
                  refine ⟨25656137125248249677681173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34208182833664332903574897 25656137125248249677681173)
                  ·
                    refine ⟨1202631427746011703641305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25656137125248249677681173 1202631427746011703641305)
                    ·
                      rfl

theorem cell23_7026349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7026349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026349 prefixEnd_7026349 := by exact prefixLift 7026349
  have htrace : WordTrace (prefixWord ++ tailWord_7026349) baseStart_7026349 baseEnd_7026349 := by
    simpa [prefixWord, tailWord_7026349, baseEnd_7026349] using wordTrace_append hprefix tailTrace_7026349
  have hstable : (prefixWord ++ tailWord_7026349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026349).length < 2 ^ (prefixWord ++ tailWord_7026349).sum := by decide
  have hdescent : baseEnd_7026349 < baseStart_7026349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026359 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 3]
def baseStart_7026359 : Nat := 118140960795 + 7026359 * 2 ^ 59
def prefixEnd_7026359 : Nat := 4983230072969 + 3 ^ 40 * 7026359 * 2
def baseEnd_7026359 : Nat := 3607899418044580071798869

theorem tailTrace_7026359 : CollatzResearch.WordTrace tailWord_7026359 prefixEnd_7026359 3607899418044580071798869 := by
  unfold tailWord_7026359
  simp only [CollatzResearch.WordTrace]
  refine ⟨256272366351708824424906131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170848244234472549616604087 256272366351708824424906131)
  ·
    refine ⟨384408549527563236637359197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256272366351708824424906131 384408549527563236637359197)
    ·
      refine ⟨144153206072836213739009699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384408549527563236637359197 144153206072836213739009699)
      ·
        refine ⟨216229809109254320608514549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144153206072836213739009699 216229809109254320608514549)
        ·
          refine ⟨20271544603992592557048239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216229809109254320608514549 20271544603992592557048239)
          ·
            refine ⟨30407316905988888835572359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20271544603992592557048239 30407316905988888835572359)
            ·
              refine ⟨45610975358983333253358539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30407316905988888835572359 45610975358983333253358539)
              ·
                refine ⟨68416463038474999880037809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45610975358983333253358539 68416463038474999880037809)
                ·
                  refine ⟨51312347278856249910028357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68416463038474999880037809 51312347278856249910028357)
                  ·
                    refine ⟨9621065114785546858130317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51312347278856249910028357 9621065114785546858130317)
                    ·
                      refine ⟨3607899418044580071798869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9621065114785546858130317 3607899418044580071798869)
                      ·
                        rfl

theorem cell23_7026359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_7026359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026359 prefixEnd_7026359 := by exact prefixLift 7026359
  have htrace : WordTrace (prefixWord ++ tailWord_7026359) baseStart_7026359 baseEnd_7026359 := by
    simpa [prefixWord, tailWord_7026359, baseEnd_7026359] using wordTrace_append hprefix tailTrace_7026359
  have hstable : (prefixWord ++ tailWord_7026359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026359).length < 2 ^ (prefixWord ++ tailWord_7026359).sum := by decide
  have hdescent : baseEnd_7026359 < baseStart_7026359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026429 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 4]
def baseStart_7026429 : Nat := 118140960795 + 7026429 * 2 ^ 59
def prefixEnd_7026429 : Nat := 4983230072969 + 3 ^ 40 * 7026429 * 2
def baseEnd_7026429 : Nat := 3607935361690394797923547

theorem tailTrace_7026429 : CollatzResearch.WordTrace tailWord_7026429 prefixEnd_7026429 3607935361690394797923547 := by
  unfold tailWord_7026429
  simp only [CollatzResearch.WordTrace]
  refine ⟨256274919461455226379954341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170849946307636817586636227 256274919461455226379954341)
  ·
    refine ⟨48051547399022854946241439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 256274919461455226379954341 48051547399022854946241439)
    ·
      refine ⟨72077321098534282419362159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48051547399022854946241439 72077321098534282419362159)
      ·
        refine ⟨108115981647801423629043239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72077321098534282419362159 108115981647801423629043239)
        ·
          refine ⟨162173972471702135443564859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108115981647801423629043239 162173972471702135443564859)
          ·
            refine ⟨243260958707553203165347289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162173972471702135443564859 243260958707553203165347289)
            ·
              refine ⟨182445719030664902374010467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243260958707553203165347289 182445719030664902374010467)
              ·
                refine ⟨273668578545997353561015701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182445719030664902374010467 273668578545997353561015701)
                ·
                  refine ⟨12828214619343625948172611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 273668578545997353561015701 12828214619343625948172611)
                  ·
                    refine ⟨19242321929015438922258917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12828214619343625948172611 19242321929015438922258917)
                    ·
                      refine ⟨3607935361690394797923547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19242321929015438922258917 3607935361690394797923547)
                      ·
                        rfl

theorem cell23_7026429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_7026429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026429 prefixEnd_7026429 := by exact prefixLift 7026429
  have htrace : WordTrace (prefixWord ++ tailWord_7026429) baseStart_7026429 baseEnd_7026429 := by
    simpa [prefixWord, tailWord_7026429, baseEnd_7026429] using wordTrace_append hprefix tailTrace_7026429
  have hstable : (prefixWord ++ tailWord_7026429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026429).length < 2 ^ (prefixWord ++ tailWord_7026429).sum := by decide
  have hdescent : baseEnd_7026429 < baseStart_7026429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026446 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2]
def baseStart_7026446 : Nat := 118140960795 + 7026446 * 2 ^ 59
def prefixEnd_7026446 : Nat := 4983230072969 + 3 ^ 40 * 7026446 * 2
def baseEnd_7026446 : Nat := 3607944090861521231410969

theorem tailTrace_7026446 : CollatzResearch.WordTrace tailWord_7026446 prefixEnd_7026446 3607944090861521231410969 := by
  unfold tailWord_7026446
  simp only [CollatzResearch.WordTrace]
  refine ⟨32034442437799204785415399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170850359668262425522215461 32034442437799204785415399)
  ·
    refine ⟨48051663656698807178123099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32034442437799204785415399 48051663656698807178123099)
    ·
      refine ⟨72077495485048210767184649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48051663656698807178123099 72077495485048210767184649)
      ·
        refine ⟨54058121613786158075388487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72077495485048210767184649 54058121613786158075388487)
        ·
          refine ⟨81087182420679237113082731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54058121613786158075388487 81087182420679237113082731)
          ·
            refine ⟨121630773631018855669624097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81087182420679237113082731 121630773631018855669624097)
            ·
              refine ⟨91223080223264141752218073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121630773631018855669624097 91223080223264141752218073)
              ·
                refine ⟨68417310167448106314163555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91223080223264141752218073 68417310167448106314163555)
                ·
                  refine ⟨102625965251172159471245333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68417310167448106314163555 102625965251172159471245333)
                  ·
                    refine ⟨4810592121148694975214625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102625965251172159471245333 4810592121148694975214625)
                    ·
                      refine ⟨3607944090861521231410969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4810592121148694975214625 3607944090861521231410969)
                      ·
                        rfl

theorem cell23_7026446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_7026446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026446 prefixEnd_7026446 := by exact prefixLift 7026446
  have htrace : WordTrace (prefixWord ++ tailWord_7026446) baseStart_7026446 baseEnd_7026446 := by
    simpa [prefixWord, tailWord_7026446, baseEnd_7026446] using wordTrace_append hprefix tailTrace_7026446
  have hstable : (prefixWord ++ tailWord_7026446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026446).length < 2 ^ (prefixWord ++ tailWord_7026446).sum := by decide
  have hdescent : baseEnd_7026446 < baseStart_7026446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026469 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 8]
def baseStart_7026469 : Nat := 118140960795 + 7026469 * 2 ^ 59
def prefixEnd_7026469 : Nat := 4983230072969 + 3 ^ 40 * 7026469 * 2
def baseEnd_7026469 : Nat := 400883988990730515713707

theorem tailTrace_7026469 : CollatzResearch.WordTrace tailWord_7026469 prefixEnd_7026469 400883988990730515713707 := by
  unfold tailWord_7026469
  simp only [CollatzResearch.WordTrace]
  refine ⟨256276378381310313211410461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170850918920873542140940307 256276378381310313211410461)
  ·
    refine ⟨96103641892991367454278923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 256276378381310313211410461 96103641892991367454278923)
    ·
      refine ⟨144155462839487051181418385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96103641892991367454278923 144155462839487051181418385)
      ·
        refine ⟨108116597129615288386063789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144155462839487051181418385 108116597129615288386063789)
        ·
          refine ⟨40543723923605733144773921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108116597129615288386063789 40543723923605733144773921)
          ·
            refine ⟨30407792942704299858580441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40543723923605733144773921 30407792942704299858580441)
            ·
              refine ⟨22805844707028224893935331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30407792942704299858580441 22805844707028224893935331)
              ·
                refine ⟨34208767060542337340902997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22805844707028224893935331 34208767060542337340902997)
                ·
                  refine ⟨400883988990730515713707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34208767060542337340902997 400883988990730515713707)
                  ·
                    rfl

theorem cell23_7026469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 8].length) (baseStart_7026469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026469 prefixEnd_7026469 := by exact prefixLift 7026469
  have htrace : WordTrace (prefixWord ++ tailWord_7026469) baseStart_7026469 baseEnd_7026469 := by
    simpa [prefixWord, tailWord_7026469, baseEnd_7026469] using wordTrace_append hprefix tailTrace_7026469
  have hstable : (prefixWord ++ tailWord_7026469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026469).length < 2 ^ (prefixWord ++ tailWord_7026469).sum := by decide
  have hdescent : baseEnd_7026469 < baseStart_7026469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026524 : List Nat := [2, 2, 4, 2, 2, 2, 2, 2, 1, 4]
def baseStart_7026524 : Nat := 118140960795 + 7026524 * 2 ^ 59
def prefixEnd_7026524 : Nat := 4983230072969 + 3 ^ 40 * 7026524 * 2
def baseEnd_7026524 : Nat := 1202661380784190642078537

theorem tailTrace_7026524 : CollatzResearch.WordTrace tailWord_7026524 prefixEnd_7026524 1202661380784190642078537 := by
  unfold tailWord_7026524
  simp only [CollatzResearch.WordTrace]
  refine ⟨128139192198055528802331313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170852256264074038403108417 128139192198055528802331313)
  ·
    refine ⟨96104394148541646601748485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128139192198055528802331313 96104394148541646601748485)
    ·
      refine ⟨18019573902851558737827841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96104394148541646601748485 18019573902851558737827841)
      ·
        refine ⟨13514680427138669053370881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18019573902851558737827841 13514680427138669053370881)
        ·
          refine ⟨10136010320354001790028161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13514680427138669053370881 10136010320354001790028161)
          ·
            refine ⟨7602007740265501342521121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10136010320354001790028161 7602007740265501342521121)
            ·
              refine ⟨5701505805199126006890841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7602007740265501342521121 5701505805199126006890841)
              ·
                refine ⟨4276129353899344505168131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5701505805199126006890841 4276129353899344505168131)
                ·
                  refine ⟨6414194030849016757752197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4276129353899344505168131 6414194030849016757752197)
                  ·
                    refine ⟨1202661380784190642078537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6414194030849016757752197 1202661380784190642078537)
                    ·
                      rfl

theorem cell23_7026524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_7026524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026524 prefixEnd_7026524 := by exact prefixLift 7026524
  have htrace : WordTrace (prefixWord ++ tailWord_7026524) baseStart_7026524 baseEnd_7026524 := by
    simpa [prefixWord, tailWord_7026524, baseEnd_7026524] using wordTrace_append hprefix tailTrace_7026524
  have hstable : (prefixWord ++ tailWord_7026524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026524).length < 2 ^ (prefixWord ++ tailWord_7026524).sum := by decide
  have hdescent : baseEnd_7026524 < baseStart_7026524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026529 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 3, 6]
def baseStart_7026529 : Nat := 118140960795 + 7026529 * 2 ^ 59
def prefixEnd_7026529 : Nat := 4983230072969 + 3 ^ 40 * 7026529 * 2
def baseEnd_7026529 : Nat := 1202662236585281468891029

theorem tailTrace_7026529 : CollatzResearch.WordTrace tailWord_7026529 prefixEnd_7026529 1202662236585281468891029 := by
  unfold tailWord_7026529
  simp only [CollatzResearch.WordTrace]
  refine ⟨256278566761092943458594641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170852377840728628972396427 256278566761092943458594641)
  ·
    refine ⟨192208925070819707593945981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 256278566761092943458594641 192208925070819707593945981)
    ·
      refine ⟨72078346901557390347729743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192208925070819707593945981 72078346901557390347729743)
      ·
        refine ⟨108117520352336085521594615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72078346901557390347729743 108117520352336085521594615)
        ·
          refine ⟨162176280528504128282391923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108117520352336085521594615 162176280528504128282391923)
          ·
            refine ⟨243264420792756192423587885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162176280528504128282391923 243264420792756192423587885)
            ·
              refine ⟨91224157797283572158845457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243264420792756192423587885 91224157797283572158845457)
              ·
                refine ⟨68418118347962679119134093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91224157797283572158845457 68418118347962679119134093)
                ·
                  refine ⟨25656794380486004669675285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68418118347962679119134093 25656794380486004669675285)
                  ·
                    refine ⟨1202662236585281468891029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25656794380486004669675285 1202662236585281468891029)
                    ·
                      rfl

theorem cell23_7026529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_7026529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026529 prefixEnd_7026529 := by exact prefixLift 7026529
  have htrace : WordTrace (prefixWord ++ tailWord_7026529) baseStart_7026529 baseEnd_7026529 := by
    simpa [prefixWord, tailWord_7026529, baseEnd_7026529] using wordTrace_append hprefix tailTrace_7026529
  have hstable : (prefixWord ++ tailWord_7026529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026529).length < 2 ^ (prefixWord ++ tailWord_7026529).sum := by decide
  have hdescent : baseEnd_7026529 < baseStart_7026529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026536 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_7026536 : Nat := 118140960795 + 7026536 * 2 ^ 59
def prefixEnd_7026536 : Nat := 4983230072969 + 3 ^ 40 * 7026536 * 2
def baseEnd_7026536 : Nat := 3607990304120425879285555

theorem tailTrace_7026536 : CollatzResearch.WordTrace tailWord_7026536 prefixEnd_7026536 3607990304120425879285555 := by
  unfold tailWord_7026536
  simp only [CollatzResearch.WordTrace]
  refine ⟨128139411036033791827049731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170852548048045055769399641 128139411036033791827049731)
  ·
    refine ⟨192209116554050687740574597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128139411036033791827049731 192209116554050687740574597)
    ·
      refine ⟨36039209353884503951357737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192209116554050687740574597 36039209353884503951357737)
      ·
        refine ⟨27029407015413377963518303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36039209353884503951357737 27029407015413377963518303)
        ·
          refine ⟨40544110523120066945277455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27029407015413377963518303 40544110523120066945277455)
          ·
            refine ⟨60816165784680100417916183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40544110523120066945277455 60816165784680100417916183)
            ·
              refine ⟨91224248677020150626874275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60816165784680100417916183 91224248677020150626874275)
              ·
                refine ⟨136836373015530225940311413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91224248677020150626874275 136836373015530225940311413)
                ·
                  refine ⟨12828409970205958681904195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136836373015530225940311413 12828409970205958681904195)
                  ·
                    refine ⟨19242614955308938022856293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12828409970205958681904195 19242614955308938022856293)
                    ·
                      refine ⟨3607990304120425879285555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19242614955308938022856293 3607990304120425879285555)
                      ·
                        rfl

theorem cell23_7026536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_7026536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026536 prefixEnd_7026536 := by exact prefixLift 7026536
  have htrace : WordTrace (prefixWord ++ tailWord_7026536) baseStart_7026536 baseEnd_7026536 := by
    simpa [prefixWord, tailWord_7026536, baseEnd_7026536] using wordTrace_append hprefix tailTrace_7026536
  have hstable : (prefixWord ++ tailWord_7026536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026536).length < 2 ^ (prefixWord ++ tailWord_7026536).sum := by decide
  have hdescent : baseEnd_7026536 < baseStart_7026536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026539 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 5]
def baseStart_7026539 : Nat := 118140960795 + 7026539 * 2 ^ 59
def prefixEnd_7026539 : Nat := 4983230072969 + 3 ^ 40 * 7026539 * 2
def baseEnd_7026539 : Nat := 3607991844562389367548041

theorem tailTrace_7026539 : CollatzResearch.WordTrace tailWord_7026539 prefixEnd_7026539 3607991844562389367548041 := by
  unfold tailWord_7026539
  simp only [CollatzResearch.WordTrace]
  refine ⟨256278931491056715166458671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170852620994037810110972447 256278931491056715166458671)
  ·
    refine ⟨384418397236585072749688007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256278931491056715166458671 384418397236585072749688007)
    ·
      refine ⟨576627595854877609124532011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384418397236585072749688007 576627595854877609124532011)
      ·
        refine ⟨864941393782316413686798017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576627595854877609124532011 864941393782316413686798017)
        ·
          refine ⟨648706045336737310265098513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 864941393782316413686798017 648706045336737310265098513)
          ·
            refine ⟨486529534002552982698823885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648706045336737310265098513 486529534002552982698823885)
            ·
              refine ⟨182448575250957368512058957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 486529534002552982698823885 182448575250957368512058957)
              ·
                refine ⟨68418215719109013192022109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182448575250957368512058957 68418215719109013192022109)
                ·
                  refine ⟨25656830894665879947008291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68418215719109013192022109 25656830894665879947008291)
                  ·
                    refine ⟨38485246341998819920512437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25656830894665879947008291 38485246341998819920512437)
                    ·
                      refine ⟨3607991844562389367548041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38485246341998819920512437 3607991844562389367548041)
                      ·
                        rfl

theorem cell23_7026539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 5].length) (baseStart_7026539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026539 prefixEnd_7026539 := by exact prefixLift 7026539
  have htrace : WordTrace (prefixWord ++ tailWord_7026539) baseStart_7026539 baseEnd_7026539 := by
    simpa [prefixWord, tailWord_7026539, baseEnd_7026539] using wordTrace_append hprefix tailTrace_7026539
  have hstable : (prefixWord ++ tailWord_7026539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026539).length < 2 ^ (prefixWord ++ tailWord_7026539).sum := by decide
  have hdescent : baseEnd_7026539 < baseStart_7026539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026546 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_7026546 : Nat := 118140960795 + 7026546 * 2 ^ 59
def prefixEnd_7026546 : Nat := 4983230072969 + 3 ^ 40 * 7026546 * 2
def baseEnd_7026546 : Nat := 1202665146308990280053503

theorem tailTrace_7026546 : CollatzResearch.WordTrace tailWord_7026546 prefixEnd_7026546 1202665146308990280053503 := by
  unfold tailWord_7026546
  simp only [CollatzResearch.WordTrace]
  refine ⟨64069796700507838840490873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170852791201354236907975661 64069796700507838840490873)
  ·
    refine ⟨48052347525380879130368155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64069796700507838840490873 48052347525380879130368155)
    ·
      refine ⟨72078521288071318695552233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48052347525380879130368155 72078521288071318695552233)
      ·
        refine ⟨54058890966053489021664175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72078521288071318695552233 54058890966053489021664175)
        ·
          refine ⟨81088336449080233532496263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54058890966053489021664175 81088336449080233532496263)
          ·
            refine ⟨121632504673620350298744395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81088336449080233532496263 121632504673620350298744395)
            ·
              refine ⟨182448757010430525448116593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121632504673620350298744395 182448757010430525448116593)
              ·
                refine ⟨136836567757822894086087445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182448757010430525448116593 136836567757822894086087445)
                ·
                  refine ⟨6414214113647948160285349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136836567757822894086087445 6414214113647948160285349)
                  ·
                    refine ⟨1202665146308990280053503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6414214113647948160285349 1202665146308990280053503)
                    ·
                      rfl

theorem cell23_7026546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_7026546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026546 prefixEnd_7026546 := by exact prefixLift 7026546
  have htrace : WordTrace (prefixWord ++ tailWord_7026546) baseStart_7026546 baseEnd_7026546 := by
    simpa [prefixWord, tailWord_7026546, baseEnd_7026546] using wordTrace_append hprefix tailTrace_7026546
  have hstable : (prefixWord ++ tailWord_7026546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026546).length < 2 ^ (prefixWord ++ tailWord_7026546).sum := by decide
  have hdescent : baseEnd_7026546 < baseStart_7026546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026567 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 1, 5]
def baseStart_7026567 : Nat := 118140960795 + 7026567 * 2 ^ 59
def prefixEnd_7026567 : Nat := 4983230072969 + 3 ^ 40 * 7026567 * 2
def baseEnd_7026567 : Nat := 1202668740673571752665971

theorem tailTrace_7026567 : CollatzResearch.WordTrace tailWord_7026567 prefixEnd_7026567 1202668740673571752665971 := by
  unfold tailWord_7026567
  simp only [CollatzResearch.WordTrace]
  refine ⟨256279952734955275948477955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170853301823303517298985303 256279952734955275948477955)
  ·
    refine ⟨384419929102432913922716933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256279952734955275948477955 384419929102432913922716933)
    ·
      refine ⟨72078736706706171360509425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 384419929102432913922716933 72078736706706171360509425)
      ·
        refine ⟨54059052530029628520382069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72078736706706171360509425 54059052530029628520382069)
        ·
          refine ⟨5068036174690277673785819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54059052530029628520382069 5068036174690277673785819)
          ·
            refine ⟨7602054262035416510678729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5068036174690277673785819 7602054262035416510678729)
            ·
              refine ⟨5701540696526562383009047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7602054262035416510678729 5701540696526562383009047)
              ·
                refine ⟨8552311044789843574513571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5701540696526562383009047 8552311044789843574513571)
                ·
                  refine ⟨12828466567184765361770357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8552311044789843574513571 12828466567184765361770357)
                  ·
                    refine ⟨1202668740673571752665971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12828466567184765361770357 1202668740673571752665971)
                    ·
                      rfl

theorem cell23_7026567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_7026567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026567 prefixEnd_7026567 := by exact prefixLift 7026567
  have htrace : WordTrace (prefixWord ++ tailWord_7026567) baseStart_7026567 baseEnd_7026567 := by
    simpa [prefixWord, tailWord_7026567, baseEnd_7026567] using wordTrace_append hprefix tailTrace_7026567
  have hstable : (prefixWord ++ tailWord_7026567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026567).length < 2 ^ (prefixWord ++ tailWord_7026567).sum := by decide
  have hdescent : baseEnd_7026567 < baseStart_7026567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026570 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4]
def baseStart_7026570 : Nat := 118140960795 + 7026570 * 2 ^ 59
def prefixEnd_7026570 : Nat := 4983230072969 + 3 ^ 40 * 7026570 * 2
def baseEnd_7026570 : Nat := 3608007762462678746260399

theorem tailTrace_7026570 : CollatzResearch.WordTrace tailWord_7026570 prefixEnd_7026570 3608007762462678746260399 := by
  unfold tailWord_7026570
  simp only [CollatzResearch.WordTrace]
  refine ⟨64070015538486101865209291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170853374769296271640558109 64070015538486101865209291)
  ·
    refine ⟨96105023307729152797813937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64070015538486101865209291 96105023307729152797813937)
    ·
      refine ⟨72078767480796864598360453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96105023307729152797813937 72078767480796864598360453)
      ·
        refine ⟨13514768902649412112192585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72078767480796864598360453 13514768902649412112192585)
        ·
          refine ⟨10136076676987059084144439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13514768902649412112192585 10136076676987059084144439)
          ·
            refine ⟨15204115015480588626216659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10136076676987059084144439 15204115015480588626216659)
            ·
              refine ⟨22806172523220882939324989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15204115015480588626216659 22806172523220882939324989)
              ·
                refine ⟨8552314696207831102246871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22806172523220882939324989 8552314696207831102246871)
                ·
                  refine ⟨12828472044311746653370307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8552314696207831102246871 12828472044311746653370307)
                  ·
                    refine ⟨19242708066467619980055461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12828472044311746653370307 19242708066467619980055461)
                    ·
                      refine ⟨3608007762462678746260399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19242708066467619980055461 3608007762462678746260399)
                      ·
                        rfl

theorem cell23_7026570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_7026570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026570 prefixEnd_7026570 := by exact prefixLift 7026570
  have htrace : WordTrace (prefixWord ++ tailWord_7026570) baseStart_7026570 baseEnd_7026570 := by
    simpa [prefixWord, tailWord_7026570, baseEnd_7026570] using wordTrace_append hprefix tailTrace_7026570
  have hstable : (prefixWord ++ tailWord_7026570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026570).length < 2 ^ (prefixWord ++ tailWord_7026570).sum := by decide
  have hdescent : baseEnd_7026570 < baseStart_7026570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026580 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_7026580 : Nat := 118140960795 + 7026580 * 2 ^ 59
def prefixEnd_7026580 : Nat := 4983230072969 + 3 ^ 40 * 7026580 * 2
def baseEnd_7026580 : Nat := 1202670965756407902378451

theorem tailTrace_7026580 : CollatzResearch.WordTrace tailWord_7026580 prefixEnd_7026580 1202670965756407902378451 := by
  unfold tailWord_7026580
  simp only [CollatzResearch.WordTrace]
  refine ⟨128140213441954089584350597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170853617922605452779134129 128140213441954089584350597)
  ·
    refine ⟨24026290020366391797065737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128140213441954089584350597 24026290020366391797065737)
    ·
      refine ⟨18019717515274793847799303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24026290020366391797065737 18019717515274793847799303)
      ·
        refine ⟨27029576272912190771698955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18019717515274793847799303 27029576272912190771698955)
        ·
          refine ⟨40544364409368286157548433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27029576272912190771698955 40544364409368286157548433)
          ·
            refine ⟨30408273307026214618161325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40544364409368286157548433 30408273307026214618161325)
            ·
              refine ⟨11403102490134830481810497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30408273307026214618161325 11403102490134830481810497)
              ·
                refine ⟨8552326867601122861357873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11403102490134830481810497 8552326867601122861357873)
                ·
                  refine ⟨6414245150700842146018405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8552326867601122861357873 6414245150700842146018405)
                  ·
                    refine ⟨1202670965756407902378451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6414245150700842146018405 1202670965756407902378451)
                    ·
                      rfl

theorem cell23_7026580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_7026580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026580 prefixEnd_7026580 := by exact prefixLift 7026580
  have htrace : WordTrace (prefixWord ++ tailWord_7026580) baseStart_7026580 baseEnd_7026580 := by
    simpa [prefixWord, tailWord_7026580, baseEnd_7026580] using wordTrace_append hprefix tailTrace_7026580
  have hstable : (prefixWord ++ tailWord_7026580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026580).length < 2 ^ (prefixWord ++ tailWord_7026580).sum := by decide
  have hdescent : baseEnd_7026580 < baseStart_7026580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026600 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7026600 : Nat := 118140960795 + 7026600 * 2 ^ 59
def prefixEnd_7026600 : Nat := 4983230072969 + 3 ^ 40 * 7026600 * 2
def baseEnd_7026600 : Nat := 3608023166882313628885261

theorem tailTrace_7026600 : CollatzResearch.WordTrace tailWord_7026600 prefixEnd_7026600 3608023166882313628885261 := by
  unfold tailWord_7026600
  simp only [CollatzResearch.WordTrace]
  refine ⟨128140578171917861292214627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170854104229223815056286169 128140578171917861292214627)
  ·
    refine ⟨192210867257876791938321941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128140578171917861292214627 192210867257876791938321941)
    ·
      refine ⟨9009884402712974622108841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192210867257876791938321941 9009884402712974622108841)
      ·
        refine ⟨6757413302034730966581631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9009884402712974622108841 6757413302034730966581631)
        ·
          refine ⟨10136119953052096449872447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6757413302034730966581631 10136119953052096449872447)
          ·
            refine ⟨15204179929578144674808671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10136119953052096449872447 15204179929578144674808671)
            ·
              refine ⟨22806269894367217012213007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15204179929578144674808671 22806269894367217012213007)
              ·
                refine ⟨34209404841550825518319511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22806269894367217012213007 34209404841550825518319511)
                ·
                  refine ⟨51314107262326238277479267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34209404841550825518319511 51314107262326238277479267)
                  ·
                    refine ⟨76971160893489357416218901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51314107262326238277479267 76971160893489357416218901)
                    ·
                      refine ⟨3608023166882313628885261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76971160893489357416218901 3608023166882313628885261)
                      ·
                        rfl

theorem cell23_7026600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7026600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026600 prefixEnd_7026600 := by exact prefixLift 7026600
  have htrace : WordTrace (prefixWord ++ tailWord_7026600) baseStart_7026600 baseEnd_7026600 := by
    simpa [prefixWord, tailWord_7026600, baseEnd_7026600] using wordTrace_append hprefix tailTrace_7026600
  have hstable : (prefixWord ++ tailWord_7026600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026600).length < 2 ^ (prefixWord ++ tailWord_7026600).sum := by decide
  have hdescent : baseEnd_7026600 < baseStart_7026600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026619 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 3, 8]
def baseStart_7026619 : Nat := 118140960795 + 7026619 * 2 ^ 59
def prefixEnd_7026619 : Nat := 4983230072969 + 3 ^ 40 * 7026619 * 2
def baseEnd_7026619 : Nat := 1202677641004916351515891

theorem tailTrace_7026619 : CollatzResearch.WordTrace tailWord_7026619 prefixEnd_7026619 1202677641004916351515891 := by
  unfold tailWord_7026619
  simp only [CollatzResearch.WordTrace]
  refine ⟨256281849330766888829370911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170854566220511259219580607 256281849330766888829370911)
  ·
    refine ⟨384422773996150333244056367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256281849330766888829370911 384422773996150333244056367)
    ·
      refine ⟨576634160994225499866084551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384422773996150333244056367 576634160994225499866084551)
      ·
        refine ⟨864951241491338249799126827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576634160994225499866084551 864951241491338249799126827)
        ·
          refine ⟨1297426862237007374698690241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864951241491338249799126827 1297426862237007374698690241)
          ·
            refine ⟨973070146677755531024017681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1297426862237007374698690241 973070146677755531024017681)
            ·
              refine ⟨729802610008316648268013261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 973070146677755531024017681 729802610008316648268013261)
              ·
                refine ⟨273675978753118743100504973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 729802610008316648268013261 273675978753118743100504973)
                ·
                  refine ⟨102628492032419528662689365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273675978753118743100504973 102628492032419528662689365)
                  ·
                    refine ⟨1202677641004916351515891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102628492032419528662689365 1202677641004916351515891)
                    ·
                      rfl

theorem cell23_7026619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 8].length) (baseStart_7026619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026619 prefixEnd_7026619 := by exact prefixLift 7026619
  have htrace : WordTrace (prefixWord ++ tailWord_7026619) baseStart_7026619 baseEnd_7026619 := by
    simpa [prefixWord, tailWord_7026619, baseEnd_7026619] using wordTrace_append hprefix tailTrace_7026619
  have hstable : (prefixWord ++ tailWord_7026619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026619).length < 2 ^ (prefixWord ++ tailWord_7026619).sum := by decide
  have hdescent : baseEnd_7026619 < baseStart_7026619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026656 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 4]
def baseStart_7026656 : Nat := 118140960795 + 7026656 * 2 ^ 59
def prefixEnd_7026656 : Nat := 4983230072969 + 3 ^ 40 * 7026656 * 2
def baseEnd_7026656 : Nat := 3608051921798965409785003

theorem tailTrace_7026656 : CollatzResearch.WordTrace tailWord_7026656 prefixEnd_7026656 3608051921798965409785003 := by
  unfold tailWord_7026656
  simp only [CollatzResearch.WordTrace]
  refine ⟨128141599415816422074233911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170855465887755229432311881 128141599415816422074233911)
  ·
    refine ⟨192212399123724633111350867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128141599415816422074233911 192212399123724633111350867)
    ·
      refine ⟨288318598685586949667026301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192212399123724633111350867 288318598685586949667026301)
      ·
        refine ⟨108119474507095106125134863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288318598685586949667026301 108119474507095106125134863)
        ·
          refine ⟨162179211760642659187702295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108119474507095106125134863 162179211760642659187702295)
          ·
            refine ⟨243268817640963988781553443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162179211760642659187702295 243268817640963988781553443)
            ·
              refine ⟨364903226461445983172330165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243268817640963988781553443 364903226461445983172330165)
              ·
                refine ⟨34209677480760560922405953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 364903226461445983172330165 34209677480760560922405953)
                ·
                  refine ⟨25657258110570420691804465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34209677480760560922405953 25657258110570420691804465)
                  ·
                    refine ⟨19242943582927815518853349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25657258110570420691804465 19242943582927815518853349)
                    ·
                      refine ⟨3608051921798965409785003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19242943582927815518853349 3608051921798965409785003)
                      ·
                        rfl

theorem cell23_7026656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_7026656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026656 prefixEnd_7026656 := by exact prefixLift 7026656
  have htrace : WordTrace (prefixWord ++ tailWord_7026656) baseStart_7026656 baseEnd_7026656 := by
    simpa [prefixWord, tailWord_7026656, baseEnd_7026656] using wordTrace_append hprefix tailTrace_7026656
  have hstable : (prefixWord ++ tailWord_7026656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026656).length < 2 ^ (prefixWord ++ tailWord_7026656).sum := by decide
  have hdescent : baseEnd_7026656 < baseStart_7026656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026666 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 9]
def baseStart_7026666 : Nat := 118140960795 + 7026666 * 2 ^ 59
def prefixEnd_7026666 : Nat := 4983230072969 + 3 ^ 40 * 7026666 * 2
def baseEnd_7026666 : Nat := 400895228511723374517773

theorem tailTrace_7026666 : CollatzResearch.WordTrace tailWord_7026666 prefixEnd_7026666 400895228511723374517773 := by
  unfold tailWord_7026666
  simp only [CollatzResearch.WordTrace]
  refine ⟨64070890890399153964082963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170855709041064410570887901 64070890890399153964082963)
  ·
    refine ⟨96106336335598730946124445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64070890890399153964082963 96106336335598730946124445)
    ·
      refine ⟨36039876125849524104796667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96106336335598730946124445 36039876125849524104796667)
      ·
        refine ⟨54059814188774286157195001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36039876125849524104796667 54059814188774286157195001)
        ·
          refine ⟨40544860641580714617896251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54059814188774286157195001 40544860641580714617896251)
          ·
            refine ⟨60817290962371071926844377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40544860641580714617896251 60817290962371071926844377)
            ·
              refine ⟨45612968221778303945133283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60817290962371071926844377 45612968221778303945133283)
              ·
                refine ⟨68419452332667455917699925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45612968221778303945133283 68419452332667455917699925)
                ·
                  refine ⟨400895228511723374517773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68419452332667455917699925 400895228511723374517773)
                  ·
                    rfl

theorem cell23_7026666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_7026666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026666 prefixEnd_7026666 := by exact prefixLift 7026666
  have htrace : WordTrace (prefixWord ++ tailWord_7026666) baseStart_7026666 baseEnd_7026666 := by
    simpa [prefixWord, tailWord_7026666, baseEnd_7026666] using wordTrace_append hprefix tailTrace_7026666
  have hstable : (prefixWord ++ tailWord_7026666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026666).length < 2 ^ (prefixWord ++ tailWord_7026666).sum := by decide
  have hdescent : baseEnd_7026666 < baseStart_7026666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026730 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 2, 5]
def baseStart_7026730 : Nat := 118140960795 + 7026730 * 2 ^ 59
def prefixEnd_7026730 : Nat := 4983230072969 + 3 ^ 40 * 7026730 * 2
def baseEnd_7026730 : Nat := 1202696639789132706753221

theorem tailTrace_7026730 : CollatzResearch.WordTrace tailWord_7026730 prefixEnd_7026730 1202696639789132706753221 := by
  unfold tailWord_7026730
  simp only [CollatzResearch.WordTrace]
  refine ⟨64071474458341188696665411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170857265222243169857774429 64071474458341188696665411)
  ·
    refine ⟨96107211687511783044998117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64071474458341188696665411 96107211687511783044998117)
    ·
      refine ⟨18020102191408459320937147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96107211687511783044998117 18020102191408459320937147)
      ·
        refine ⟨27030153287112688981405721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18020102191408459320937147 27030153287112688981405721)
        ·
          refine ⟨20272614965334516736054291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27030153287112688981405721 20272614965334516736054291)
          ·
            refine ⟨30408922448001775104081437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20272614965334516736054291 30408922448001775104081437)
            ·
              refine ⟨11403345918000665664030539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30408922448001775104081437 11403345918000665664030539)
              ·
                refine ⟨17105018877000998496045809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11403345918000665664030539 17105018877000998496045809)
                ·
                  refine ⟨12828764157750748872034357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17105018877000998496045809 12828764157750748872034357)
                  ·
                    refine ⟨1202696639789132706753221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12828764157750748872034357 1202696639789132706753221)
                    ·
                      rfl

theorem cell23_7026730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_7026730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026730 prefixEnd_7026730 := by exact prefixLift 7026730
  have htrace : WordTrace (prefixWord ++ tailWord_7026730) baseStart_7026730 baseEnd_7026730 := by
    simpa [prefixWord, tailWord_7026730, baseEnd_7026730] using wordTrace_append hprefix tailTrace_7026730
  have hstable : (prefixWord ++ tailWord_7026730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026730).length < 2 ^ (prefixWord ++ tailWord_7026730).sum := by decide
  have hdescent : baseEnd_7026730 < baseStart_7026730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026850 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_7026850 : Nat := 118140960795 + 7026850 * 2 ^ 59
def prefixEnd_7026850 : Nat := 4983230072969 + 3 ^ 40 * 7026850 * 2
def baseEnd_7026850 : Nat := 1202717179015312550253037

theorem tailTrace_7026850 : CollatzResearch.WordTrace tailWord_7026850 prefixEnd_7026850 1202717179015312550253037 := by
  unfold tailWord_7026850
  simp only [CollatzResearch.WordTrace]
  refine ⟨64072568648232503820257501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170860183061953343520686669 64072568648232503820257501)
  ·
    refine ⟨24027213243087188932596563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64072568648232503820257501 24027213243087188932596563)
    ·
      refine ⟨36040819864630783398894845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24027213243087188932596563 36040819864630783398894845)
      ·
        refine ⟨13515307449236543774585567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36040819864630783398894845 13515307449236543774585567)
        ·
          refine ⟨20272961173854815661878351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13515307449236543774585567 20272961173854815661878351)
          ·
            refine ⟨30409441760782223492817527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20272961173854815661878351 30409441760782223492817527)
            ·
              refine ⟨45614162641173335239226291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30409441760782223492817527 45614162641173335239226291)
              ·
                refine ⟨68421243961760002858839437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45614162641173335239226291 68421243961760002858839437)
                ·
                  refine ⟨25657966485660001072064789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68421243961760002858839437 25657966485660001072064789)
                  ·
                    refine ⟨1202717179015312550253037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25657966485660001072064789 1202717179015312550253037)
                    ·
                      rfl

theorem cell23_7026850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_7026850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026850 prefixEnd_7026850 := by exact prefixLift 7026850
  have htrace : WordTrace (prefixWord ++ tailWord_7026850) baseStart_7026850 baseEnd_7026850 := by
    simpa [prefixWord, tailWord_7026850, baseEnd_7026850] using wordTrace_append hprefix tailTrace_7026850
  have hstable : (prefixWord ++ tailWord_7026850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026850).length < 2 ^ (prefixWord ++ tailWord_7026850).sum := by decide
  have hdescent : baseEnd_7026850 < baseStart_7026850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026880 : List Nat := [2, 1, 1, 2, 5, 3, 1, 8]
def baseStart_7026880 : Nat := 118140960795 + 7026880 * 2 ^ 59
def prefixEnd_7026880 : Nat := 4983230072969 + 3 ^ 40 * 7026880 * 2
def baseEnd_7026880 : Nat := 133635812646873056791999

theorem tailTrace_7026880 : CollatzResearch.WordTrace tailWord_7026880 prefixEnd_7026880 133635812646873056791999 := by
  unfold tailWord_7026880
  simp only [CollatzResearch.WordTrace]
  refine ⟨128145684391410665202311047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170860912521880886936414729 128145684391410665202311047)
  ·
    refine ⟨192218526587115997803466571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128145684391410665202311047 192218526587115997803466571)
    ·
      refine ⟨288327789880673996705199857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192218526587115997803466571 288327789880673996705199857)
      ·
        refine ⟨216245842410505497528899893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288327789880673996705199857 216245842410505497528899893)
        ·
          refine ⟨20273047725984890393334365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216245842410505497528899893 20273047725984890393334365)
          ·
            refine ⟨7602392897244333897500387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20273047725984890393334365 7602392897244333897500387)
            ·
              refine ⟨11403589345866500846250581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7602392897244333897500387 11403589345866500846250581)
              ·
                refine ⟨133635812646873056791999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11403589345866500846250581 133635812646873056791999)
                ·
                  rfl

theorem cell23_7026880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 8].length) (baseStart_7026880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026880 prefixEnd_7026880 := by exact prefixLift 7026880
  have htrace : WordTrace (prefixWord ++ tailWord_7026880) baseStart_7026880 baseEnd_7026880 := by
    simpa [prefixWord, tailWord_7026880, baseEnd_7026880] using wordTrace_append hprefix tailTrace_7026880
  have hstable : (prefixWord ++ tailWord_7026880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026880).length < 2 ^ (prefixWord ++ tailWord_7026880).sum := by decide
  have hdescent : baseEnd_7026880 < baseStart_7026880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026903 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_7026903 : Nat := 118140960795 + 7026903 * 2 ^ 59
def prefixEnd_7026903 : Nat := 4983230072969 + 3 ^ 40 * 7026903 * 2
def baseEnd_7026903 : Nat := 3608178751520625943396367

theorem tailTrace_7026903 : CollatzResearch.WordTrace tailWord_7026903 prefixEnd_7026903 3608178751520625943396367 := by
  unfold tailWord_7026903
  simp only [CollatzResearch.WordTrace]
  refine ⟨256292207661738005332709363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170861471774492003555139575 256292207661738005332709363)
  ·
    refine ⟨384438311492607007999064045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 256292207661738005332709363 384438311492607007999064045)
    ·
      refine ⟨144164366809727627999649017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 384438311492607007999064045 144164366809727627999649017)
      ·
        refine ⟨108123275107295720999736763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144164366809727627999649017 108123275107295720999736763)
        ·
          refine ⟨162184912660943581499605145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108123275107295720999736763 162184912660943581499605145)
          ·
            refine ⟨121638684495707686124703859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162184912660943581499605145 121638684495707686124703859)
            ·
              refine ⟨182458026743561529187055789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121638684495707686124703859 182458026743561529187055789)
              ·
                refine ⟨68421760028835573445145921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182458026743561529187055789 68421760028835573445145921)
                ·
                  refine ⟨51316320021626680083859441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68421760028835573445145921 51316320021626680083859441)
                  ·
                    refine ⟨38487240016220010062894581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51316320021626680083859441 38487240016220010062894581)
                    ·
                      refine ⟨3608178751520625943396367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38487240016220010062894581 3608178751520625943396367)
                      ·
                        rfl

theorem cell23_7026903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_7026903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026903 prefixEnd_7026903 := by exact prefixLift 7026903
  have htrace : WordTrace (prefixWord ++ tailWord_7026903) baseStart_7026903 baseEnd_7026903 := by
    simpa [prefixWord, tailWord_7026903, baseEnd_7026903] using wordTrace_append hprefix tailTrace_7026903
  have hstable : (prefixWord ++ tailWord_7026903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026903).length < 2 ^ (prefixWord ++ tailWord_7026903).sum := by decide
  have hdescent : baseEnd_7026903 < baseStart_7026903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7026908 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_7026908 : Nat := 118140960795 + 7026908 * 2 ^ 59
def prefixEnd_7026908 : Nat := 4983230072969 + 3 ^ 40 * 7026908 * 2
def baseEnd_7026908 : Nat := 3608181318923898423833845

theorem tailTrace_7026908 : CollatzResearch.WordTrace tailWord_7026908 prefixEnd_7026908 3608181318923898423833845 := by
  unfold tailWord_7026908
  simp only [CollatzResearch.WordTrace]
  refine ⟨128146195013359945593320689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170861593351146594124427585 128146195013359945593320689)
  ·
    refine ⟨96109646260019959194990517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128146195013359945593320689 96109646260019959194990517)
    ·
      refine ⟨9010279336876871174530361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96109646260019959194990517 9010279336876871174530361)
      ·
        refine ⟨6757709502657653380897771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9010279336876871174530361 6757709502657653380897771)
        ·
          refine ⟨10136564253986480071346657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6757709502657653380897771 10136564253986480071346657)
          ·
            refine ⟨7602423190489860053509993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10136564253986480071346657 7602423190489860053509993)
            ·
              refine ⟨5701817392867395040132495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7602423190489860053509993 5701817392867395040132495)
              ·
                refine ⟨8552726089301092560198743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5701817392867395040132495 8552726089301092560198743)
                ·
                  refine ⟨12829089133951638840298115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8552726089301092560198743 12829089133951638840298115)
                  ·
                    refine ⟨19243633700927458260447173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12829089133951638840298115 19243633700927458260447173)
                    ·
                      refine ⟨3608181318923898423833845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19243633700927458260447173 3608181318923898423833845)
                      ·
                        rfl

theorem cell23_7026908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_7026908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7026908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7026908 prefixEnd_7026908 := by exact prefixLift 7026908
  have htrace : WordTrace (prefixWord ++ tailWord_7026908) baseStart_7026908 baseEnd_7026908 := by
    simpa [prefixWord, tailWord_7026908, baseEnd_7026908] using wordTrace_append hprefix tailTrace_7026908
  have hstable : (prefixWord ++ tailWord_7026908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7026908).length < 2 ^ (prefixWord ++ tailWord_7026908).sum := by decide
  have hdescent : baseEnd_7026908 < baseStart_7026908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7026908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
