import V185TrunkScan22Chunk302

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2701495 : List Nat := [1, 1, 3, 1, 4, 2, 4, 6]
def baseStart_2701495 : Nat := 118140960795 + 2701495 * 2 ^ 59
def prefixEnd_2701495 : Nat := 4983230072969 + 3 ^ 40 * 2701495 * 2
def baseEnd_2701495 : Nat := 102752994127260231265819

theorem tailTrace_2701495 : CollatzResearch.WordTrace tailWord_2701495 prefixEnd_2701495 102752994127260231265819 := by
  unfold tailWord_2701495
  simp only [CollatzResearch.WordTrace]
  refine ⟨98531617347952468458881939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65687744898634978972587959 98531617347952468458881939)
  ·
    refine ⟨147797426021928702688322909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98531617347952468458881939 147797426021928702688322909)
    ·
      refine ⟨55424034758223263508121091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147797426021928702688322909 55424034758223263508121091)
      ·
        refine ⟨83136052137334895262181637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55424034758223263508121091 83136052137334895262181637)
        ·
          refine ⟨15588009775750292861659057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83136052137334895262181637 15588009775750292861659057)
          ·
            refine ⟨11691007331812719646244293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15588009775750292861659057 11691007331812719646244293)
            ·
              refine ⟨2192063874714884933670805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11691007331812719646244293 2192063874714884933670805)
              ·
                refine ⟨102752994127260231265819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2192063874714884933670805 102752994127260231265819)
                ·
                  rfl

theorem cell22_2701495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 6].length) (baseStart_2701495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701495 prefixEnd_2701495 := by exact prefixLift 2701495
  have htrace : WordTrace (prefixWord ++ tailWord_2701495) baseStart_2701495 baseEnd_2701495 := by
    simpa [prefixWord, tailWord_2701495, baseEnd_2701495] using wordTrace_append hprefix tailTrace_2701495
  have hstable : (prefixWord ++ tailWord_2701495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701495).length < 2 ^ (prefixWord ++ tailWord_2701495).sum := by decide
  have hdescent : baseEnd_2701495 < baseStart_2701495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701602 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_2701602 : Nat := 118140960795 + 2701602 * 2 ^ 59
def prefixEnd_2701602 : Nat := 4983230072969 + 3 ^ 40 * 2701602 * 2
def baseEnd_2701602 : Nat := 308271191810676489655681

theorem tailTrace_2701602 : CollatzResearch.WordTrace tailWord_2701602 prefixEnd_2701602 308271191810676489655681 := by
  unfold tailWord_2701602
  simp only [CollatzResearch.WordTrace]
  refine ⟨24633879989641206433256765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65690346639043217155351373 24633879989641206433256765)
  ·
    refine ⟨9237704996115452412471287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24633879989641206433256765 9237704996115452412471287)
    ·
      refine ⟨13856557494173178618706931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9237704996115452412471287 13856557494173178618706931)
      ·
        refine ⟨20784836241259767928060397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13856557494173178618706931 20784836241259767928060397)
        ·
          refine ⟨7794313590472412973022649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20784836241259767928060397 7794313590472412973022649)
          ·
            refine ⟨5845735192854309729766987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7794313590472412973022649 5845735192854309729766987)
            ·
              refine ⟨8768602789281464594650481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845735192854309729766987 8768602789281464594650481)
              ·
                refine ⟨6576452091961098445987861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8768602789281464594650481 6576452091961098445987861)
                ·
                  refine ⟨308271191810676489655681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6576452091961098445987861 308271191810676489655681)
                  ·
                    rfl

theorem cell22_2701602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_2701602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701602 prefixEnd_2701602 := by exact prefixLift 2701602
  have htrace : WordTrace (prefixWord ++ tailWord_2701602) baseStart_2701602 baseEnd_2701602 := by
    simpa [prefixWord, tailWord_2701602, baseEnd_2701602] using wordTrace_append hprefix tailTrace_2701602
  have hstable : (prefixWord ++ tailWord_2701602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701602).length < 2 ^ (prefixWord ++ tailWord_2701602).sum := by decide
  have hdescent : baseEnd_2701602 < baseStart_2701602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701664 : List Nat := [2, 1, 1, 3, 5, 2, 2, 6]
def baseStart_2701664 : Nat := 118140960795 + 2701664 * 2 ^ 59
def prefixEnd_2701664 : Nat := 4983230072969 + 3 ^ 40 * 2701664 * 2
def baseEnd_2701664 : Nat := 102759422144342441546317

theorem tailTrace_2701664 : CollatzResearch.WordTrace tailWord_2701664 prefixEnd_2701664 102759422144342441546317 := by
  unfold tailWord_2701664
  simp only [CollatzResearch.WordTrace]
  refine ⟨49268890642170105160892023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65691854189560140214522697 49268890642170105160892023)
  ·
    refine ⟨73903335963255157741338035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49268890642170105160892023 73903335963255157741338035)
    ·
      refine ⟨110855003944882736612007053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73903335963255157741338035 110855003944882736612007053)
      ·
        refine ⟨41570626479331026229502645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110855003944882736612007053 41570626479331026229502645)
        ·
          refine ⟨3897246232437283709015873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41570626479331026229502645 3897246232437283709015873)
          ·
            refine ⟨2922934674327962781761905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3897246232437283709015873 2922934674327962781761905)
            ·
              refine ⟨2192201005745972086321429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2922934674327962781761905 2192201005745972086321429)
              ·
                refine ⟨102759422144342441546317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2192201005745972086321429 102759422144342441546317)
                ·
                  rfl

theorem cell22_2701664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 6].length) (baseStart_2701664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701664 prefixEnd_2701664 := by exact prefixLift 2701664
  have htrace : WordTrace (prefixWord ++ tailWord_2701664) baseStart_2701664 baseEnd_2701664 := by
    simpa [prefixWord, tailWord_2701664, baseEnd_2701664] using wordTrace_append hprefix tailTrace_2701664
  have hstable : (prefixWord ++ tailWord_2701664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701664).length < 2 ^ (prefixWord ++ tailWord_2701664).sum := by decide
  have hdescent : baseEnd_2701664 < baseStart_2701664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701679 : List Nat := [1, 1, 2, 1, 3, 1, 2, 7, 1, 3]
def baseStart_2701679 : Nat := 118140960795 + 2701679 * 2 ^ 59
def prefixEnd_2701679 : Nat := 4983230072969 + 3 ^ 40 * 2701679 * 2
def baseEnd_2701679 : Nat := 924839934105626934791807

theorem tailTrace_2701679 : CollatzResearch.WordTrace tailWord_2701679 prefixEnd_2701679 924839934105626934791807 := by
  unfold tailWord_2701679
  simp only [CollatzResearch.WordTrace]
  refine ⟨98538328379285867883580091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65692218919523911922386727 98538328379285867883580091)
  ·
    refine ⟨147807492568928801825370137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98538328379285867883580091 147807492568928801825370137)
    ·
      refine ⟨110855619426696601369027603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147807492568928801825370137 110855619426696601369027603)
      ·
        refine ⟨166283429140044902053541405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110855619426696601369027603 166283429140044902053541405)
        ·
          refine ⟨62356285927516838270078027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166283429140044902053541405 62356285927516838270078027)
          ·
            refine ⟨93534428891275257405117041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62356285927516838270078027 93534428891275257405117041)
            ·
              refine ⟨70150821668456443053837781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93534428891275257405117041 70150821668456443053837781)
              ·
                refine ⟨1644159882854447884074323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70150821668456443053837781 1644159882854447884074323)
                ·
                  refine ⟨2466239824281671826111485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644159882854447884074323 2466239824281671826111485)
                  ·
                    refine ⟨924839934105626934791807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2466239824281671826111485 924839934105626934791807)
                    ·
                      rfl

theorem cell22_2701679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 7, 1, 3].length) (baseStart_2701679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701679 prefixEnd_2701679 := by exact prefixLift 2701679
  have htrace : WordTrace (prefixWord ++ tailWord_2701679) baseStart_2701679 baseEnd_2701679 := by
    simpa [prefixWord, tailWord_2701679, baseEnd_2701679] using wordTrace_append hprefix tailTrace_2701679
  have hstable : (prefixWord ++ tailWord_2701679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701679).length < 2 ^ (prefixWord ++ tailWord_2701679).sum := by decide
  have hdescent : baseEnd_2701679 < baseStart_2701679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701769 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 2, 3]
def baseStart_2701769 : Nat := 118140960795 + 2701769 * 2 ^ 59
def prefixEnd_2701769 : Nat := 4983230072969 + 3 ^ 40 * 2701769 * 2
def baseEnd_2701769 : Nat := 924870742944896700041531

theorem tailTrace_2701769 : CollatzResearch.WordTrace tailWord_2701769 prefixEnd_2701769 924870742944896700041531 := by
  unfold tailWord_2701769
  simp only [CollatzResearch.WordTrace]
  refine ⟨98541610948959813254356361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65694407299306542169570907 98541610948959813254356361)
  ·
    refine ⟨73906208211719859940767271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98541610948959813254356361 73906208211719859940767271)
    ·
      refine ⟨110859312317579789911150907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73906208211719859940767271 110859312317579789911150907)
      ·
        refine ⟨166288968476369684866726361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110859312317579789911150907 166288968476369684866726361)
        ·
          refine ⟨124716726357277263650044771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166288968476369684866726361 124716726357277263650044771)
          ·
            refine ⟨187075089535915895475067157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124716726357277263650044771 187075089535915895475067157)
            ·
              refine ⟨8769144821996057600393773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187075089535915895475067157 8769144821996057600393773)
              ·
                refine ⟨3288429308248521600147665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8769144821996057600393773 3288429308248521600147665)
                ·
                  refine ⟨2466321981186391200110749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3288429308248521600147665 2466321981186391200110749)
                  ·
                    refine ⟨924870742944896700041531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2466321981186391200110749 924870742944896700041531)
                    ·
                      rfl

theorem cell22_2701769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 2, 3].length) (baseStart_2701769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701769 prefixEnd_2701769 := by exact prefixLift 2701769
  have htrace : WordTrace (prefixWord ++ tailWord_2701769) baseStart_2701769 baseEnd_2701769 := by
    simpa [prefixWord, tailWord_2701769, baseEnd_2701769] using wordTrace_append hprefix tailTrace_2701769
  have hstable : (prefixWord ++ tailWord_2701769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701769).length < 2 ^ (prefixWord ++ tailWord_2701769).sum := by decide
  have hdescent : baseEnd_2701769 < baseStart_2701769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701848 : List Nat := [2, 1, 2, 3, 3, 1, 3, 3, 1, 3]
def baseStart_2701848 : Nat := 118140960795 + 2701848 * 2 ^ 59
def prefixEnd_2701848 : Nat := 4983230072969 + 3 ^ 40 * 2701848 * 2
def baseEnd_2701848 : Nat := 924897786259366827316289

theorem tailTrace_2701848 : CollatzResearch.WordTrace tailWord_2701848 prefixEnd_2701848 924897786259366827316289 := by
  unfold tailWord_2701848
  simp only [CollatzResearch.WordTrace]
  refine ⟨49272246157836804873241099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65696328210449073164321465 49272246157836804873241099)
  ·
    refine ⟨73908369236755207309861649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49272246157836804873241099 73908369236755207309861649)
    ·
      refine ⟨55431276927566405482396237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73908369236755207309861649 55431276927566405482396237)
      ·
        refine ⟨20786728847837402055898589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55431276927566405482396237 20786728847837402055898589)
        ·
          refine ⟨7795023317939025770961971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20786728847837402055898589 7795023317939025770961971)
          ·
            refine ⟨11692534976908538656442957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7795023317939025770961971 11692534976908538656442957)
            ·
              refine ⟨4384700616340701996166109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11692534976908538656442957 4384700616340701996166109)
              ·
                refine ⟨1644262731127763248562291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4384700616340701996166109 1644262731127763248562291)
                ·
                  refine ⟨2466394096691644872843437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644262731127763248562291 2466394096691644872843437)
                  ·
                    refine ⟨924897786259366827316289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2466394096691644872843437 924897786259366827316289)
                    ·
                      rfl

theorem cell22_2701848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_2701848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701848 prefixEnd_2701848 := by exact prefixLift 2701848
  have htrace : WordTrace (prefixWord ++ tailWord_2701848) baseStart_2701848 baseEnd_2701848 := by
    simpa [prefixWord, tailWord_2701848, baseEnd_2701848] using wordTrace_append hprefix tailTrace_2701848
  have hstable : (prefixWord ++ tailWord_2701848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701848).length < 2 ^ (prefixWord ++ tailWord_2701848).sum := by decide
  have hdescent : baseEnd_2701848 < baseStart_2701848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701878 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_2701878 : Nat := 118140960795 + 2701878 * 2 ^ 59
def prefixEnd_2701878 : Nat := 4983230072969 + 3 ^ 40 * 2701878 * 2
def baseEnd_2701878 : Nat := 308302685290818916355399

theorem tailTrace_2701878 : CollatzResearch.WordTrace tailWord_2701878 prefixEnd_2701878 308302685290818916355399 := by
  unfold tailWord_2701878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6159099156597807804379643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65697057670376616580049525 6159099156597807804379643)
  ·
    refine ⟨9238648734896711706569465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6159099156597807804379643 9238648734896711706569465)
    ·
      refine ⟨6928986551172533779927099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9238648734896711706569465 6928986551172533779927099)
      ·
        refine ⟨10393479826758800669890649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6928986551172533779927099 10393479826758800669890649)
        ·
          refine ⟨7795109870069100502417987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10393479826758800669890649 7795109870069100502417987)
          ·
            refine ⟨11692664805103650753626981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7795109870069100502417987 11692664805103650753626981)
            ·
              refine ⟨2192374650956934516305059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11692664805103650753626981 2192374650956934516305059)
              ·
                refine ⟨3288561976435401774457589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192374650956934516305059 3288561976435401774457589)
                ·
                  refine ⟨308302685290818916355399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3288561976435401774457589 308302685290818916355399)
                  ·
                    rfl

theorem cell22_2701878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_2701878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701878 prefixEnd_2701878 := by exact prefixLift 2701878
  have htrace : WordTrace (prefixWord ++ tailWord_2701878) baseStart_2701878 baseEnd_2701878 := by
    simpa [prefixWord, tailWord_2701878, baseEnd_2701878] using wordTrace_append hprefix tailTrace_2701878
  have hstable : (prefixWord ++ tailWord_2701878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701878).length < 2 ^ (prefixWord ++ tailWord_2701878).sum := by decide
  have hdescent : baseEnd_2701878 < baseStart_2701878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701904 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 4, 3]
def baseStart_2701904 : Nat := 118140960795 + 2701904 * 2 ^ 59
def prefixEnd_2701904 : Nat := 4983230072969 + 3 ^ 40 * 2701904 * 2
def baseEnd_2701904 : Nat := 924916956203801347916117

theorem tailTrace_2701904 : CollatzResearch.WordTrace tailWord_2701904 prefixEnd_2701904 924916956203801347916117 := by
  unfold tailWord_2701904
  simp only [CollatzResearch.WordTrace]
  refine ⟨49273267401735365655260383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65697689868980487540347177 49273267401735365655260383)
  ·
    refine ⟨73909901102603048482890575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49273267401735365655260383 73909901102603048482890575)
    ·
      refine ⟨110864851653904572724335863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73909901102603048482890575 110864851653904572724335863)
      ·
        refine ⟨166297277480856859086503795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110864851653904572724335863 166297277480856859086503795)
        ·
          refine ⟨249445916221285288629755693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166297277480856859086503795 249445916221285288629755693)
          ·
            refine ⟨93542218582981983236158385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249445916221285288629755693 93542218582981983236158385)
            ·
              refine ⟨70156663937236487427118789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93542218582981983236158385 70156663937236487427118789)
              ·
                refine ⟨13154374488231841392584773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70156663937236487427118789 13154374488231841392584773)
                ·
                  refine ⟨2466445216543470261109645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13154374488231841392584773 2466445216543470261109645)
                  ·
                    refine ⟨924916956203801347916117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2466445216543470261109645 924916956203801347916117)
                    ·
                      rfl

theorem cell22_2701904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4, 3].length) (baseStart_2701904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701904 prefixEnd_2701904 := by exact prefixLift 2701904
  have htrace : WordTrace (prefixWord ++ tailWord_2701904) baseStart_2701904 baseEnd_2701904 := by
    simpa [prefixWord, tailWord_2701904, baseEnd_2701904] using wordTrace_append hprefix tailTrace_2701904
  have hstable : (prefixWord ++ tailWord_2701904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701904).length < 2 ^ (prefixWord ++ tailWord_2701904).sum := by decide
  have hdescent : baseEnd_2701904 < baseStart_2701904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701906 : List Nat := [3, 2, 2, 1, 2, 1, 2, 5, 4]
def baseStart_2701906 : Nat := 118140960795 + 2701906 * 2 ^ 59
def prefixEnd_2701906 : Nat := 4983230072969 + 3 ^ 40 * 2701906 * 2
def baseEnd_2701906 : Nat := 308305880281558003122037

theorem tailTrace_2701906 : CollatzResearch.WordTrace tailWord_2701906 prefixEnd_2701906 308305880281558003122037 := by
  unfold tailWord_2701906
  simp only [CollatzResearch.WordTrace]
  refine ⟨24636651937365871413023393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65697738499642323768062381 24636651937365871413023393)
  ·
    refine ⟨18477488953024403559767545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24636651937365871413023393 18477488953024403559767545)
    ·
      refine ⟨13858116714768302669825659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18477488953024403559767545 13858116714768302669825659)
      ·
        refine ⟨20787175072152454004738489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13858116714768302669825659 20787175072152454004738489)
        ·
          refine ⟨15590381304114340503553867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20787175072152454004738489 15590381304114340503553867)
          ·
            refine ⟨23385571956171510755330801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15590381304114340503553867 23385571956171510755330801)
            ·
              refine ⟨17539178967128633066498101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23385571956171510755330801 17539178967128633066498101)
              ·
                refine ⟨1644298028168309349984197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17539178967128633066498101 1644298028168309349984197)
                ·
                  refine ⟨308305880281558003122037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1644298028168309349984197 308305880281558003122037)
                  ·
                    rfl

theorem cell22_2701906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_2701906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701906 prefixEnd_2701906 := by exact prefixLift 2701906
  have htrace : WordTrace (prefixWord ++ tailWord_2701906) baseStart_2701906 baseEnd_2701906 := by
    simpa [prefixWord, tailWord_2701906, baseEnd_2701906] using wordTrace_append hprefix tailTrace_2701906
  have hstable : (prefixWord ++ tailWord_2701906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701906).length < 2 ^ (prefixWord ++ tailWord_2701906).sum := by decide
  have hdescent : baseEnd_2701906 < baseStart_2701906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701908 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_2701908 : Nat := 118140960795 + 2701908 * 2 ^ 59
def prefixEnd_2701908 : Nat := 4983230072969 + 3 ^ 40 * 2701908 * 2
def baseEnd_2701908 : Nat := 924918325485546670816105

theorem tailTrace_2701908 : CollatzResearch.WordTrace tailWord_2701908 prefixEnd_2701908 924918325485546670816105 := by
  unfold tailWord_2701908
  simp only [CollatzResearch.WordTrace]
  refine ⟨49273340347728119996833189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65697787130304159995777585 49273340347728119996833189)
  ·
    refine ⟨9238751315199022499406223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49273340347728119996833189 9238751315199022499406223)
    ·
      refine ⟨13858126972798533749109335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9238751315199022499406223 13858126972798533749109335)
      ·
        refine ⟨20787190459197800623664003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13858126972798533749109335 20787190459197800623664003)
        ·
          refine ⟨31180785688796700935496005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20787190459197800623664003 31180785688796700935496005)
          ·
            refine ⟨5846397316649381425405501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31180785688796700935496005 5846397316649381425405501)
            ·
              refine ⟨2192398993743518034527063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5846397316649381425405501 2192398993743518034527063)
              ·
                refine ⟨3288598490615277051790595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192398993743518034527063 3288598490615277051790595)
                ·
                  refine ⟨4932897735922915577685893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3288598490615277051790595 4932897735922915577685893)
                  ·
                    refine ⟨924918325485546670816105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4932897735922915577685893 924918325485546670816105)
                    ·
                      rfl

theorem cell22_2701908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_2701908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701908 prefixEnd_2701908 := by exact prefixLift 2701908
  have htrace : WordTrace (prefixWord ++ tailWord_2701908) baseStart_2701908 baseEnd_2701908 := by
    simpa [prefixWord, tailWord_2701908, baseEnd_2701908] using wordTrace_append hprefix tailTrace_2701908
  have hstable : (prefixWord ++ tailWord_2701908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701908).length < 2 ^ (prefixWord ++ tailWord_2701908).sum := by decide
  have hdescent : baseEnd_2701908 < baseStart_2701908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701921 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 2, 3]
def baseStart_2701921 : Nat := 118140960795 + 2701921 * 2 ^ 59
def prefixEnd_2701921 : Nat := 4983230072969 + 3 ^ 40 * 2701921 * 2
def baseEnd_2701921 : Nat := 924922775651218970241065

theorem tailTrace_2701921 : CollatzResearch.WordTrace tailWord_2701921 prefixEnd_2701921 924922775651218970241065 := by
  unfold tailWord_2701921
  simp only [CollatzResearch.WordTrace]
  refine ⟨98547154844409143213889617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65698103229606095475926411 98547154844409143213889617)
  ·
    refine ⟨73910366133306857410417213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98547154844409143213889617 73910366133306857410417213)
    ·
      refine ⟨27716387299990071528906455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73910366133306857410417213 27716387299990071528906455)
      ·
        refine ⟨41574580949985107293359683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27716387299990071528906455 41574580949985107293359683)
        ·
          refine ⟨62361871424977660940039525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41574580949985107293359683 62361871424977660940039525)
          ·
            refine ⟨11692850892183311426257411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62361871424977660940039525 11692850892183311426257411)
            ·
              refine ⟨17539276338274967139386117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11692850892183311426257411 17539276338274967139386117)
              ·
                refine ⟨3288614313426556338634897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17539276338274967139386117 3288614313426556338634897)
                ·
                  refine ⟨2466460735069917253976173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3288614313426556338634897 2466460735069917253976173)
                  ·
                    refine ⟨924922775651218970241065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2466460735069917253976173 924922775651218970241065)
                    ·
                      rfl

theorem cell22_2701921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_2701921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701921 prefixEnd_2701921 := by exact prefixLift 2701921
  have htrace : WordTrace (prefixWord ++ tailWord_2701921) baseStart_2701921 baseEnd_2701921 := by
    simpa [prefixWord, tailWord_2701921, baseEnd_2701921] using wordTrace_append hprefix tailTrace_2701921
  have hstable : (prefixWord ++ tailWord_2701921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701921).length < 2 ^ (prefixWord ++ tailWord_2701921).sum := by decide
  have hdescent : baseEnd_2701921 < baseStart_2701921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2701966 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_2701966 : Nat := 118140960795 + 2701966 * 2 ^ 59
def prefixEnd_2701966 : Nat := 4983230072969 + 3 ^ 40 * 2701966 * 2
def baseEnd_2701966 : Nat := 924938180070853852865927

theorem tailTrace_2701966 : CollatzResearch.WordTrace tailWord_2701966 prefixEnd_2701966 924938180070853852865927 := by
  unfold tailWord_2701966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12318599516155764487409719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65699197419497410599518501 12318599516155764487409719)
  ·
    refine ⟨18477899274233646731114579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12318599516155764487409719 18477899274233646731114579)
    ·
      refine ⟨27716848911350470096671869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18477899274233646731114579 27716848911350470096671869)
      ·
        refine ⟨10393818341756426286251951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27716848911350470096671869 10393818341756426286251951)
        ·
          refine ⟨15590727512634639429377927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10393818341756426286251951 15590727512634639429377927)
          ·
            refine ⟨23386091268951959144066891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15590727512634639429377927 23386091268951959144066891)
            ·
              refine ⟨35079136903427938716100337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23386091268951959144066891 35079136903427938716100337)
              ·
                refine ⟨26309352677570954037075253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35079136903427938716100337 26309352677570954037075253)
                ·
                  refine ⟨2466501813522276940975805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26309352677570954037075253 2466501813522276940975805)
                  ·
                    refine ⟨924938180070853852865927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2466501813522276940975805 924938180070853852865927)
                    ·
                      rfl

theorem cell22_2701966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_2701966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2701966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2701966 prefixEnd_2701966 := by exact prefixLift 2701966
  have htrace : WordTrace (prefixWord ++ tailWord_2701966) baseStart_2701966 baseEnd_2701966 := by
    simpa [prefixWord, tailWord_2701966, baseEnd_2701966] using wordTrace_append hprefix tailTrace_2701966
  have hstable : (prefixWord ++ tailWord_2701966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2701966).length < 2 ^ (prefixWord ++ tailWord_2701966).sum := by decide
  have hdescent : baseEnd_2701966 < baseStart_2701966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2701966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702099 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 1, 8]
def baseStart_2702099 : Nat := 118140960795 + 2702099 * 2 ^ 59
def prefixEnd_2702099 : Nat := 4983230072969 + 3 ^ 40 * 2702099 * 2
def baseEnd_2702099 : Nat := 924983708688885839290519

theorem tailTrace_2702099 : CollatzResearch.WordTrace tailWord_2702099 prefixEnd_2702099 924983708688885839290519 := by
  unfold tailWord_2702099
  simp only [CollatzResearch.WordTrace]
  refine ⟨98553647037764279613869351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65702431358509519742579567 98553647037764279613869351)
  ·
    refine ⟨147830470556646419420804027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98553647037764279613869351 147830470556646419420804027)
    ·
      refine ⟨221745705834969629131206041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147830470556646419420804027 221745705834969629131206041)
      ·
        refine ⟨166309279376227221848404531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221745705834969629131206041 166309279376227221848404531)
        ·
          refine ⟨249463919064340832772606797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166309279376227221848404531 249463919064340832772606797)
          ·
            refine ⟨93548969649127812289727549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249463919064340832772606797 93548969649127812289727549)
            ·
              refine ⟨35080863618422929608647831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93548969649127812289727549 35080863618422929608647831)
              ·
                refine ⟨52621295427634394412971747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35080863618422929608647831 52621295427634394412971747)
                ·
                  refine ⟨78931943141451591619457621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52621295427634394412971747 78931943141451591619457621)
                  ·
                    refine ⟨924983708688885839290519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78931943141451591619457621 924983708688885839290519)
                    ·
                      rfl

theorem cell22_2702099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_2702099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702099 prefixEnd_2702099 := by exact prefixLift 2702099
  have htrace : WordTrace (prefixWord ++ tailWord_2702099) baseStart_2702099 baseEnd_2702099 := by
    simpa [prefixWord, tailWord_2702099, baseEnd_2702099] using wordTrace_append hprefix tailTrace_2702099
  have hstable : (prefixWord ++ tailWord_2702099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702099).length < 2 ^ (prefixWord ++ tailWord_2702099).sum := by decide
  have hdescent : baseEnd_2702099 < baseStart_2702099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702103 : List Nat := [1, 1, 3, 4, 3, 2, 1, 7]
def baseStart_2702103 : Nat := 118140960795 + 2702103 * 2 ^ 59
def prefixEnd_2702103 : Nat := 4983230072969 + 3 ^ 40 * 2702103 * 2
def baseEnd_2702103 : Nat := 102776119774514573576723

theorem tailTrace_2702103 : CollatzResearch.WordTrace tailWord_2702103 prefixEnd_2702103 102776119774514573576723 := by
  unfold tailWord_2702103
  simp only [CollatzResearch.WordTrace]
  refine ⟨98553792929749788297014963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65702528619833192198009975 98553792929749788297014963)
  ·
    refine ⟨147830689394624682445522445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98553792929749788297014963 147830689394624682445522445)
    ·
      refine ⟨55436508522984255917070917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147830689394624682445522445 55436508522984255917070917)
      ·
        refine ⟨10394345348059547984450797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55436508522984255917070917 10394345348059547984450797)
        ·
          refine ⟨3897879505522330494169049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10394345348059547984450797 3897879505522330494169049)
          ·
            refine ⟨2923409629141747870626787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3897879505522330494169049 2923409629141747870626787)
            ·
              refine ⟨4385114443712621805940181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923409629141747870626787 4385114443712621805940181)
              ·
                refine ⟨102776119774514573576723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4385114443712621805940181 102776119774514573576723)
                ·
                  rfl

theorem cell22_2702103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 7].length) (baseStart_2702103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702103 prefixEnd_2702103 := by exact prefixLift 2702103
  have htrace : WordTrace (prefixWord ++ tailWord_2702103) baseStart_2702103 baseEnd_2702103 := by
    simpa [prefixWord, tailWord_2702103, baseEnd_2702103] using wordTrace_append hprefix tailTrace_2702103
  have hstable : (prefixWord ++ tailWord_2702103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702103).length < 2 ^ (prefixWord ++ tailWord_2702103).sum := by decide
  have hdescent : baseEnd_2702103 < baseStart_2702103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702122 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 2, 4]
def baseStart_2702122 : Nat := 118140960795 + 2702122 * 2 ^ 59
def prefixEnd_2702122 : Nat := 4983230072969 + 3 ^ 40 * 2702122 * 2
def baseEnd_2702122 : Nat := 924991582058921445965449

theorem tailTrace_2702122 : CollatzResearch.WordTrace tailWord_2702122 prefixEnd_2702122 924991582058921445965449 := by
  unfold tailWord_2702122
  simp only [CollatzResearch.WordTrace]
  refine ⟨24638621479170238635489155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65702990611120636361304413 24638621479170238635489155)
  ·
    refine ⟨36957932218755357953233733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24638621479170238635489155 36957932218755357953233733)
    ·
      refine ⟨6929612291016629616231325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36957932218755357953233733 6929612291016629616231325)
      ·
        refine ⟨2598604609131236106086747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6929612291016629616231325 2598604609131236106086747)
        ·
          refine ⟨3897906913696854159130121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2598604609131236106086747 3897906913696854159130121)
          ·
            refine ⟨2923430185272640619347591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3897906913696854159130121 2923430185272640619347591)
            ·
              refine ⟨4385145277908960929021387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923430185272640619347591 4385145277908960929021387)
              ·
                refine ⟨6577717916863441393532081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4385145277908960929021387 6577717916863441393532081)
                ·
                  refine ⟨4933288437647581045149061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6577717916863441393532081 4933288437647581045149061)
                  ·
                    refine ⟨924991582058921445965449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4933288437647581045149061 924991582058921445965449)
                    ·
                      rfl

theorem cell22_2702122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_2702122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702122 prefixEnd_2702122 := by exact prefixLift 2702122
  have htrace : WordTrace (prefixWord ++ tailWord_2702122) baseStart_2702122 baseEnd_2702122 := by
    simpa [prefixWord, tailWord_2702122, baseEnd_2702122] using wordTrace_append hprefix tailTrace_2702122
  have hstable : (prefixWord ++ tailWord_2702122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702122).length < 2 ^ (prefixWord ++ tailWord_2702122).sum := by decide
  have hdescent : baseEnd_2702122 < baseStart_2702122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702135 : List Nat := [1, 1, 3, 1, 2, 1, 6, 3, 1, 3]
def baseStart_2702135 : Nat := 118140960795 + 2702135 * 2 ^ 59
def prefixEnd_2702135 : Nat := 4983230072969 + 3 ^ 40 * 2702135 * 2
def baseEnd_2702135 : Nat := 924996032224593745390409

theorem tailTrace_2702135 : CollatzResearch.WordTrace tailWord_2702135 prefixEnd_2702135 924996032224593745390409 := by
  unfold tailWord_2702135
  simp only [CollatzResearch.WordTrace]
  refine ⟨98554960065633857762179859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65703306710422571841453239 98554960065633857762179859)
  ·
    refine ⟨147832440098450786643269789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98554960065633857762179859 147832440098450786643269789)
    ·
      refine ⟨55437165036919044991226171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147832440098450786643269789 55437165036919044991226171)
      ·
        refine ⟨83155747555378567486839257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55437165036919044991226171 83155747555378567486839257)
        ·
          refine ⟨62366810666533925615129443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83155747555378567486839257 62366810666533925615129443)
          ·
            refine ⟨93550215999800888422694165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62366810666533925615129443 93550215999800888422694165)
            ·
              refine ⟨4385166374990666644813789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93550215999800888422694165 4385166374990666644813789)
              ·
                refine ⟨1644437390621499991805171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4385166374990666644813789 1644437390621499991805171)
                ·
                  refine ⟨2466656085932249987707757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644437390621499991805171 2466656085932249987707757)
                  ·
                    refine ⟨924996032224593745390409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2466656085932249987707757 924996032224593745390409)
                    ·
                      rfl

theorem cell22_2702135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_2702135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702135 prefixEnd_2702135 := by exact prefixLift 2702135
  have htrace : WordTrace (prefixWord ++ tailWord_2702135) baseStart_2702135 baseEnd_2702135 := by
    simpa [prefixWord, tailWord_2702135, baseEnd_2702135] using wordTrace_append hprefix tailTrace_2702135
  have hstable : (prefixWord ++ tailWord_2702135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702135).length < 2 ^ (prefixWord ++ tailWord_2702135).sum := by decide
  have hdescent : baseEnd_2702135 < baseStart_2702135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702176 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 6]
def baseStart_2702176 : Nat := 118140960795 + 2702176 * 2 ^ 59
def prefixEnd_2702176 : Nat := 4983230072969 + 3 ^ 40 * 2702176 * 2
def baseEnd_2702176 : Nat := 308336689120827768371761

theorem tailTrace_2702176 : CollatzResearch.WordTrace tailWord_2702176 prefixEnd_2702176 308336689120827768371761 := by
  unfold tailWord_2702176
  simp only [CollatzResearch.WordTrace]
  refine ⟨49278227729242660882211191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65704303638990214509614921 49278227729242660882211191)
  ·
    refine ⟨73917341593863991323316787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49278227729242660882211191 73917341593863991323316787)
    ·
      refine ⟨110876012390795986984975181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73917341593863991323316787 110876012390795986984975181)
      ·
        refine ⟨41578504646548495119365693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110876012390795986984975181 41578504646548495119365693)
        ·
          refine ⟨15591939242455685669762135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41578504646548495119365693 15591939242455685669762135)
          ·
            refine ⟨23387908863683528504643203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15591939242455685669762135 23387908863683528504643203)
            ·
              refine ⟨35081863295525292756964805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23387908863683528504643203 35081863295525292756964805)
              ·
                refine ⟨6577849367910992391930901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35081863295525292756964805 6577849367910992391930901)
                ·
                  refine ⟨308336689120827768371761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6577849367910992391930901 308336689120827768371761)
                  ·
                    rfl

theorem cell22_2702176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_2702176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702176 prefixEnd_2702176 := by exact prefixLift 2702176
  have htrace : WordTrace (prefixWord ++ tailWord_2702176) baseStart_2702176 baseEnd_2702176 := by
    simpa [prefixWord, tailWord_2702176, baseEnd_2702176] using wordTrace_append hprefix tailTrace_2702176
  have hstable : (prefixWord ++ tailWord_2702176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702176).length < 2 ^ (prefixWord ++ tailWord_2702176).sum := by decide
  have hdescent : baseEnd_2702176 < baseStart_2702176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702191 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 1, 5]
def baseStart_2702191 : Nat := 118140960795 + 2702191 * 2 ^ 59
def prefixEnd_2702191 : Nat := 4983230072969 + 3 ^ 40 * 2702191 * 2
def baseEnd_2702191 : Nat := 925015202169028265990237

theorem tailTrace_2702191 : CollatzResearch.WordTrace tailWord_2702191 prefixEnd_2702191 925015202169028265990237 := by
  unfold tailWord_2702191
  simp only [CollatzResearch.WordTrace]
  refine ⟨98557002553430979326218427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65704668368953986217478951 98557002553430979326218427)
  ·
    refine ⟨147835503830146468989327641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98557002553430979326218427 147835503830146468989327641)
    ·
      refine ⟨110876627872609851741995731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147835503830146468989327641 110876627872609851741995731)
      ·
        refine ⟨166314941808914777612993597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110876627872609851741995731 166314941808914777612993597)
        ·
          refine ⟨62368103178343041604872599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166314941808914777612993597 62368103178343041604872599)
          ·
            refine ⟨93552154767514562407308899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62368103178343041604872599 93552154767514562407308899)
            ·
              refine ⟨140328232151271843610963349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93552154767514562407308899 140328232151271843610963349)
              ·
                refine ⟨6577885882090867669263907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140328232151271843610963349 6577885882090867669263907)
                ·
                  refine ⟨9866828823136301503895861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6577885882090867669263907 9866828823136301503895861)
                  ·
                    refine ⟨925015202169028265990237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9866828823136301503895861 925015202169028265990237)
                    ·
                      rfl

theorem cell22_2702191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_2702191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702191 prefixEnd_2702191 := by exact prefixLift 2702191
  have htrace : WordTrace (prefixWord ++ tailWord_2702191) baseStart_2702191 baseEnd_2702191 := by
    simpa [prefixWord, tailWord_2702191, baseEnd_2702191] using wordTrace_append hprefix tailTrace_2702191
  have hstable : (prefixWord ++ tailWord_2702191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702191).length < 2 ^ (prefixWord ++ tailWord_2702191).sum := by decide
  have hdescent : baseEnd_2702191 < baseStart_2702191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702270 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2702270 : Nat := 118140960795 + 2702270 * 2 ^ 59
def prefixEnd_2702270 : Nat := 4983230072969 + 3 ^ 40 * 2702270 * 2
def baseEnd_2702270 : Nat := 925042245483498393264995

theorem tailTrace_2702270 : CollatzResearch.WordTrace tailWord_2702270 prefixEnd_2702270 925042245483498393264995 := by
  unfold tailWord_2702270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12319985490018096977293033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65706589280096517212229509 12319985490018096977293033)
  ·
    refine ⟨9239989117513572732969775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12319985490018096977293033 9239989117513572732969775)
    ·
      refine ⟨13859983676270359099454663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9239989117513572732969775 13859983676270359099454663)
      ·
        refine ⟨20789975514405538649181995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13859983676270359099454663 20789975514405538649181995)
        ·
          refine ⟨31184963271608307973772993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20789975514405538649181995 31184963271608307973772993)
          ·
            refine ⟨23388722453706230980329745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31184963271608307973772993 23388722453706230980329745)
            ·
              refine ⟨17541541840279673235247309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23388722453706230980329745 17541541840279673235247309)
              ·
                refine ⟨6578078190104877463217741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17541541840279673235247309 6578078190104877463217741)
                ·
                  refine ⟨2466779321289329048706653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6578078190104877463217741 2466779321289329048706653)
                  ·
                    refine ⟨925042245483498393264995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2466779321289329048706653 925042245483498393264995)
                    ·
                      rfl

theorem cell22_2702270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2702270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702270 prefixEnd_2702270 := by exact prefixLift 2702270
  have htrace : WordTrace (prefixWord ++ tailWord_2702270) baseStart_2702270 baseEnd_2702270 := by
    simpa [prefixWord, tailWord_2702270, baseEnd_2702270] using wordTrace_append hprefix tailTrace_2702270
  have hstable : (prefixWord ++ tailWord_2702270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702270).length < 2 ^ (prefixWord ++ tailWord_2702270).sum := by decide
  have hdescent : baseEnd_2702270 < baseStart_2702270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702283 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 5]
def baseStart_2702283 : Nat := 118140960795 + 2702283 * 2 ^ 59
def prefixEnd_2702283 : Nat := 4983230072969 + 3 ^ 40 * 2702283 * 2
def baseEnd_2702283 : Nat := 308348898549723564229985

theorem tailTrace_2702283 : CollatzResearch.WordTrace tailWord_2702283 prefixEnd_2702283 308348898549723564229985 := by
  unfold tailWord_2702283
  simp only [CollatzResearch.WordTrace]
  refine ⟨98560358069097679038567503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65706905379398452692378335 98560358069097679038567503)
  ·
    refine ⟨147840537103646518557851255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98560358069097679038567503 147840537103646518557851255)
    ·
      refine ⟨221760805655469777836776883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147840537103646518557851255 221760805655469777836776883)
      ·
        refine ⟨332641208483204666755165325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221760805655469777836776883 332641208483204666755165325)
        ·
          refine ⟨124740453181201750033186997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332641208483204666755165325 124740453181201750033186997)
          ·
            refine ⟨11694417485737664065611281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124740453181201750033186997 11694417485737664065611281)
            ·
              refine ⟨8770813114303248049208461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11694417485737664065611281 8770813114303248049208461)
              ·
                refine ⟨3289054917863718018453173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8770813114303248049208461 3289054917863718018453173)
                ·
                  refine ⟨308348898549723564229985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3289054917863718018453173 308348898549723564229985)
                  ·
                    rfl

theorem cell22_2702283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 5].length) (baseStart_2702283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702283 prefixEnd_2702283 := by exact prefixLift 2702283
  have htrace : WordTrace (prefixWord ++ tailWord_2702283) baseStart_2702283 baseEnd_2702283 := by
    simpa [prefixWord, tailWord_2702283, baseEnd_2702283] using wordTrace_append hprefix tailTrace_2702283
  have hstable : (prefixWord ++ tailWord_2702283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702283).length < 2 ^ (prefixWord ++ tailWord_2702283).sum := by decide
  have hdescent : baseEnd_2702283 < baseStart_2702283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702334 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_2702334 : Nat := 118140960795 + 2702334 * 2 ^ 59
def prefixEnd_2702334 : Nat := 4983230072969 + 3 ^ 40 * 2702334 * 2
def baseEnd_2702334 : Nat := 308354717997141186554933

theorem tailTrace_2702334 : CollatzResearch.WordTrace tailWord_2702334 prefixEnd_2702334 308354717997141186554933 := by
  unfold tailWord_2702334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12320277273989114343584257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65708145461275276499116037 12320277273989114343584257)
  ·
    refine ⟨9240207955491835757688193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12320277273989114343584257 9240207955491835757688193)
    ·
      refine ⟨6930155966618876818266145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9240207955491835757688193 6930155966618876818266145)
      ·
        refine ⟨5197616974964157613699609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6930155966618876818266145 5197616974964157613699609)
        ·
          refine ⟨3898212731223118210274707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5197616974964157613699609 3898212731223118210274707)
          ·
            refine ⟨5847319096834677315412061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898212731223118210274707 5847319096834677315412061)
            ·
              refine ⟨2192744661313003993279523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5847319096834677315412061 2192744661313003993279523)
              ·
                refine ⟨3289116991969505989919285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192744661313003993279523 3289116991969505989919285)
                ·
                  refine ⟨308354717997141186554933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3289116991969505989919285 308354717997141186554933)
                  ·
                    rfl

theorem cell22_2702334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_2702334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702334 prefixEnd_2702334 := by exact prefixLift 2702334
  have htrace : WordTrace (prefixWord ++ tailWord_2702334) baseStart_2702334 baseEnd_2702334 := by
    simpa [prefixWord, tailWord_2702334, baseEnd_2702334] using wordTrace_append hprefix tailTrace_2702334
  have hstable : (prefixWord ++ tailWord_2702334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702334).length < 2 ^ (prefixWord ++ tailWord_2702334).sum := by decide
  have hdescent : baseEnd_2702334 < baseStart_2702334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702360 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 4, 3]
def baseStart_2702360 : Nat := 118140960795 + 2702360 * 2 ^ 59
def prefixEnd_2702360 : Nat := 4983230072969 + 3 ^ 40 * 2702360 * 2
def baseEnd_2702360 : Nat := 925073054322768158514719

theorem tailTrace_2702360 : CollatzResearch.WordTrace tailWord_2702360 prefixEnd_2702360 925073054322768158514719 := by
  unfold tailWord_2702360
  simp only [CollatzResearch.WordTrace]
  refine ⟨49281583244909360594560267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65708777659879147459413689 49281583244909360594560267)
  ·
    refine ⟨73922374867364040891840401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49281583244909360594560267 73922374867364040891840401)
    ·
      refine ⟨55441781150523030668880301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73922374867364040891840401 55441781150523030668880301)
      ·
        refine ⟨20790667931446136500830113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55441781150523030668880301 20790667931446136500830113)
        ·
          refine ⟨15593000948584602375622585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20790667931446136500830113 15593000948584602375622585)
          ·
            refine ⟨11694750711438451781716939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15593000948584602375622585 11694750711438451781716939)
            ·
              refine ⟨17542126067157677672575409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11694750711438451781716939 17542126067157677672575409)
              ·
                refine ⟨13156594550368258254431557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17542126067157677672575409 13156594550368258254431557)
                ·
                  refine ⟨2466861478194048422705917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13156594550368258254431557 2466861478194048422705917)
                  ·
                    refine ⟨925073054322768158514719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2466861478194048422705917 925073054322768158514719)
                    ·
                      rfl

theorem cell22_2702360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_2702360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702360 prefixEnd_2702360 := by exact prefixLift 2702360
  have htrace : WordTrace (prefixWord ++ tailWord_2702360) baseStart_2702360 baseEnd_2702360 := by
    simpa [prefixWord, tailWord_2702360, baseEnd_2702360] using wordTrace_append hprefix tailTrace_2702360
  have hstable : (prefixWord ++ tailWord_2702360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702360).length < 2 ^ (prefixWord ++ tailWord_2702360).sum := by decide
  have hdescent : baseEnd_2702360 < baseStart_2702360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702390 : List Nat := [5, 1, 2, 1, 1, 2, 1, 9]
def baseStart_2702390 : Nat := 118140960795 + 2702390 * 2 ^ 59
def prefixEnd_2702390 : Nat := 4983230072969 + 3 ^ 40 * 2702390 * 2
def baseEnd_2702390 : Nat := 102787035992873120029403

theorem tailTrace_2702390 : CollatzResearch.WordTrace tailWord_2702390 prefixEnd_2702390 102787035992873120029403 := by
  unfold tailWord_2702390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6160266292481877269544539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65709507119806690875141749 6160266292481877269544539)
  ·
    refine ⟨9240399438722815904316809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6160266292481877269544539 9240399438722815904316809)
    ·
      refine ⟨6930299579042111928237607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9240399438722815904316809 6930299579042111928237607)
      ·
        refine ⟨10395449368563167892356411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6930299579042111928237607 10395449368563167892356411)
        ·
          refine ⟨15593174052844751838534617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10395449368563167892356411 15593174052844751838534617)
          ·
            refine ⟨11694880539633563878900963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15593174052844751838534617 11694880539633563878900963)
            ·
              refine ⟨17542320809450345818351445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11694880539633563878900963 17542320809450345818351445)
              ·
                refine ⟨102787035992873120029403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17542320809450345818351445 102787035992873120029403)
                ·
                  rfl

theorem cell22_2702390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_2702390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702390 prefixEnd_2702390 := by exact prefixLift 2702390
  have htrace : WordTrace (prefixWord ++ tailWord_2702390) baseStart_2702390 baseEnd_2702390 := by
    simpa [prefixWord, tailWord_2702390, baseEnd_2702390] using wordTrace_append hprefix tailTrace_2702390
  have hstable : (prefixWord ++ tailWord_2702390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702390).length < 2 ^ (prefixWord ++ tailWord_2702390).sum := by decide
  have hdescent : baseEnd_2702390 < baseStart_2702390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702405 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 3, 3]
def baseStart_2702405 : Nat := 118140960795 + 2702405 * 2 ^ 59
def prefixEnd_2702405 : Nat := 4983230072969 + 3 ^ 40 * 2702405 * 2
def baseEnd_2702405 : Nat := 925088458742403041139581

theorem tailTrace_2702405 : CollatzResearch.WordTrace tailWord_2702405 prefixEnd_2702405 925088458742403041139581 := by
  unfold tailWord_2702405
  simp only [CollatzResearch.WordTrace]
  refine ⟨98564807774655693874508669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65709871849770462583005779 98564807774655693874508669)
  ·
    refine ⟨36961802915495885202940751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98564807774655693874508669 36961802915495885202940751)
    ·
      refine ⟨55442704373243827804411127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36961802915495885202940751 55442704373243827804411127)
      ·
        refine ⟨83164056559865741706616691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55442704373243827804411127 83164056559865741706616691)
        ·
          refine ⟨124746084839798612559925037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83164056559865741706616691 124746084839798612559925037)
          ·
            refine ⟨46779781814924479709971889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124746084839798612559925037 46779781814924479709971889)
            ·
              refine ⟨35084836361193359782478917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46779781814924479709971889 35084836361193359782478917)
              ·
                refine ⟨6578406817723754959214797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35084836361193359782478917 6578406817723754959214797)
                ·
                  refine ⟨2466902556646408109705549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6578406817723754959214797 2466902556646408109705549)
                  ·
                    refine ⟨925088458742403041139581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2466902556646408109705549 925088458742403041139581)
                    ·
                      rfl

theorem cell22_2702405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_2702405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702405 prefixEnd_2702405 := by exact prefixLift 2702405
  have htrace : WordTrace (prefixWord ++ tailWord_2702405) baseStart_2702405 baseEnd_2702405 := by
    simpa [prefixWord, tailWord_2702405, baseEnd_2702405] using wordTrace_append hprefix tailTrace_2702405
  have hstable : (prefixWord ++ tailWord_2702405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702405).length < 2 ^ (prefixWord ++ tailWord_2702405).sum := by decide
  have hdescent : baseEnd_2702405 < baseStart_2702405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702439 : List Nat := [1, 1, 5, 1, 1, 4, 1, 4, 1, 3]
def baseStart_2702439 : Nat := 118140960795 + 2702439 * 2 ^ 59
def prefixEnd_2702439 : Nat := 4983230072969 + 3 ^ 40 * 2702439 * 2
def baseEnd_2702439 : Nat := 925100097637238285789477

theorem tailTrace_2702439 : CollatzResearch.WordTrace tailWord_2702439 prefixEnd_2702439 925100097637238285789477 := by
  unfold tailWord_2702439
  simp only [CollatzResearch.WordTrace]
  refine ⟨98566047856532517681246371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65710698571021678454164247 98566047856532517681246371)
  ·
    refine ⟨147849071784798776521869557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98566047856532517681246371 147849071784798776521869557)
    ·
      refine ⟨13860850479824885298925271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147849071784798776521869557 13860850479824885298925271)
      ·
        refine ⟨20791275719737327948387907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13860850479824885298925271 20791275719737327948387907)
        ·
          refine ⟨31186913579605991922581861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20791275719737327948387907 31186913579605991922581861)
          ·
            refine ⟨5847546296176123485484099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31186913579605991922581861 5847546296176123485484099)
            ·
              refine ⟨8771319444264185228226149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5847546296176123485484099 8771319444264185228226149)
              ·
                refine ⟨1644622395799534730292403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8771319444264185228226149 1644622395799534730292403)
                ·
                  refine ⟨2466933593699302095438605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644622395799534730292403 2466933593699302095438605)
                  ·
                    refine ⟨925100097637238285789477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2466933593699302095438605 925100097637238285789477)
                    ·
                      rfl

theorem cell22_2702439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_2702439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702439 prefixEnd_2702439 := by exact prefixLift 2702439
  have htrace : WordTrace (prefixWord ++ tailWord_2702439) baseStart_2702439 baseEnd_2702439 := by
    simpa [prefixWord, tailWord_2702439, baseEnd_2702439] using wordTrace_append hprefix tailTrace_2702439
  have hstable : (prefixWord ++ tailWord_2702439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702439).length < 2 ^ (prefixWord ++ tailWord_2702439).sum := by decide
  have hdescent : baseEnd_2702439 < baseStart_2702439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702450 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_2702450 : Nat := 118140960795 + 2702450 * 2 ^ 59
def prefixEnd_2702450 : Nat := 4983230072969 + 3 ^ 40 * 2702450 * 2
def baseEnd_2702450 : Nat := 925103863162037923764443

theorem tailTrace_2702450 : CollatzResearch.WordTrace tailWord_2702450 prefixEnd_2702450 925103863162037923764443 := by
  unfold tailWord_2702450
  simp only [CollatzResearch.WordTrace]
  refine ⟨24641612264873166639974201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65710966039661777706597869 24641612264873166639974201)
  ·
    refine ⟨18481209198654874979980651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24641612264873166639974201 18481209198654874979980651)
    ·
      refine ⟨27721813797982312469970977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18481209198654874979980651 27721813797982312469970977)
      ·
        refine ⟨20791360348486734352478233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27721813797982312469970977 20791360348486734352478233)
        ·
          refine ⟨15593520261365050764358675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20791360348486734352478233 15593520261365050764358675)
          ·
            refine ⟨23390280392047576146538013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15593520261365050764358675 23390280392047576146538013)
            ·
              refine ⟨8771355147017841054951755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23390280392047576146538013 8771355147017841054951755)
              ·
                refine ⟨13157032720526761582427633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8771355147017841054951755 13157032720526761582427633)
                ·
                  refine ⟨9867774540395071186820725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13157032720526761582427633 9867774540395071186820725)
                  ·
                    refine ⟨925103863162037923764443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9867774540395071186820725 925103863162037923764443)
                    ·
                      rfl

theorem cell22_2702450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_2702450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702450 prefixEnd_2702450 := by exact prefixLift 2702450
  have htrace : WordTrace (prefixWord ++ tailWord_2702450) baseStart_2702450 baseEnd_2702450 := by
    simpa [prefixWord, tailWord_2702450, baseEnd_2702450] using wordTrace_append hprefix tailTrace_2702450
  have hstable : (prefixWord ++ tailWord_2702450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702450).length < 2 ^ (prefixWord ++ tailWord_2702450).sum := by decide
  have hdescent : baseEnd_2702450 < baseStart_2702450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702497 : List Nat := [1, 2, 3, 3, 1, 1, 1, 6, 4]
def baseStart_2702497 : Nat := 118140960795 + 2702497 * 2 ^ 59
def prefixEnd_2702497 : Nat := 4983230072969 + 3 ^ 40 * 2702497 * 2
def baseEnd_2702497 : Nat := 308373317407515155946433

theorem tailTrace_2702497 : CollatzResearch.WordTrace tailWord_2702497 prefixEnd_2702497 308373317407515155946433 := by
  unfold tailWord_2702497
  simp only [CollatzResearch.WordTrace]
  refine ⟨98568163290322393586857745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65712108860214929057905163 98568163290322393586857745)
  ·
    refine ⟨73926122467741795190143309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98568163290322393586857745 73926122467741795190143309)
    ·
      refine ⟨27722295925403173196303741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73926122467741795190143309 27722295925403173196303741)
      ·
        refine ⟨10395860972026189948613903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27722295925403173196303741 10395860972026189948613903)
        ·
          refine ⟨15593791458039284922920855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10395860972026189948613903 15593791458039284922920855)
          ·
            refine ⟨23390687187058927384381283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15593791458039284922920855 23390687187058927384381283)
            ·
              refine ⟨35086030780588391076571925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23390687187058927384381283 35086030780588391076571925)
              ·
                refine ⟨1644657692840080831714309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35086030780588391076571925 1644657692840080831714309)
                ·
                  refine ⟨308373317407515155946433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1644657692840080831714309 308373317407515155946433)
                  ·
                    rfl

theorem cell22_2702497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 4].length) (baseStart_2702497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702497 prefixEnd_2702497 := by exact prefixLift 2702497
  have htrace : WordTrace (prefixWord ++ tailWord_2702497) baseStart_2702497 baseEnd_2702497 := by
    simpa [prefixWord, tailWord_2702497, baseEnd_2702497] using wordTrace_append hprefix tailTrace_2702497
  have hstable : (prefixWord ++ tailWord_2702497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702497).length < 2 ^ (prefixWord ++ tailWord_2702497).sum := by decide
  have hdescent : baseEnd_2702497 < baseStart_2702497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702529 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2702529 : Nat := 118140960795 + 2702529 * 2 ^ 59
def prefixEnd_2702529 : Nat := 4983230072969 + 3 ^ 40 * 2702529 * 2
def baseEnd_2702529 : Nat := 925130906476508051039201

theorem tailTrace_2702529 : CollatzResearch.WordTrace tailWord_2702529 prefixEnd_2702529 925130906476508051039201 := by
  unfold tailWord_2702529
  simp only [CollatzResearch.WordTrace]
  refine ⟨98569330426206463052022641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65712886950804308701348427 98569330426206463052022641)
  ·
    refine ⟨73926997819654847289016981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98569330426206463052022641 73926997819654847289016981)
    ·
      refine ⟨3465328022796320966672671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73926997819654847289016981 3465328022796320966672671)
      ·
        refine ⟨5197992034194481450009007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3465328022796320966672671 5197992034194481450009007)
        ·
          refine ⟨7796988051291722175013511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5197992034194481450009007 7796988051291722175013511)
          ·
            refine ⟨11695482076937583262520267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7796988051291722175013511 11695482076937583262520267)
            ·
              refine ⟨17543223115406374893780401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11695482076937583262520267 17543223115406374893780401)
              ·
                refine ⟨13157417336554781170335301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17543223115406374893780401 13157417336554781170335301)
                ·
                  refine ⟨2467015750604021469437869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13157417336554781170335301 2467015750604021469437869)
                  ·
                    refine ⟨925130906476508051039201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2467015750604021469437869 925130906476508051039201)
                    ·
                      rfl

theorem cell22_2702529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2702529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702529 prefixEnd_2702529 := by exact prefixLift 2702529
  have htrace : WordTrace (prefixWord ++ tailWord_2702529) baseStart_2702529 baseEnd_2702529 := by
    simpa [prefixWord, tailWord_2702529, baseEnd_2702529] using wordTrace_append hprefix tailTrace_2702529
  have hstable : (prefixWord ++ tailWord_2702529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702529).length < 2 ^ (prefixWord ++ tailWord_2702529).sum := by decide
  have hdescent : baseEnd_2702529 < baseStart_2702529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702542 : List Nat := [4, 1, 1, 1, 5, 2, 8]
def baseStart_2702542 : Nat := 118140960795 + 2702542 * 2 ^ 59
def prefixEnd_2702542 : Nat := 4983230072969 + 3 ^ 40 * 2702542 * 2
def baseEnd_2702542 : Nat := 34264272468228901869043

theorem tailTrace_2702542 : CollatzResearch.WordTrace tailWord_2702542 prefixEnd_2702542 34264272468228901869043 := by
  unfold tailWord_2702542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12321225571894920784030735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65713203050106244181497253 12321225571894920784030735)
  ·
    refine ⟨18481838357842381176046103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12321225571894920784030735 18481838357842381176046103)
    ·
      refine ⟨27722757536763571764069155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18481838357842381176046103 27722757536763571764069155)
      ·
        refine ⟨41584136305145357646103733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27722757536763571764069155 41584136305145357646103733)
        ·
          refine ⟨3898512778607377279322225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41584136305145357646103733 3898512778607377279322225)
          ·
            refine ⟨2923884583955532959491669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3898512778607377279322225 2923884583955532959491669)
            ·
              refine ⟨34264272468228901869043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2923884583955532959491669 34264272468228901869043)
              ·
                rfl

theorem cell22_2702542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 8].length) (baseStart_2702542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702542 prefixEnd_2702542 := by exact prefixLift 2702542
  have htrace : WordTrace (prefixWord ++ tailWord_2702542) baseStart_2702542 baseEnd_2702542 := by
    simpa [prefixWord, tailWord_2702542, baseEnd_2702542] using wordTrace_append hprefix tailTrace_2702542
  have hstable : (prefixWord ++ tailWord_2702542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702542).length < 2 ^ (prefixWord ++ tailWord_2702542).sum := by decide
  have hdescent : baseEnd_2702542 < baseStart_2702542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702548 : List Nat := [2, 4, 1, 4, 1, 1, 3, 2, 4]
def baseStart_2702548 : Nat := 118140960795 + 2702548 * 2 ^ 59
def prefixEnd_2702548 : Nat := 4983230072969 + 3 ^ 40 * 2702548 * 2
def baseEnd_2702548 : Nat := 308379136854932778271381

theorem tailTrace_2702548 : CollatzResearch.WordTrace tailWord_2702548 prefixEnd_2702548 308379136854932778271381 := by
  unfold tailWord_2702548
  simp only [CollatzResearch.WordTrace]
  refine ⟨49285011706568814648482149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65713348942091752864642865 49285011706568814648482149)
  ·
    refine ⟨9240939694981652746590403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49285011706568814648482149 9240939694981652746590403)
    ·
      refine ⟨13861409542472479119885605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9240939694981652746590403 13861409542472479119885605)
      ·
        refine ⟨2599014289213589834978551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13861409542472479119885605 2599014289213589834978551)
        ·
          refine ⟨3898521433820384752467827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2599014289213589834978551 3898521433820384752467827)
          ·
            refine ⟨5847782150730577128701741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898521433820384752467827 5847782150730577128701741)
            ·
              refine ⟨2192918306523966423263153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5847782150730577128701741 2192918306523966423263153)
              ·
                refine ⟨1644688729892974817447365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2192918306523966423263153 1644688729892974817447365)
                ·
                  refine ⟨308379136854932778271381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1644688729892974817447365 308379136854932778271381)
                  ·
                    rfl

theorem cell22_2702548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_2702548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702548 prefixEnd_2702548 := by exact prefixLift 2702548
  have htrace : WordTrace (prefixWord ++ tailWord_2702548) baseStart_2702548 baseEnd_2702548 := by
    simpa [prefixWord, tailWord_2702548, baseEnd_2702548] using wordTrace_append hprefix tailTrace_2702548
  have hstable : (prefixWord ++ tailWord_2702548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702548).length < 2 ^ (prefixWord ++ tailWord_2702548).sum := by decide
  have hdescent : baseEnd_2702548 < baseStart_2702548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702632 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 8]
def baseStart_2702632 : Nat := 118140960795 + 2702632 * 2 ^ 59
def prefixEnd_2702632 : Nat := 4983230072969 + 3 ^ 40 * 2702632 * 2
def baseEnd_2702632 : Nat := 308388721827150038571295

theorem tailTrace_2702632 : CollatzResearch.WordTrace tailWord_2702632 prefixEnd_2702632 308388721827150038571295 := by
  unfold tailWord_2702632
  simp only [CollatzResearch.WordTrace]
  refine ⟨49286543572416655821511075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65715391429888874428681433 49286543572416655821511075)
  ·
    refine ⟨73929815358624983732266613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49286543572416655821511075 73929815358624983732266613)
    ·
      refine ⟨6930920189871092224899995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73929815358624983732266613 6930920189871092224899995)
      ·
        refine ⟨10396380284806638337349993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6930920189871092224899995 10396380284806638337349993)
        ·
          refine ⟨7797285213604978753012495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10396380284806638337349993 7797285213604978753012495)
          ·
            refine ⟨11695927820407468129518743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7797285213604978753012495 11695927820407468129518743)
            ·
              refine ⟨17543891730611202194278115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11695927820407468129518743 17543891730611202194278115)
              ·
                refine ⟨26315837595916803291417173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17543891730611202194278115 26315837595916803291417173)
                ·
                  refine ⟨308388721827150038571295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26315837595916803291417173 308388721827150038571295)
                  ·
                    rfl

theorem cell22_2702632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_2702632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702632 prefixEnd_2702632 := by exact prefixLift 2702632
  have htrace : WordTrace (prefixWord ++ tailWord_2702632) baseStart_2702632 baseEnd_2702632 := by
    simpa [prefixWord, tailWord_2702632, baseEnd_2702632] using wordTrace_append hprefix tailTrace_2702632
  have hstable : (prefixWord ++ tailWord_2702632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702632).length < 2 ^ (prefixWord ++ tailWord_2702632).sum := by decide
  have hdescent : baseEnd_2702632 < baseStart_2702632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702634 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_2702634 : Nat := 118140960795 + 2702634 * 2 ^ 59
def prefixEnd_2702634 : Nat := 4983230072969 + 3 ^ 40 * 2702634 * 2
def baseEnd_2702634 : Nat := 925166850122322777163879

theorem tailTrace_2702634 : CollatzResearch.WordTrace tailWord_2702634 prefixEnd_2702634 925166850122322777163879 := by
  unfold tailWord_2702634
  simp only [CollatzResearch.WordTrace]
  refine ⟨24643290022706516496148739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65715440060550710656396637 24643290022706516496148739)
  ·
    refine ⟨36964935034059774744223109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24643290022706516496148739 36964935034059774744223109)
    ·
      refine ⟨6930925318886207764541833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36964935034059774744223109 6930925318886207764541833)
      ·
        refine ⟨5198193989164655823406375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6930925318886207764541833 5198193989164655823406375)
        ·
          refine ⟨7797290983746983735109563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5198193989164655823406375 7797290983746983735109563)
          ·
            refine ⟨11695936475620475602664345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7797290983746983735109563 11695936475620475602664345)
            ·
              refine ⟨8771952356715356701998259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11695936475620475602664345 8771952356715356701998259)
              ·
                refine ⟨13157928535073035052997389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8771952356715356701998259 13157928535073035052997389)
                ·
                  refine ⟨4934223200652388144874021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13157928535073035052997389 4934223200652388144874021)
                  ·
                    refine ⟨925166850122322777163879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4934223200652388144874021 925166850122322777163879)
                    ·
                      rfl

theorem cell22_2702634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_2702634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702634 prefixEnd_2702634 := by exact prefixLift 2702634
  have htrace : WordTrace (prefixWord ++ tailWord_2702634) baseStart_2702634 baseEnd_2702634 := by
    simpa [prefixWord, tailWord_2702634, baseEnd_2702634] using wordTrace_append hprefix tailTrace_2702634
  have hstable : (prefixWord ++ tailWord_2702634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702634).length < 2 ^ (prefixWord ++ tailWord_2702634).sum := by decide
  have hdescent : baseEnd_2702634 < baseStart_2702634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702685 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2702685 : Nat := 118140960795 + 2702685 * 2 ^ 59
def prefixEnd_2702685 : Nat := 4983230072969 + 3 ^ 40 * 2702685 * 2
def baseEnd_2702685 : Nat := 925184308464575644138723

theorem tailTrace_2702685 : CollatzResearch.WordTrace tailWord_2702685 prefixEnd_2702685 925184308464575644138723 := by
  unfold tailWord_2702685
  simp only [CollatzResearch.WordTrace]
  refine ⟨98575020213641301694701509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65716680142427534463134339 98575020213641301694701509)
  ·
    refine ⟨18482816290057744067756533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98575020213641301694701509 18482816290057744067756533)
    ·
      refine ⟨1732764027192913506352175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18482816290057744067756533 1732764027192913506352175)
      ·
        refine ⟨2599146040789370259528263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732764027192913506352175 2599146040789370259528263)
        ·
          refine ⟨3898719061184055389292395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2599146040789370259528263 3898719061184055389292395)
          ·
            refine ⟨5848078591776083083938593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898719061184055389292395 5848078591776083083938593)
            ·
              refine ⟨4386058943832062312953945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5848078591776083083938593 4386058943832062312953945)
              ·
                refine ⟨3289544207874046734715459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4386058943832062312953945 3289544207874046734715459)
                ·
                  refine ⟨4934316311811070102073189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289544207874046734715459 4934316311811070102073189)
                  ·
                    refine ⟨925184308464575644138723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4934316311811070102073189 925184308464575644138723)
                    ·
                      rfl

theorem cell22_2702685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2702685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702685 prefixEnd_2702685 := by exact prefixLift 2702685
  have htrace : WordTrace (prefixWord ++ tailWord_2702685) baseStart_2702685 baseEnd_2702685 := by
    simpa [prefixWord, tailWord_2702685, baseEnd_2702685] using wordTrace_append hprefix tailTrace_2702685
  have hstable : (prefixWord ++ tailWord_2702685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702685).length < 2 ^ (prefixWord ++ tailWord_2702685).sum := by decide
  have hdescent : baseEnd_2702685 < baseStart_2702685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702777 : List Nat := [1, 2, 1, 4, 5, 1, 2, 2, 1, 3]
def baseStart_2702777 : Nat := 118140960795 + 2702777 * 2 ^ 59
def prefixEnd_2702777 : Nat := 4983230072969 + 3 ^ 40 * 2702777 * 2
def baseEnd_2702777 : Nat := 925215801944718070838441

theorem tailTrace_2702777 : CollatzResearch.WordTrace tailWord_2702777 prefixEnd_2702777 925215801944718070838441 := by
  unfold tailWord_2702777
  simp only [CollatzResearch.WordTrace]
  refine ⟨98578375729308001407050585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65718917152872000938033723 98578375729308001407050585)
  ·
    refine ⟨73933781796981001055287939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98578375729308001407050585 73933781796981001055287939)
    ·
      refine ⟨110900672695471501582931909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73933781796981001055287939 110900672695471501582931909)
      ·
        refine ⟨20793876130400906546799733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110900672695471501582931909 20793876130400906546799733)
        ·
          refine ⟨1949425887225084988762475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20793876130400906546799733 1949425887225084988762475)
          ·
            refine ⟨2924138830837627483143713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949425887225084988762475 2924138830837627483143713)
            ·
              refine ⟨2193104123128220612357785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2924138830837627483143713 2193104123128220612357785)
              ·
                refine ⟨1644828092346165459268339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2193104123128220612357785 1644828092346165459268339)
                ·
                  refine ⟨2467242138519248188902509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644828092346165459268339 2467242138519248188902509)
                  ·
                    refine ⟨925215801944718070838441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2467242138519248188902509 925215801944718070838441)
                    ·
                      rfl

theorem cell22_2702777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 1, 3].length) (baseStart_2702777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702777 prefixEnd_2702777 := by exact prefixLift 2702777
  have htrace : WordTrace (prefixWord ++ tailWord_2702777) baseStart_2702777 baseEnd_2702777 := by
    simpa [prefixWord, tailWord_2702777, baseEnd_2702777] using wordTrace_append hprefix tailTrace_2702777
  have hstable : (prefixWord ++ tailWord_2702777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702777).length < 2 ^ (prefixWord ++ tailWord_2702777).sum := by decide
  have hdescent : baseEnd_2702777 < baseStart_2702777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702833 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 2, 3]
def baseStart_2702833 : Nat := 118140960795 + 2702833 * 2 ^ 59
def prefixEnd_2702833 : Nat := 4983230072969 + 3 ^ 40 * 2702833 * 2
def baseEnd_2702833 : Nat := 925234971889152591438269

theorem tailTrace_2702833 : CollatzResearch.WordTrace tailWord_2702833 prefixEnd_2702833 925234971889152591438269 := by
  unfold tailWord_2702833
  simp only [CollatzResearch.WordTrace]
  refine ⟨98580418217105122971089153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65720278811403415314059435 98580418217105122971089153)
  ·
    refine ⟨73935313662828842228316865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98580418217105122971089153 73935313662828842228316865)
    ·
      refine ⟨55451485247121631671237649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73935313662828842228316865 55451485247121631671237649)
      ·
        refine ⟨41588613935341223753428237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55451485247121631671237649 41588613935341223753428237)
        ·
          refine ⟨15595730225752958907535589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41588613935341223753428237 15595730225752958907535589)
          ·
            refine ⟨2924199417328679795162923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15595730225752958907535589 2924199417328679795162923)
            ·
              refine ⟨4386299125993019692744385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924199417328679795162923 4386299125993019692744385)
              ·
                refine ⟨3289724344494764769558289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4386299125993019692744385 3289724344494764769558289)
                ·
                  refine ⟨2467293258371073577168717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3289724344494764769558289 2467293258371073577168717)
                  ·
                    refine ⟨925234971889152591438269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2467293258371073577168717 925234971889152591438269)
                    ·
                      rfl

theorem cell22_2702833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_2702833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702833 prefixEnd_2702833 := by exact prefixLift 2702833
  have htrace : WordTrace (prefixWord ++ tailWord_2702833) baseStart_2702833 baseEnd_2702833 := by
    simpa [prefixWord, tailWord_2702833, baseEnd_2702833] using wordTrace_append hprefix tailTrace_2702833
  have hstable : (prefixWord ++ tailWord_2702833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702833).length < 2 ^ (prefixWord ++ tailWord_2702833).sum := by decide
  have hdescent : baseEnd_2702833 < baseStart_2702833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702936 : List Nat := [2, 1, 2, 2, 1, 2, 1, 7, 4]
def baseStart_2702936 : Nat := 118140960795 + 2702936 * 2 ^ 59
def prefixEnd_2702936 : Nat := 4983230072969 + 3 ^ 40 * 2702936 * 2
def baseEnd_2702936 : Nat := 308423410298031552037651

theorem tailTrace_2702936 : CollatzResearch.WordTrace tailWord_2702936 prefixEnd_2702936 308423410298031552037651 := by
  unfold tailWord_2702936
  simp only [CollatzResearch.WordTrace]
  refine ⟨49292087467865985781044331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65722783290487981041392441 49292087467865985781044331)
  ·
    refine ⟨73938131201798978671566497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49292087467865985781044331 73938131201798978671566497)
    ·
      refine ⟨55453598401349234003674873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73938131201798978671566497 55453598401349234003674873)
      ·
        refine ⟨41590198801011925502756155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55453598401349234003674873 41590198801011925502756155)
        ·
          refine ⟨62385298201517888254134233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41590198801011925502756155 62385298201517888254134233)
          ·
            refine ⟨46788973651138416190600675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62385298201517888254134233 46788973651138416190600675)
            ·
              refine ⟨70183460476707624285901013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46788973651138416190600675 70183460476707624285901013)
              ·
                refine ⟨1644924854922834944200805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70183460476707624285901013 1644924854922834944200805)
                ·
                  refine ⟨308423410298031552037651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1644924854922834944200805 308423410298031552037651)
                  ·
                    rfl

theorem cell22_2702936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 4].length) (baseStart_2702936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702936 prefixEnd_2702936 := by exact prefixLift 2702936
  have htrace : WordTrace (prefixWord ++ tailWord_2702936) baseStart_2702936 baseEnd_2702936 := by
    simpa [prefixWord, tailWord_2702936, baseEnd_2702936] using wordTrace_append hprefix tailTrace_2702936
  have hstable : (prefixWord ++ tailWord_2702936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702936).length < 2 ^ (prefixWord ++ tailWord_2702936).sum := by decide
  have hdescent : baseEnd_2702936 < baseStart_2702936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702951 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 4, 3]
def baseStart_2702951 : Nat := 118140960795 + 2702951 * 2 ^ 59
def prefixEnd_2702951 : Nat := 4983230072969 + 3 ^ 40 * 2702951 * 2
def baseEnd_2702951 : Nat := 925275365700639616987907

theorem tailTrace_2702951 : CollatzResearch.WordTrace tailWord_2702951 prefixEnd_2702951 925275365700639616987907 := by
  unfold tailWord_2702951
  simp only [CollatzResearch.WordTrace]
  refine ⟨98584722030677629123884707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65723148020451752749256471 98584722030677629123884707)
  ·
    refine ⟨147877083046016443685827061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98584722030677629123884707 147877083046016443685827061)
    ·
      refine ⟨13863476535564041595546287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 147877083046016443685827061 13863476535564041595546287)
      ·
        refine ⟨20795214803346062393319431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13863476535564041595546287 20795214803346062393319431)
        ·
          refine ⟨31192822205019093589979147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20795214803346062393319431 31192822205019093589979147)
          ·
            refine ⟨46789233307528640384968721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31192822205019093589979147 46789233307528640384968721)
            ·
              refine ⟨35091924980646480288726541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46789233307528640384968721 35091924980646480288726541)
              ·
                refine ⟨13159471867742430108272453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35091924980646480288726541 13159471867742430108272453)
                ·
                  refine ⟨2467400975201705645301085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13159471867742430108272453 2467400975201705645301085)
                  ·
                    refine ⟨925275365700639616987907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2467400975201705645301085 925275365700639616987907)
                    ·
                      rfl

theorem cell22_2702951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_2702951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702951 prefixEnd_2702951 := by exact prefixLift 2702951
  have htrace : WordTrace (prefixWord ++ tailWord_2702951) baseStart_2702951 baseEnd_2702951 := by
    simpa [prefixWord, tailWord_2702951, baseEnd_2702951] using wordTrace_append hprefix tailTrace_2702951
  have hstable : (prefixWord ++ tailWord_2702951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702951).length < 2 ^ (prefixWord ++ tailWord_2702951).sum := by decide
  have hdescent : baseEnd_2702951 < baseStart_2702951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702953 : List Nat := [1, 2, 1, 1, 1, 4, 6, 2, 4]
def baseStart_2702953 : Nat := 118140960795 + 2702953 * 2 ^ 59
def prefixEnd_2702953 : Nat := 4983230072969 + 3 ^ 40 * 2702953 * 2
def baseEnd_2702953 : Nat := 308425350113837426145967

theorem tailTrace_2702953 : CollatzResearch.WordTrace tailWord_2702953 prefixEnd_2702953 308425350113837426145967 := by
  unfold tailWord_2702953
  simp only [CollatzResearch.WordTrace]
  refine ⟨98584794976670383465457513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65723196651113588976971675 98584794976670383465457513)
  ·
    refine ⟨73938596232502787599093135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98584794976670383465457513 73938596232502787599093135)
    ·
      refine ⟨110907894348754181398639703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73938596232502787599093135 110907894348754181398639703)
      ·
        refine ⟨166361841523131272097959555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110907894348754181398639703 166361841523131272097959555)
        ·
          refine ⟨249542762284696908146939333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166361841523131272097959555 249542762284696908146939333)
          ·
            refine ⟨46789267928380670277551125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 249542762284696908146939333 46789267928380670277551125)
            ·
              refine ⟨2193246934142843919260209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46789267928380670277551125 2193246934142843919260209)
              ·
                refine ⟨1644935200607132939445157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2193246934142843919260209 1644935200607132939445157)
                ·
                  refine ⟨308425350113837426145967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1644935200607132939445157 308425350113837426145967)
                  ·
                    rfl

theorem cell22_2702953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 4].length) (baseStart_2702953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702953 prefixEnd_2702953 := by exact prefixLift 2702953
  have htrace : WordTrace (prefixWord ++ tailWord_2702953) baseStart_2702953 baseEnd_2702953 := by
    simpa [prefixWord, tailWord_2702953, baseEnd_2702953] using wordTrace_append hprefix tailTrace_2702953
  have hstable : (prefixWord ++ tailWord_2702953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702953).length < 2 ^ (prefixWord ++ tailWord_2702953).sum := by decide
  have hdescent : baseEnd_2702953 < baseStart_2702953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702981 : List Nat := [1, 3, 1, 1, 4, 1, 5, 6]
def baseStart_2702981 : Nat := 118140960795 + 2702981 * 2 ^ 59
def prefixEnd_2702981 : Nat := 4983230072969 + 3 ^ 40 * 2702981 * 2
def baseEnd_2702981 : Nat := 102809515034858837637535

theorem tailTrace_2702981 : CollatzResearch.WordTrace tailWord_2702981 prefixEnd_2702981 102809515034858837637535 := by
  unfold tailWord_2702981
  simp only [CollatzResearch.WordTrace]
  refine ⟨98585816220568944247476797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65723877480379296164984531 98585816220568944247476797)
  ·
    refine ⟨36969681082713354092803799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98585816220568944247476797 36969681082713354092803799)
    ·
      refine ⟨55454521624070031139205699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36969681082713354092803799 55454521624070031139205699)
      ·
        refine ⟨83181782436105046708808549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55454521624070031139205699 83181782436105046708808549)
        ·
          refine ⟨15596584206769696257901603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83181782436105046708808549 15596584206769696257901603)
          ·
            refine ⟨23394876310154544386852405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15596584206769696257901603 23394876310154544386852405)
            ·
              refine ⟨2193269654076988536267413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23394876310154544386852405 2193269654076988536267413)
              ·
                refine ⟨102809515034858837637535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2193269654076988536267413 102809515034858837637535)
                ·
                  rfl

theorem cell22_2702981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 6].length) (baseStart_2702981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702981 prefixEnd_2702981 := by exact prefixLift 2702981
  have htrace : WordTrace (prefixWord ++ tailWord_2702981) baseStart_2702981 baseEnd_2702981 := by
    simpa [prefixWord, tailWord_2702981, baseEnd_2702981] using wordTrace_append hprefix tailTrace_2702981
  have hstable : (prefixWord ++ tailWord_2702981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702981).length < 2 ^ (prefixWord ++ tailWord_2702981).sum := by decide
  have hdescent : baseEnd_2702981 < baseStart_2702981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2702983 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 2, 4]
def baseStart_2702983 : Nat := 118140960795 + 2702983 * 2 ^ 59
def prefixEnd_2702983 : Nat := 4983230072969 + 3 ^ 40 * 2702983 * 2
def baseEnd_2702983 : Nat := 925286319954602200187809

theorem tailTrace_2702983 : CollatzResearch.WordTrace tailWord_2702983 prefixEnd_2702983 925286319954602200187809 := by
  unfold tailWord_2702983
  simp only [CollatzResearch.WordTrace]
  refine ⟨98585889166561698589049603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65723926111041132392699735 98585889166561698589049603)
  ·
    refine ⟨147878833749842547883574405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98585889166561698589049603 147878833749842547883574405)
    ·
      refine ⟨27727281328095477728170201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147878833749842547883574405 27727281328095477728170201)
      ·
        refine ⟨20795460996071608296127651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27727281328095477728170201 20795460996071608296127651)
        ·
          refine ⟨31193191494107412444191477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20795460996071608296127651 31193191494107412444191477)
          ·
            refine ⟨2924361702572569916642951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31193191494107412444191477 2924361702572569916642951)
            ·
              refine ⟨4386542553858854874964427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924361702572569916642951 4386542553858854874964427)
              ·
                refine ⟨6579813830788282312446641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386542553858854874964427 6579813830788282312446641)
                ·
                  refine ⟨4934860373091211734334981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6579813830788282312446641 4934860373091211734334981)
                  ·
                    refine ⟨925286319954602200187809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4934860373091211734334981 925286319954602200187809)
                    ·
                      rfl

theorem cell22_2702983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_2702983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2702983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2702983 prefixEnd_2702983 := by exact prefixLift 2702983
  have htrace : WordTrace (prefixWord ++ tailWord_2702983) baseStart_2702983 baseEnd_2702983 := by
    simpa [prefixWord, tailWord_2702983, baseEnd_2702983] using wordTrace_append hprefix tailTrace_2702983
  have hstable : (prefixWord ++ tailWord_2702983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2702983).length < 2 ^ (prefixWord ++ tailWord_2702983).sum := by decide
  have hdescent : baseEnd_2702983 < baseStart_2702983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2702983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703026 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_2703026 : Nat := 118140960795 + 2703026 * 2 ^ 59
def prefixEnd_2703026 : Nat := 4983230072969 + 3 ^ 40 * 2703026 * 2
def baseEnd_2703026 : Nat := 308433679911121473787559

theorem tailTrace_2703026 : CollatzResearch.WordTrace tailWord_2703026 prefixEnd_2703026 308433679911121473787559 := by
  unfold tailWord_2703026
  simp only [CollatzResearch.WordTrace]
  refine ⟨24646864376351479233216233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65724971670270611288576621 24646864376351479233216233)
  ·
    refine ⟨18485148282263609424912175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24646864376351479233216233 18485148282263609424912175)
    ·
      refine ⟨27727722423395414137368263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18485148282263609424912175 27727722423395414137368263)
      ·
        refine ⟨41591583635093121206052395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27727722423395414137368263 41591583635093121206052395)
        ·
          refine ⟨62387375452639681809078593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41591583635093121206052395 62387375452639681809078593)
          ·
            refine ⟨46790531589479761356808945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62387375452639681809078593 46790531589479761356808945)
            ·
              refine ⟨35092898692109821017606709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46790531589479761356808945 35092898692109821017606709)
              ·
                refine ⟨3289959252385295720400629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35092898692109821017606709 3289959252385295720400629)
                ·
                  refine ⟨308433679911121473787559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3289959252385295720400629 308433679911121473787559)
                  ·
                    rfl

theorem cell22_2703026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_2703026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703026 prefixEnd_2703026 := by exact prefixLift 2703026
  have htrace : WordTrace (prefixWord ++ tailWord_2703026) baseStart_2703026 baseEnd_2703026 := by
    simpa [prefixWord, tailWord_2703026, baseEnd_2703026] using wordTrace_append hprefix tailTrace_2703026
  have hstable : (prefixWord ++ tailWord_2703026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703026).length < 2 ^ (prefixWord ++ tailWord_2703026).sum := by decide
  have hdescent : baseEnd_2703026 < baseStart_2703026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703118 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_2703118 : Nat := 118140960795 + 2703118 * 2 ^ 59
def prefixEnd_2703118 : Nat := 4983230072969 + 3 ^ 40 * 2703118 * 2
def baseEnd_2703118 : Nat := 925332533213506848062395

theorem tailTrace_2703118 : CollatzResearch.WordTrace tailWord_2703118 prefixEnd_2703118 925332533213506848062395 := by
  unfold tailWord_2703118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12323851627634077080651751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65727208680715077763476005 12323851627634077080651751)
  ·
    refine ⟨18485777441451115620977627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12323851627634077080651751 18485777441451115620977627)
    ·
      refine ⟨27728666162176673431466441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18485777441451115620977627 27728666162176673431466441)
      ·
        refine ⟨20796499621632505073599831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27728666162176673431466441 20796499621632505073599831)
        ·
          refine ⟨31194749432448757610399747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20796499621632505073599831 31194749432448757610399747)
          ·
            refine ⟨46792124148673136415599621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31194749432448757610399747 46792124148673136415599621)
            ·
              refine ⟨8773523277876213077924929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46792124148673136415599621 8773523277876213077924929)
              ·
                refine ⟨6580142458407159808443697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8773523277876213077924929 6580142458407159808443697)
                ·
                  refine ⟨4935106843805369856332773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6580142458407159808443697 4935106843805369856332773)
                  ·
                    refine ⟨925332533213506848062395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4935106843805369856332773 925332533213506848062395)
                    ·
                      rfl

theorem cell22_2703118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_2703118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703118 prefixEnd_2703118 := by exact prefixLift 2703118
  have htrace : WordTrace (prefixWord ++ tailWord_2703118) baseStart_2703118 baseEnd_2703118 := by
    simpa [prefixWord, tailWord_2703118, baseEnd_2703118] using wordTrace_append hprefix tailTrace_2703118
  have hstable : (prefixWord ++ tailWord_2703118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703118).length < 2 ^ (prefixWord ++ tailWord_2703118).sum := by decide
  have hdescent : baseEnd_2703118 < baseStart_2703118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703122 : List Nat := [3, 2, 4, 1, 1, 2, 1, 4, 4]
def baseStart_2703122 : Nat := 118140960795 + 2703122 * 2 ^ 59
def prefixEnd_2703122 : Nat := 4983230072969 + 3 ^ 40 * 2703122 * 2
def baseEnd_2703122 : Nat := 308444634165084056987461

theorem tailTrace_2703122 : CollatzResearch.WordTrace tailWord_2703122 prefixEnd_2703122 308444634165084056987461 := by
  unfold tailWord_2703122
  simp only [CollatzResearch.WordTrace]
  refine ⟨24647739728264531332089905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65727305942038750218906413 24647739728264531332089905)
  ·
    refine ⟨18485804796198398499067429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24647739728264531332089905 18485804796198398499067429)
    ·
      refine ⟨3466088399287199718575143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18485804796198398499067429 3466088399287199718575143)
      ·
        refine ⟨5199132598930799577862715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3466088399287199718575143 5199132598930799577862715)
        ·
          refine ⟨7798698898396199366794073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5199132598930799577862715 7798698898396199366794073)
          ·
            refine ⟨5849024173797149525095555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7798698898396199366794073 5849024173797149525095555)
            ·
              refine ⟨8773536260695724287643333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5849024173797149525095555 8773536260695724287643333)
              ·
                refine ⟨1645038048880448303933125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8773536260695724287643333 1645038048880448303933125)
                ·
                  refine ⟨308444634165084056987461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1645038048880448303933125 308444634165084056987461)
                  ·
                    rfl

theorem cell22_2703122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_2703122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703122 prefixEnd_2703122 := by exact prefixLift 2703122
  have htrace : WordTrace (prefixWord ++ tailWord_2703122) baseStart_2703122 baseEnd_2703122 := by
    simpa [prefixWord, tailWord_2703122, baseEnd_2703122] using wordTrace_append hprefix tailTrace_2703122
  have hstable : (prefixWord ++ tailWord_2703122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703122).length < 2 ^ (prefixWord ++ tailWord_2703122).sum := by decide
  have hdescent : baseEnd_2703122 < baseStart_2703122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703148 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 5, 3]
def baseStart_2703148 : Nat := 118140960795 + 2703148 * 2 ^ 59
def prefixEnd_2703148 : Nat := 4983230072969 + 3 ^ 40 * 2703148 * 2
def baseEnd_2703148 : Nat := 925342802826596769812303

theorem tailTrace_2703148 : CollatzResearch.WordTrace tailWord_2703148 prefixEnd_2703148 925342802826596769812303 := by
  unfold tailWord_2703148
  simp only [CollatzResearch.WordTrace]
  refine ⟨49295953605481965884403049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65727938140642621179204065 49295953605481965884403049)
  ·
    refine ⟨36971965204111474413302287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49295953605481965884403049 36971965204111474413302287)
    ·
      refine ⟨55457947806167211619953431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36971965204111474413302287 55457947806167211619953431)
      ·
        refine ⟨83186921709250817429930147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55457947806167211619953431 83186921709250817429930147)
        ·
          refine ⟨124780382563876226144895221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83186921709250817429930147 124780382563876226144895221)
          ·
            refine ⟨11698160865363396201083927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124780382563876226144895221 11698160865363396201083927)
            ·
              refine ⟨17547241298045094301625891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11698160865363396201083927 17547241298045094301625891)
              ·
                refine ⟨26320861947067641452438837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17547241298045094301625891 26320861947067641452438837)
                ·
                  refine ⟨2467580807537591386166141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26320861947067641452438837 2467580807537591386166141)
                  ·
                    refine ⟨925342802826596769812303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2467580807537591386166141 925342802826596769812303)
                    ·
                      rfl

theorem cell22_2703148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_2703148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703148 prefixEnd_2703148 := by exact prefixLift 2703148
  have htrace : WordTrace (prefixWord ++ tailWord_2703148) baseStart_2703148 baseEnd_2703148 := by
    simpa [prefixWord, tailWord_2703148, baseEnd_2703148] using wordTrace_append hprefix tailTrace_2703148
  have hstable : (prefixWord ++ tailWord_2703148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703148).length < 2 ^ (prefixWord ++ tailWord_2703148).sum := by decide
  have hdescent : baseEnd_2703148 < baseStart_2703148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703246 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_2703246 : Nat := 118140960795 + 2703246 * 2 ^ 59
def prefixEnd_2703246 : Nat := 4983230072969 + 3 ^ 40 * 2703246 * 2
def baseEnd_2703246 : Nat := 308458783409785726954001

theorem tailTrace_2703246 : CollatzResearch.WordTrace tailWord_2703246 prefixEnd_2703246 308458783409785726954001 := by
  unfold tailWord_2703246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12324435195576111813234199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65730321043072596337249061 12324435195576111813234199)
  ·
    refine ⟨18486652793364167719851299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12324435195576111813234199 18486652793364167719851299)
    ·
      refine ⟨27729979190046251579776949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18486652793364167719851299 27729979190046251579776949)
      ·
        refine ⟨2599685549066836085604089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27729979190046251579776949 2599685549066836085604089)
        ·
          refine ⟨1949764161800127064203067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2599685549066836085604089 1949764161800127064203067)
          ·
            refine ⟨2924646242700190596304601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949764161800127064203067 2924646242700190596304601)
            ·
              refine ⟨2193484682025142947228451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2924646242700190596304601 2193484682025142947228451)
              ·
                refine ⟨3290227023037714420842677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193484682025142947228451 3290227023037714420842677)
                ·
                  refine ⟨308458783409785726954001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3290227023037714420842677 308458783409785726954001)
                  ·
                    rfl

theorem cell22_2703246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_2703246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703246 prefixEnd_2703246 := by exact prefixLift 2703246
  have htrace : WordTrace (prefixWord ++ tailWord_2703246) baseStart_2703246 baseEnd_2703246 := by
    simpa [prefixWord, tailWord_2703246, baseEnd_2703246] using wordTrace_append hprefix tailTrace_2703246
  have hstable : (prefixWord ++ tailWord_2703246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703246).length < 2 ^ (prefixWord ++ tailWord_2703246).sum := by decide
  have hdescent : baseEnd_2703246 < baseStart_2703246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703253 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2703253 : Nat := 118140960795 + 2703253 * 2 ^ 59
def prefixEnd_2703253 : Nat := 4983230072969 + 3 ^ 40 * 2703253 * 2
def baseEnd_2703253 : Nat := 925378746472411495936981

theorem tailTrace_2703253 : CollatzResearch.WordTrace tailWord_2703253 prefixEnd_2703253 925378746472411495936981 := by
  unfold tailWord_2703253
  simp only [CollatzResearch.WordTrace]
  refine ⟨98595736875583534701378413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65730491250389023134252275 98595736875583534701378413)
  ·
    refine ⟨36973401328343825513016905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98595736875583534701378413 36973401328343825513016905)
    ·
      refine ⟨27730050996257869134762679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36973401328343825513016905 27730050996257869134762679)
      ·
        refine ⟨41595076494386803702144019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27730050996257869134762679 41595076494386803702144019)
        ·
          refine ⟨62392614741580205553216029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41595076494386803702144019 62392614741580205553216029)
          ·
            refine ⟨23397230528092577082456011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62392614741580205553216029 23397230528092577082456011)
            ·
              refine ⟨35095845792138865623684017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23397230528092577082456011 35095845792138865623684017)
              ·
                refine ⟨26321884344104149217763013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35095845792138865623684017 26321884344104149217763013)
                ·
                  refine ⟨4935353314519527978330565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26321884344104149217763013 4935353314519527978330565)
                  ·
                    refine ⟨925378746472411495936981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4935353314519527978330565 925378746472411495936981)
                    ·
                      rfl

theorem cell22_2703253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2703253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703253 prefixEnd_2703253 := by exact prefixLift 2703253
  have htrace : WordTrace (prefixWord ++ tailWord_2703253) baseStart_2703253 baseEnd_2703253 := by
    simpa [prefixWord, tailWord_2703253, baseEnd_2703253] using wordTrace_append hprefix tailTrace_2703253
  have hstable : (prefixWord ++ tailWord_2703253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703253).length < 2 ^ (prefixWord ++ tailWord_2703253).sum := by decide
  have hdescent : baseEnd_2703253 < baseStart_2703253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703268 : List Nat := [2, 3, 1, 2, 1, 3, 2, 8]
def baseStart_2703268 : Nat := 118140960795 + 2703268 * 2 ^ 59
def prefixEnd_2703268 : Nat := 4983230072969 + 3 ^ 40 * 2703268 * 2
def baseEnd_2703268 : Nat := 102820431253217384090215

theorem tailTrace_2703268 : CollatzResearch.WordTrace tailWord_2703268 prefixEnd_2703268 102820431253217384090215 := by
  unfold tailWord_2703268
  simp only [CollatzResearch.WordTrace]
  refine ⟨49298141985264596131587229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65730855980352794842116305 49298141985264596131587229)
  ·
    refine ⟨18486803244474223549345211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49298141985264596131587229 18486803244474223549345211)
    ·
      refine ⟨27730204866711335324017817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18486803244474223549345211 27730204866711335324017817)
      ·
        refine ⟨20797653650033501493013363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27730204866711335324017817 20797653650033501493013363)
        ·
          refine ⟨31196480475050252239520045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20797653650033501493013363 31196480475050252239520045)
          ·
            refine ⟨11698680178143844589820017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31196480475050252239520045 11698680178143844589820017)
            ·
              refine ⟨8774010133607883442365013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11698680178143844589820017 8774010133607883442365013)
              ·
                refine ⟨102820431253217384090215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8774010133607883442365013 102820431253217384090215)
                ·
                  rfl

theorem cell22_2703268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 8].length) (baseStart_2703268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703268 prefixEnd_2703268 := by exact prefixLift 2703268
  have htrace : WordTrace (prefixWord ++ tailWord_2703268) baseStart_2703268 baseEnd_2703268 := by
    simpa [prefixWord, tailWord_2703268, baseEnd_2703268] using wordTrace_append hprefix tailTrace_2703268
  have hstable : (prefixWord ++ tailWord_2703268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703268).length < 2 ^ (prefixWord ++ tailWord_2703268).sum := by decide
  have hdescent : baseEnd_2703268 < baseStart_2703268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703317 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 3, 3]
def baseStart_2703317 : Nat := 118140960795 + 2703317 * 2 ^ 59
def prefixEnd_2703317 : Nat := 4983230072969 + 3 ^ 40 * 2703317 * 2
def baseEnd_2703317 : Nat := 925400654980336662336785

theorem tailTrace_2703317 : CollatzResearch.WordTrace tailWord_2703317 prefixEnd_2703317 925400654980336662336785 := by
  unfold tailWord_2703317
  simp only [CollatzResearch.WordTrace]
  refine ⟨98598071147351673631708205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65732047431567782421138803 98598071147351673631708205)
  ·
    refine ⟨36974276680256877611890577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98598071147351673631708205 36974276680256877611890577)
    ·
      refine ⟨27730707510192658208917933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36974276680256877611890577 27730707510192658208917933)
      ·
        refine ⟨10399015316322246828344225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27730707510192658208917933 10399015316322246828344225)
        ·
          refine ⟨7799261487241685121258169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10399015316322246828344225 7799261487241685121258169)
          ·
            refine ⟨5849446115431263840943627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7799261487241685121258169 5849446115431263840943627)
            ·
              refine ⟨8774169173146895761415441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5849446115431263840943627 8774169173146895761415441)
              ·
                refine ⟨6580626879860171821061581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8774169173146895761415441 6580626879860171821061581)
                ·
                  refine ⟨2467735079947564432898093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6580626879860171821061581 2467735079947564432898093)
                  ·
                    refine ⟨925400654980336662336785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2467735079947564432898093 925400654980336662336785)
                    ·
                      rfl

theorem cell22_2703317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_2703317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703317 prefixEnd_2703317 := by exact prefixLift 2703317
  have htrace : WordTrace (prefixWord ++ tailWord_2703317) baseStart_2703317 baseEnd_2703317 := by
    simpa [prefixWord, tailWord_2703317, baseEnd_2703317] using wordTrace_append hprefix tailTrace_2703317
  have hstable : (prefixWord ++ tailWord_2703317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703317).length < 2 ^ (prefixWord ++ tailWord_2703317).sum := by decide
  have hdescent : baseEnd_2703317 < baseStart_2703317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703409 : List Nat := [1, 2, 2, 3, 1, 4, 3, 2, 4]
def baseStart_2703409 : Nat := 118140960795 + 2703409 * 2 ^ 59
def prefixEnd_2703409 : Nat := 4983230072969 + 3 ^ 40 * 2703409 * 2
def baseEnd_2703409 : Nat := 308477382820159696345501

theorem tailTrace_2703409 : CollatzResearch.WordTrace tailWord_2703409 prefixEnd_2703409 308477382820159696345501 := by
  unfold tailWord_2703409
  simp only [CollatzResearch.WordTrace]
  refine ⟨98601426663018373344057281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65734284442012248896038187 98601426663018373344057281)
  ·
    refine ⟨73951069997263780008042961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98601426663018373344057281 73951069997263780008042961)
    ·
      refine ⟨55463302497947835006032221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73951069997263780008042961 55463302497947835006032221)
      ·
        refine ⟨20798738436730438127262083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55463302497947835006032221 20798738436730438127262083)
        ·
          refine ⟨31198107655095657190893125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20798738436730438127262083 31198107655095657190893125)
          ·
            refine ⟨5849645185330435723292461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31198107655095657190893125 5849645185330435723292461)
            ·
              refine ⟨2193616944498913396234673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5849645185330435723292461 2193616944498913396234673)
              ·
                refine ⟨1645212708374185047176005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2193616944498913396234673 1645212708374185047176005)
                ·
                  refine ⟨308477382820159696345501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1645212708374185047176005 308477382820159696345501)
                  ·
                    rfl

theorem cell22_2703409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 4].length) (baseStart_2703409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703409 prefixEnd_2703409 := by exact prefixLift 2703409
  have htrace : WordTrace (prefixWord ++ tailWord_2703409) baseStart_2703409 baseEnd_2703409 := by
    simpa [prefixWord, tailWord_2703409, baseEnd_2703409] using wordTrace_append hprefix tailTrace_2703409
  have hstable : (prefixWord ++ tailWord_2703409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703409).length < 2 ^ (prefixWord ++ tailWord_2703409).sum := by decide
  have hdescent : baseEnd_2703409 < baseStart_2703409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703420 : List Nat := [2, 2, 2, 2, 2, 1, 4, 7]
def baseStart_2703420 : Nat := 118140960795 + 2703420 * 2 ^ 59
def prefixEnd_2703420 : Nat := 4983230072969 + 3 ^ 40 * 2703420 * 2
def baseEnd_2703420 : Nat := 102826212665030969667941

theorem tailTrace_2703420 : CollatzResearch.WordTrace tailWord_2703420 prefixEnd_2703420 102826212665030969667941 := by
  unfold tailWord_2703420
  simp only [CollatzResearch.WordTrace]
  refine ⟨49300913932989261111353857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65734551910652348148471809 49300913932989261111353857)
  ·
    refine ⟨36975685449741945833515393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49300913932989261111353857 36975685449741945833515393)
    ·
      refine ⟨27731764087306459375136545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36975685449741945833515393 27731764087306459375136545)
      ·
        refine ⟨20798823065479844531352409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27731764087306459375136545 20798823065479844531352409)
        ·
          refine ⟨15599117299109883398514307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20798823065479844531352409 15599117299109883398514307)
          ·
            refine ⟨23398675948664825097771461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15599117299109883398514307 23398675948664825097771461)
            ·
              refine ⟨4387251740374654705832149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23398675948664825097771461 4387251740374654705832149)
              ·
                refine ⟨102826212665030969667941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4387251740374654705832149 102826212665030969667941)
                ·
                  rfl

theorem cell22_2703420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 7].length) (baseStart_2703420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703420 prefixEnd_2703420 := by exact prefixLift 2703420
  have htrace : WordTrace (prefixWord ++ tailWord_2703420) baseStart_2703420 baseEnd_2703420 := by
    simpa [prefixWord, tailWord_2703420, baseEnd_2703420] using wordTrace_append hprefix tailTrace_2703420
  have hstable : (prefixWord ++ tailWord_2703420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703420).length < 2 ^ (prefixWord ++ tailWord_2703420).sum := by decide
  have hdescent : baseEnd_2703420 < baseStart_2703420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703424 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 2, 3]
def baseStart_2703424 : Nat := 118140960795 + 2703424 * 2 ^ 59
def prefixEnd_2703424 : Nat := 4983230072969 + 3 ^ 40 * 2703424 * 2
def baseEnd_2703424 : Nat := 925437283267024049911457

theorem tailTrace_2703424 : CollatzResearch.WordTrace tailWord_2703424 prefixEnd_2703424 925437283267024049911457 := by
  unfold tailWord_2703424
  simp only [CollatzResearch.WordTrace]
  refine ⟨49300986878982015452926663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65734649171976020603902217 49300986878982015452926663)
  ·
    refine ⟨73951480318473023179389995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49300986878982015452926663 73951480318473023179389995)
    ·
      refine ⟨110927220477709534769084993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73951480318473023179389995 110927220477709534769084993)
      ·
        refine ⟨83195415358282151076813745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110927220477709534769084993 83195415358282151076813745)
        ·
          refine ⟨62396561518711613307610309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83195415358282151076813745 62396561518711613307610309)
          ·
            refine ⟨11699355284758427495176933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62396561518711613307610309 11699355284758427495176933)
            ·
              refine ⟨2193629115892205155345675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11699355284758427495176933 2193629115892205155345675)
              ·
                refine ⟨3290443673838307733018513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193629115892205155345675 3290443673838307733018513)
                ·
                  refine ⟨2467832755378730799763885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3290443673838307733018513 2467832755378730799763885)
                  ·
                    refine ⟨925437283267024049911457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2467832755378730799763885 925437283267024049911457)
                    ·
                      rfl

theorem cell22_2703424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 2, 3].length) (baseStart_2703424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703424 prefixEnd_2703424 := by exact prefixLift 2703424
  have htrace : WordTrace (prefixWord ++ tailWord_2703424) baseStart_2703424 baseEnd_2703424 := by
    simpa [prefixWord, tailWord_2703424, baseEnd_2703424] using wordTrace_append hprefix tailTrace_2703424
  have hstable : (prefixWord ++ tailWord_2703424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703424).length < 2 ^ (prefixWord ++ tailWord_2703424).sum := by decide
  have hdescent : baseEnd_2703424 < baseStart_2703424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703454 : List Nat := [4, 4, 1, 1, 2, 10]
def baseStart_2703454 : Nat := 118140960795 + 2703454 * 2 ^ 59
def prefixEnd_2703454 : Nat := 4983230072969 + 3 ^ 40 * 2703454 * 2
def baseEnd_2703454 : Nat := 11425278430618691008165

theorem tailTrace_2703454 : CollatzResearch.WordTrace tailWord_2703454 prefixEnd_2703454 11425278430618691008165 := by
  unfold tailWord_2703454
  simp only [CollatzResearch.WordTrace]
  refine ⟨12325383493481918253680677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65735378631903564019630277 12325383493481918253680677)
  ·
    refine ⟨2311009405027859672565127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12325383493481918253680677 2311009405027859672565127)
    ·
      refine ⟨3466514107541789508847691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2311009405027859672565127 3466514107541789508847691)
      ·
        refine ⟨5199771161312684263271537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3466514107541789508847691 5199771161312684263271537)
        ·
          refine ⟨3899828370984513197453653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5199771161312684263271537 3899828370984513197453653)
          ·
            refine ⟨11425278430618691008165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3899828370984513197453653 11425278430618691008165)
            ·
              rfl

theorem cell22_2703454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 10].length) (baseStart_2703454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703454 prefixEnd_2703454 := by exact prefixLift 2703454
  have htrace : WordTrace (prefixWord ++ tailWord_2703454) baseStart_2703454 baseEnd_2703454 := by
    simpa [prefixWord, tailWord_2703454, baseEnd_2703454] using wordTrace_append hprefix tailTrace_2703454
  have hstable : (prefixWord ++ tailWord_2703454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703454).length < 2 ^ (prefixWord ++ tailWord_2703454).sum := by decide
  have hdescent : baseEnd_2703454 < baseStart_2703454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703655 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2703655 : Nat := 118140960795 + 2703655 * 2 ^ 59
def prefixEnd_2703655 : Nat := 4983230072969 + 3 ^ 40 * 2703655 * 2
def baseEnd_2703655 : Nat := 925516359287816447385749

theorem tailTrace_2703655 : CollatzResearch.WordTrace tailWord_2703655 prefixEnd_2703655 925516359287816447385749 := by
  unfold tailWord_2703655
  simp only [CollatzResearch.WordTrace]
  refine ⟨98610399020127157357512419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65740266013418104905008279 98610399020127157357512419)
  ·
    refine ⟨147915598530190736036268629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98610399020127157357512419 147915598530190736036268629)
    ·
      refine ⟨1733385920275672687925023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 147915598530190736036268629 1733385920275672687925023)
      ·
        refine ⟨2600078880413509031887535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733385920275672687925023 2600078880413509031887535)
        ·
          refine ⟨3900118320620263547831303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600078880413509031887535 3900118320620263547831303)
          ·
            refine ⟨5850177480930395321746955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900118320620263547831303 5850177480930395321746955)
            ·
              refine ⟨8775266221395592982620433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5850177480930395321746955 8775266221395592982620433)
              ·
                refine ⟨6581449666046694736965325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8775266221395592982620433 6581449666046694736965325)
                ·
                  refine ⟨2468043624767510526361997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6581449666046694736965325 2468043624767510526361997)
                  ·
                    refine ⟨925516359287816447385749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468043624767510526361997 925516359287816447385749)
                    ·
                      rfl

theorem cell22_2703655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2703655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703655 prefixEnd_2703655 := by exact prefixLift 2703655
  have htrace : WordTrace (prefixWord ++ tailWord_2703655) baseStart_2703655 baseEnd_2703655 := by
    simpa [prefixWord, tailWord_2703655, baseEnd_2703655] using wordTrace_append hprefix tailTrace_2703655
  have hstable : (prefixWord ++ tailWord_2703655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703655).length < 2 ^ (prefixWord ++ tailWord_2703655).sum := by decide
  have hdescent : baseEnd_2703655 < baseStart_2703655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703724 : List Nat := [2, 2, 1, 1, 6, 1, 1, 8]
def baseStart_2703724 : Nat := 118140960795 + 2703724 * 2 ^ 59
def prefixEnd_2703724 : Nat := 4983230072969 + 3 ^ 40 * 2703724 * 2
def baseEnd_2703724 : Nat := 102837775488658140823393

theorem tailTrace_2703724 : CollatzResearch.WordTrace tailWord_2703724 prefixEnd_2703724 102837775488658140823393 := by
  unfold tailWord_2703724
  simp only [CollatzResearch.WordTrace]
  refine ⟨49306457828438591070887113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65741943771251454761182817 49306457828438591070887113)
  ·
    refine ⟨36979843371328943303165335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49306457828438591070887113 36979843371328943303165335)
    ·
      refine ⟨55469765056993414954748003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36979843371328943303165335 55469765056993414954748003)
      ·
        refine ⟨83204647585490122432122005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55469765056993414954748003 83204647585490122432122005)
        ·
          refine ⟨3900217855569849489005719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83204647585490122432122005 3900217855569849489005719)
          ·
            refine ⟨5850326783354774233508579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900217855569849489005719 5850326783354774233508579)
            ·
              refine ⟨8775490175032161350262869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5850326783354774233508579 8775490175032161350262869)
              ·
                refine ⟨102837775488658140823393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8775490175032161350262869 102837775488658140823393)
                ·
                  rfl

theorem cell22_2703724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 8].length) (baseStart_2703724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703724 prefixEnd_2703724 := by exact prefixLift 2703724
  have htrace : WordTrace (prefixWord ++ tailWord_2703724) baseStart_2703724 baseEnd_2703724 := by
    simpa [prefixWord, tailWord_2703724, baseEnd_2703724] using wordTrace_append hprefix tailTrace_2703724
  have hstable : (prefixWord ++ tailWord_2703724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703724).length < 2 ^ (prefixWord ++ tailWord_2703724).sum := by decide
  have hdescent : baseEnd_2703724 < baseStart_2703724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703737 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_2703737 : Nat := 118140960795 + 2703737 * 2 ^ 59
def prefixEnd_2703737 : Nat := 4983230072969 + 3 ^ 40 * 2703737 * 2
def baseEnd_2703737 : Nat := 925544429563595566835497

theorem tailTrace_2703737 : CollatzResearch.WordTrace tailWord_2703737 prefixEnd_2703737 925544429563595566835497 := by
  unfold tailWord_2703737
  simp only [CollatzResearch.WordTrace]
  refine ⟨98613389805830085361997465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65742259870553390241331643 98613389805830085361997465)
  ·
    refine ⟨73960042354372564021498099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98613389805830085361997465 73960042354372564021498099)
    ·
      refine ⟨110940063531558846032247149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73960042354372564021498099 110940063531558846032247149)
      ·
        refine ⟨41602523824334567262092681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110940063531558846032247149 41602523824334567262092681)
        ·
          refine ⟨31201892868250925446569511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41602523824334567262092681 31201892868250925446569511)
          ·
            refine ⟨46802839302376388169854267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31201892868250925446569511 46802839302376388169854267)
            ·
              refine ⟨70204258953564582254781401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46802839302376388169854267 70204258953564582254781401)
              ·
                refine ⟨52653194215173436691086051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70204258953564582254781401 52653194215173436691086051)
                ·
                  refine ⟨78979791322760155036629077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52653194215173436691086051 78979791322760155036629077)
                  ·
                    refine ⟨925544429563595566835497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78979791322760155036629077 925544429563595566835497)
                    ·
                      rfl

theorem cell22_2703737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_2703737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703737 prefixEnd_2703737 := by exact prefixLift 2703737
  have htrace : WordTrace (prefixWord ++ tailWord_2703737) baseStart_2703737 baseEnd_2703737 := by
    simpa [prefixWord, tailWord_2703737, baseEnd_2703737] using wordTrace_append hprefix tailTrace_2703737
  have hstable : (prefixWord ++ tailWord_2703737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703737).length < 2 ^ (prefixWord ++ tailWord_2703737).sum := by decide
  have hdescent : baseEnd_2703737 < baseStart_2703737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703756 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 3, 3]
def baseStart_2703756 : Nat := 118140960795 + 2703756 * 2 ^ 59
def prefixEnd_2703756 : Nat := 4983230072969 + 3 ^ 40 * 2703756 * 2
def baseEnd_2703756 : Nat := 925550933651885850610439

theorem tailTrace_2703756 : CollatzResearch.WordTrace tailWord_2703756 prefixEnd_2703756 925550933651885850610439 := by
  unfold tailWord_2703756
  simp only [CollatzResearch.WordTrace]
  refine ⟨49307041396380625803469561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65742721861840834404626081 49307041396380625803469561)
  ·
    refine ⟨36980281047285469352602171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49307041396380625803469561 36980281047285469352602171)
    ·
      refine ⟨55470421570928204028903257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36980281047285469352602171 55470421570928204028903257)
      ·
        refine ⟨41602816178196153021677443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55470421570928204028903257 41602816178196153021677443)
        ·
          refine ⟨62404224267294229532516165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41602816178196153021677443 62404224267294229532516165)
          ·
            refine ⟨11700792050117668037346781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62404224267294229532516165 11700792050117668037346781)
            ·
              refine ⟨4387797018794125514005043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11700792050117668037346781 4387797018794125514005043)
              ·
                refine ⟨6581695528191188271007565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4387797018794125514005043 6581695528191188271007565)
                ·
                  refine ⟨2468135823071695601627837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6581695528191188271007565 2468135823071695601627837)
                  ·
                    refine ⟨925550933651885850610439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468135823071695601627837 925550933651885850610439)
                    ·
                      rfl

theorem cell22_2703756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_2703756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703756 prefixEnd_2703756 := by exact prefixLift 2703756
  have htrace : WordTrace (prefixWord ++ tailWord_2703756) baseStart_2703756 baseEnd_2703756 := by
    simpa [prefixWord, tailWord_2703756, baseEnd_2703756] using wordTrace_append hprefix tailTrace_2703756
  have hstable : (prefixWord ++ tailWord_2703756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703756).length < 2 ^ (prefixWord ++ tailWord_2703756).sum := by decide
  have hdescent : baseEnd_2703756 < baseStart_2703756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703769 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 5]
def baseStart_2703769 : Nat := 118140960795 + 2703769 * 2 ^ 59
def prefixEnd_2703769 : Nat := 4983230072969 + 3 ^ 40 * 2703769 * 2
def baseEnd_2703769 : Nat := 308518461272519383345133

theorem tailTrace_2703769 : CollatzResearch.WordTrace tailWord_2703769 prefixEnd_2703769 308518461272519383345133 := by
  unfold tailWord_2703769
  simp only [CollatzResearch.WordTrace]
  refine ⟨98614556941714154827162361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65743037961142769884774907 98614556941714154827162361)
  ·
    refine ⟨73960917706285616120371771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98614556941714154827162361 73960917706285616120371771)
    ·
      refine ⟨110941376559428424180557657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73960917706285616120371771 110941376559428424180557657)
      ·
        refine ⟨83206032419571318135418243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110941376559428424180557657 83206032419571318135418243)
        ·
          refine ⟨124809048629356977203127365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83206032419571318135418243 124809048629356977203127365)
          ·
            refine ⟨23401696618004433225586381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124809048629356977203127365 23401696618004433225586381)
            ·
              refine ⟨8775636231751662459594893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23401696618004433225586381 8775636231751662459594893)
              ·
                refine ⟨3290863586906873422348085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8775636231751662459594893 3290863586906873422348085)
                ·
                  refine ⟨308518461272519383345133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3290863586906873422348085 308518461272519383345133)
                  ·
                    rfl

theorem cell22_2703769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_2703769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703769 prefixEnd_2703769 := by exact prefixLift 2703769
  have htrace : WordTrace (prefixWord ++ tailWord_2703769) baseStart_2703769 baseEnd_2703769 := by
    simpa [prefixWord, tailWord_2703769, baseEnd_2703769] using wordTrace_append hprefix tailTrace_2703769
  have hstable : (prefixWord ++ tailWord_2703769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703769).length < 2 ^ (prefixWord ++ tailWord_2703769).sum := by decide
  have hdescent : baseEnd_2703769 < baseStart_2703769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703848 : List Nat := [2, 1, 4, 1, 1, 4, 2, 3, 4]
def baseStart_2703848 : Nat := 118140960795 + 2703848 * 2 ^ 59
def prefixEnd_2703848 : Nat := 4983230072969 + 3 ^ 40 * 2703848 * 2
def baseEnd_2703848 : Nat := 308527475710676092436719

theorem tailTrace_2703848 : CollatzResearch.WordTrace tailWord_2703848 prefixEnd_2703848 308527475710676092436719 := by
  unfold tailWord_2703848
  simp only [CollatzResearch.WordTrace]
  refine ⟨49308719154213975659644099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65744958872285300879525465 49308719154213975659644099)
  ·
    refine ⟨73963078731320963489466149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49308719154213975659644099 73963078731320963489466149)
    ·
      refine ⟨13868077262122680654274903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73963078731320963489466149 13868077262122680654274903)
      ·
        refine ⟨20802115893184020981412355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13868077262122680654274903 20802115893184020981412355)
        ·
          refine ⟨31203173839776031472118533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20802115893184020981412355 31203173839776031472118533)
          ·
            refine ⟨5850595094958005901022225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31203173839776031472118533 5850595094958005901022225)
            ·
              refine ⟨4387946321218504425766669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5850595094958005901022225 4387946321218504425766669)
              ·
                refine ⟨1645479870456939159662501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4387946321218504425766669 1645479870456939159662501)
                ·
                  refine ⟨308527475710676092436719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1645479870456939159662501 308527475710676092436719)
                  ·
                    rfl

theorem cell22_2703848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 4].length) (baseStart_2703848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703848 prefixEnd_2703848 := by exact prefixLift 2703848
  have htrace : WordTrace (prefixWord ++ tailWord_2703848) baseStart_2703848 baseEnd_2703848 := by
    simpa [prefixWord, tailWord_2703848, baseEnd_2703848] using wordTrace_append hprefix tailTrace_2703848
  have hstable : (prefixWord ++ tailWord_2703848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703848).length < 2 ^ (prefixWord ++ tailWord_2703848).sum := by decide
  have hdescent : baseEnd_2703848 < baseStart_2703848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703850 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 1, 4]
def baseStart_2703850 : Nat := 118140960795 + 2703850 * 2 ^ 59
def prefixEnd_2703850 : Nat := 4983230072969 + 3 ^ 40 * 2703850 * 2
def baseEnd_2703850 : Nat := 925583111772900938760151

theorem tailTrace_2703850 : CollatzResearch.WordTrace tailWord_2703850 prefixEnd_2703850 925583111772900938760151 := by
  unfold tailWord_2703850
  simp only [CollatzResearch.WordTrace]
  refine ⟨24654377813605176415215251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65745007502947137107240669 24654377813605176415215251)
  ·
    refine ⟨36981566720407764622822877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24654377813605176415215251 36981566720407764622822877)
    ·
      refine ⟨13868087520152911733558579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36981566720407764622822877 13868087520152911733558579)
      ·
        refine ⟨20802131280229367600337869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13868087520152911733558579 20802131280229367600337869)
        ·
          refine ⟨7800799230086012850126701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20802131280229367600337869 7800799230086012850126701)
          ·
            refine ⟨2925299711282254818797513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7800799230086012850126701 2925299711282254818797513)
            ·
              refine ⟨2193974783461691114098135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2925299711282254818797513 2193974783461691114098135)
              ·
                refine ⟨3290962175192536671147203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193974783461691114098135 3290962175192536671147203)
                ·
                  refine ⟨4936443262788805006720805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3290962175192536671147203 4936443262788805006720805)
                  ·
                    refine ⟨925583111772900938760151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4936443262788805006720805 925583111772900938760151)
                    ·
                      rfl

theorem cell22_2703850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_2703850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703850 prefixEnd_2703850 := by exact prefixLift 2703850
  have htrace : WordTrace (prefixWord ++ tailWord_2703850) baseStart_2703850 baseEnd_2703850 := by
    simpa [prefixWord, tailWord_2703850, baseEnd_2703850] using wordTrace_append hprefix tailTrace_2703850
  have hstable : (prefixWord ++ tailWord_2703850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703850).length < 2 ^ (prefixWord ++ tailWord_2703850).sum := by decide
  have hdescent : baseEnd_2703850 < baseStart_2703850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703891 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 3, 3]
def baseStart_2703891 : Nat := 118140960795 + 2703891 * 2 ^ 59
def prefixEnd_2703891 : Nat := 4983230072969 + 3 ^ 40 * 2703891 * 2
def baseEnd_2703891 : Nat := 925597146910790498485025

theorem tailTrace_2703891 : CollatzResearch.WordTrace tailWord_2703891 prefixEnd_2703891 925597146910790498485025 := by
  unfold tailWord_2703891
  simp only [CollatzResearch.WordTrace]
  refine ⟨98619006647272169663103527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65746004431514779775402351 98619006647272169663103527)
  ·
    refine ⟨147928509970908254494655291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98619006647272169663103527 147928509970908254494655291)
    ·
      refine ⟨221892764956362381741982937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147928509970908254494655291 221892764956362381741982937)
      ·
        refine ⟨166419573717271786306487203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221892764956362381741982937 166419573717271786306487203)
        ·
          refine ⟨249629360575907679459730805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166419573717271786306487203 249629360575907679459730805)
          ·
            refine ⟨23402752553991344949349763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 249629360575907679459730805 23402752553991344949349763)
            ·
              refine ⟨35104128830987017424024645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23402752553991344949349763 35104128830987017424024645)
              ·
                refine ⟨6582024155810065767004621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35104128830987017424024645 6582024155810065767004621)
                ·
                  refine ⟨2468259058428774662626733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6582024155810065767004621 2468259058428774662626733)
                  ·
                    refine ⟨925597146910790498485025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468259058428774662626733 925597146910790498485025)
                    ·
                      rfl

theorem cell22_2703891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 3].length) (baseStart_2703891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703891 prefixEnd_2703891 := by exact prefixLift 2703891
  have htrace : WordTrace (prefixWord ++ tailWord_2703891) baseStart_2703891 baseEnd_2703891 := by
    simpa [prefixWord, tailWord_2703891, baseEnd_2703891] using wordTrace_append hprefix tailTrace_2703891
  have hstable : (prefixWord ++ tailWord_2703891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703891).length < 2 ^ (prefixWord ++ tailWord_2703891).sum := by decide
  have hdescent : baseEnd_2703891 < baseStart_2703891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703976 : List Nat := [2, 1, 4, 3, 3, 1, 2, 2, 1, 3]
def baseStart_2703976 : Nat := 118140960795 + 2703976 * 2 ^ 59
def prefixEnd_2703976 : Nat := 4983230072969 + 3 ^ 40 * 2703976 * 2
def baseEnd_2703976 : Nat := 925626244147878610109765

theorem tailTrace_2703976 : CollatzResearch.WordTrace tailWord_2703976 prefixEnd_2703976 925626244147878610109765 := by
  unfold tailWord_2703976
  simp only [CollatzResearch.WordTrace]
  refine ⟨49311053425982114589973891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65748071234642819453298521 49311053425982114589973891)
  ·
    refine ⟨73966580138973171884960837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49311053425982114589973891 73966580138973171884960837)
    ·
      refine ⟨13868733776057469728430157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73966580138973171884960837 13868733776057469728430157)
      ·
        refine ⟨5200775166021551148161309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13868733776057469728430157 5200775166021551148161309)
        ·
          refine ⟨1950290687258081680560491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5200775166021551148161309 1950290687258081680560491)
          ·
            refine ⟨2925436030887122520840737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950290687258081680560491 2925436030887122520840737)
            ·
              refine ⟨2194077023165341890630553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2925436030887122520840737 2194077023165341890630553)
              ·
                refine ⟨1645557767374006417972915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2194077023165341890630553 1645557767374006417972915)
                ·
                  refine ⟨2468336651061009626959373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1645557767374006417972915 2468336651061009626959373)
                  ·
                    refine ⟨925626244147878610109765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468336651061009626959373 925626244147878610109765)
                    ·
                      rfl

theorem cell22_2703976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_2703976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703976 prefixEnd_2703976 := by exact prefixLift 2703976
  have htrace : WordTrace (prefixWord ++ tailWord_2703976) baseStart_2703976 baseEnd_2703976 := by
    simpa [prefixWord, tailWord_2703976, baseEnd_2703976] using wordTrace_append hprefix tailTrace_2703976
  have hstable : (prefixWord ++ tailWord_2703976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703976).length < 2 ^ (prefixWord ++ tailWord_2703976).sum := by decide
  have hdescent : baseEnd_2703976 < baseStart_2703976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2703996 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_2703996 : Nat := 118140960795 + 2703996 * 2 ^ 59
def prefixEnd_2703996 : Nat := 4983230072969 + 3 ^ 40 * 2703996 * 2
def baseEnd_2703996 : Nat := 925633090556605224609703

theorem tailTrace_2703996 : CollatzResearch.WordTrace tailWord_2703996 prefixEnd_2703996 925633090556605224609703 := by
  unfold tailWord_2703996
  simp only [CollatzResearch.WordTrace]
  refine ⟨49311418155945886297837921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65748557541261181730450561 49311418155945886297837921)
  ·
    refine ⟨36983563616959414723378441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49311418155945886297837921 36983563616959414723378441)
    ·
      refine ⟨27737672712719561042533831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36983563616959414723378441 27737672712719561042533831)
      ·
        refine ⟨41606509069079341563800747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27737672712719561042533831 41606509069079341563800747)
        ·
          refine ⟨62409763603619012345701121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41606509069079341563800747 62409763603619012345701121)
          ·
            refine ⟨46807322702714259259275841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62409763603619012345701121 46807322702714259259275841)
            ·
              refine ⟨35105492027035694444456881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46807322702714259259275841 35105492027035694444456881)
              ·
                refine ⟨26329119020276770833342661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35105492027035694444456881 26329119020276770833342661)
                ·
                  refine ⟨4936709816301894531251749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26329119020276770833342661 4936709816301894531251749)
                  ·
                    refine ⟨925633090556605224609703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4936709816301894531251749 925633090556605224609703)
                    ·
                      rfl

theorem cell22_2703996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_2703996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2703996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2703996 prefixEnd_2703996 := by exact prefixLift 2703996
  have htrace : WordTrace (prefixWord ++ tailWord_2703996) baseStart_2703996 baseEnd_2703996 := by
    simpa [prefixWord, tailWord_2703996, baseEnd_2703996] using wordTrace_append hprefix tailTrace_2703996
  have hstable : (prefixWord ++ tailWord_2703996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2703996).length < 2 ^ (prefixWord ++ tailWord_2703996).sum := by decide
  have hdescent : baseEnd_2703996 < baseStart_2703996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2703996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704032 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 2, 3]
def baseStart_2704032 : Nat := 118140960795 + 2704032 * 2 ^ 59
def prefixEnd_2704032 : Nat := 4983230072969 + 3 ^ 40 * 2704032 * 2
def baseEnd_2704032 : Nat := 925645414092313130709593

theorem tailTrace_2704032 : CollatzResearch.WordTrace tailWord_2704032 prefixEnd_2704032 925645414092313130709593 := by
  unfold tailWord_2704032
  simp only [CollatzResearch.WordTrace]
  refine ⟨49312074669880675371993175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65749432893174233829324233 49312074669880675371993175)
  ·
    refine ⟨73968112004821013057989763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49312074669880675371993175 73968112004821013057989763)
    ·
      refine ⟨110952168007231519586984645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73968112004821013057989763 110952168007231519586984645)
      ·
        refine ⟨20803531501355909922559621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110952168007231519586984645 20803531501355909922559621)
        ·
          refine ⟨3900662156504233110479929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20803531501355909922559621 3900662156504233110479929)
          ·
            refine ⟨2925496617378174832859947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3900662156504233110479929 2925496617378174832859947)
            ·
              refine ⟨4388244926067262249289921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2925496617378174832859947 4388244926067262249289921)
              ·
                refine ⟨3291183694550446686967441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4388244926067262249289921 3291183694550446686967441)
                ·
                  refine ⟨2468387770912835015225581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3291183694550446686967441 2468387770912835015225581)
                  ·
                    refine ⟨925645414092313130709593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468387770912835015225581 925645414092313130709593)
                    ·
                      rfl

theorem cell22_2704032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2, 3].length) (baseStart_2704032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704032 prefixEnd_2704032 := by exact prefixLift 2704032
  have htrace : WordTrace (prefixWord ++ tailWord_2704032) baseStart_2704032 baseEnd_2704032 := by
    simpa [prefixWord, tailWord_2704032, baseEnd_2704032] using wordTrace_append hprefix tailTrace_2704032
  have hstable : (prefixWord ++ tailWord_2704032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704032).length < 2 ^ (prefixWord ++ tailWord_2704032).sum := by decide
  have hdescent : baseEnd_2704032 < baseStart_2704032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704049 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 2, 3]
def baseStart_2704049 : Nat := 118140960795 + 2704049 * 2 ^ 59
def prefixEnd_2704049 : Nat := 4983230072969 + 3 ^ 40 * 2704049 * 2
def baseEnd_2704049 : Nat := 925651233539730753034541

theorem tailTrace_2704049 : CollatzResearch.WordTrace tailWord_2704049 prefixEnd_2704049 925651233539730753034541 := by
  unfold tailWord_2704049
  simp only [CollatzResearch.WordTrace]
  refine ⟨98624769380699762647355201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65749846253799841764903467 98624769380699762647355201)
  ·
    refine ⟨73968577035524821985516401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98624769380699762647355201 73968577035524821985516401)
    ·
      refine ⟨55476432776643616489137301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73968577035524821985516401 55476432776643616489137301)
      ·
        refine ⟨2600457786405169522928311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55476432776643616489137301 2600457786405169522928311)
        ·
          refine ⟨3900686679607754284392467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600457786405169522928311 3900686679607754284392467)
          ·
            refine ⟨5851030019411631426588701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900686679607754284392467 5851030019411631426588701)
            ·
              refine ⟨2194136257279361784970763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5851030019411631426588701 2194136257279361784970763)
              ·
                refine ⟨3291204385919042677456145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194136257279361784970763 3291204385919042677456145)
                ·
                  refine ⟨2468403289439282008092109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3291204385919042677456145 2468403289439282008092109)
                  ·
                    refine ⟨925651233539730753034541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468403289439282008092109 925651233539730753034541)
                    ·
                      rfl

theorem cell22_2704049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_2704049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704049 prefixEnd_2704049 := by exact prefixLift 2704049
  have htrace : WordTrace (prefixWord ++ tailWord_2704049) baseStart_2704049 baseEnd_2704049 := by
    simpa [prefixWord, tailWord_2704049, baseEnd_2704049] using wordTrace_append hprefix tailTrace_2704049
  have hstable : (prefixWord ++ tailWord_2704049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704049).length < 2 ^ (prefixWord ++ tailWord_2704049).sum := by decide
  have hdescent : baseEnd_2704049 < baseStart_2704049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704071 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 4, 5]
def baseStart_2704071 : Nat := 118140960795 + 2704071 * 2 ^ 59
def prefixEnd_2704071 : Nat := 4983230072969 + 3 ^ 40 * 2704071 * 2
def baseEnd_2704071 : Nat := 925658764589330028984473

theorem tailTrace_2704071 : CollatzResearch.WordTrace tailWord_2704071 prefixEnd_2704071 925658764589330028984473 := by
  unfold tailWord_2704071
  simp only [CollatzResearch.WordTrace]
  refine ⟨98625571786620060404656067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65750381191080040269770711 98625571786620060404656067)
  ·
    refine ⟨147938357679930090606984101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98625571786620060404656067 147938357679930090606984101)
    ·
      refine ⟨27738442064986891988809519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147938357679930090606984101 27738442064986891988809519)
      ·
        refine ⟨41607663097480337983214279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27738442064986891988809519 41607663097480337983214279)
        ·
          refine ⟨62411494646220506974821419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41607663097480337983214279 62411494646220506974821419)
          ·
            refine ⟨93617241969330760462232129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62411494646220506974821419 93617241969330760462232129)
            ·
              refine ⟨70212931476998070346674097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93617241969330760462232129 70212931476998070346674097)
              ·
                refine ⟨52659698607748552760005573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70212931476998070346674097 52659698607748552760005573)
                ·
                  refine ⟨9873693488952853642501045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52659698607748552760005573 9873693488952853642501045)
                  ·
                    refine ⟨925658764589330028984473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9873693488952853642501045 925658764589330028984473)
                    ·
                      rfl

theorem cell22_2704071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_2704071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704071 prefixEnd_2704071 := by exact prefixLift 2704071
  have htrace : WordTrace (prefixWord ++ tailWord_2704071) baseStart_2704071 baseEnd_2704071 := by
    simpa [prefixWord, tailWord_2704071, baseEnd_2704071] using wordTrace_append hprefix tailTrace_2704071
  have hstable : (prefixWord ++ tailWord_2704071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704071).length < 2 ^ (prefixWord ++ tailWord_2704071).sum := by decide
  have hdescent : baseEnd_2704071 < baseStart_2704071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704118 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_2704118 : Nat := 118140960795 + 2704118 * 2 ^ 59
def prefixEnd_2704118 : Nat := 4983230072969 + 3 ^ 40 * 2704118 * 2
def baseEnd_2704118 : Nat := 308558284549945857686443

theorem tailTrace_2704118 : CollatzResearch.WordTrace tailWord_2704118 prefixEnd_2704118 308558284549945857686443 := by
  unfold tailWord_2704118
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164205376090611714476063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65751524011633191621078005 6164205376090611714476063)
  ·
    refine ⟨9246308064135917571714095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6164205376090611714476063 9246308064135917571714095)
    ·
      refine ⟨13869462096203876357571143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9246308064135917571714095 13869462096203876357571143)
      ·
        refine ⟨20804193144305814536356715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13869462096203876357571143 20804193144305814536356715)
        ·
          refine ⟨31206289716458721804535073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20804193144305814536356715 31206289716458721804535073)
          ·
            refine ⟨23404717287344041353401305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31206289716458721804535073 23404717287344041353401305)
            ·
              refine ⟨17553537965508031015050979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23404717287344041353401305 17553537965508031015050979)
              ·
                refine ⟨26330306948262046522576469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17553537965508031015050979 26330306948262046522576469)
                ·
                  refine ⟨308558284549945857686443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26330306948262046522576469 308558284549945857686443)
                  ·
                    rfl

theorem cell22_2704118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_2704118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704118 prefixEnd_2704118 := by exact prefixLift 2704118
  have htrace : WordTrace (prefixWord ++ tailWord_2704118) baseStart_2704118 baseEnd_2704118 := by
    simpa [prefixWord, tailWord_2704118, baseEnd_2704118] using wordTrace_append hprefix tailTrace_2704118
  have hstable : (prefixWord ++ tailWord_2704118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704118).length < 2 ^ (prefixWord ++ tailWord_2704118).sum := by decide
  have hdescent : baseEnd_2704118 < baseStart_2704118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704133 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 6, 3]
def baseStart_2704133 : Nat := 118140960795 + 2704133 * 2 ^ 59
def prefixEnd_2704133 : Nat := 4983230072969 + 3 ^ 40 * 2704133 * 2
def baseEnd_2704133 : Nat := 925679988456382533934283

theorem tailTrace_2704133 : CollatzResearch.WordTrace tailWord_2704133 prefixEnd_2704133 925679988456382533934283 := by
  unfold tailWord_2704133
  simp only [CollatzResearch.WordTrace]
  refine ⟨98627833112395444993413053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65751888741596963328942035 98627833112395444993413053)
  ·
    refine ⟨36985437417148291872529895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98627833112395444993413053 36985437417148291872529895)
    ·
      refine ⟨55478156125722437808794843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36985437417148291872529895 55478156125722437808794843)
      ·
        refine ⟨83217234188583656713192265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55478156125722437808794843 83217234188583656713192265)
        ·
          refine ⟨62412925641437742534894199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83217234188583656713192265 62412925641437742534894199)
          ·
            refine ⟨93619388462156613802341299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62412925641437742534894199 93619388462156613802341299)
            ·
              refine ⟨140429082693234920703511949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93619388462156613802341299 140429082693234920703511949)
              ·
                refine ⟨52660906009963095263816981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140429082693234920703511949 52660906009963095263816981)
                ·
                  refine ⟨2468479969217020090491421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52660906009963095263816981 2468479969217020090491421)
                  ·
                    refine ⟨925679988456382533934283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468479969217020090491421 925679988456382533934283)
                    ·
                      rfl

theorem cell22_2704133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_2704133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704133 prefixEnd_2704133 := by exact prefixLift 2704133
  have htrace : WordTrace (prefixWord ++ tailWord_2704133) baseStart_2704133 baseEnd_2704133 := by
    simpa [prefixWord, tailWord_2704133, baseEnd_2704133] using wordTrace_append hprefix tailTrace_2704133
  have hstable : (prefixWord ++ tailWord_2704133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704133).length < 2 ^ (prefixWord ++ tailWord_2704133).sum := by decide
  have hdescent : baseEnd_2704133 < baseStart_2704133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704182 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2704182 : Nat := 118140960795 + 2704182 * 2 ^ 59
def prefixEnd_2704182 : Nat := 4983230072969 + 3 ^ 40 * 2704182 * 2
def baseEnd_2704182 : Nat := 925696762157762739459133

theorem tailTrace_2704182 : CollatzResearch.WordTrace tailWord_2704182 prefixEnd_2704182 925696762157762739459133 := by
  unfold tailWord_2704182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164351268076120397621675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65753080192811950907964533 6164351268076120397621675)
  ·
    refine ⟨9246526902114180596432513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6164351268076120397621675 9246526902114180596432513)
    ·
      refine ⟨6934895176585635447324385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9246526902114180596432513 6934895176585635447324385)
      ·
        refine ⟨5201171382439226585493289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6934895176585635447324385 5201171382439226585493289)
        ·
          refine ⟨3900878536829419939119967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5201171382439226585493289 3900878536829419939119967)
          ·
            refine ⟨5851317805244129908679951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900878536829419939119967 5851317805244129908679951)
            ·
              refine ⟨8776976707866194863019927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5851317805244129908679951 8776976707866194863019927)
              ·
                refine ⟨13165465061799292294529891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8776976707866194863019927 13165465061799292294529891)
                ·
                  refine ⟨19748197592698938441794837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13165465061799292294529891 19748197592698938441794837)
                  ·
                    refine ⟨925696762157762739459133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19748197592698938441794837 925696762157762739459133)
                    ·
                      rfl

theorem cell22_2704182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2704182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704182 prefixEnd_2704182 := by exact prefixLift 2704182
  have htrace : WordTrace (prefixWord ++ tailWord_2704182) baseStart_2704182 baseEnd_2704182 := by
    simpa [prefixWord, tailWord_2704182, baseEnd_2704182] using wordTrace_append hprefix tailTrace_2704182
  have hstable : (prefixWord ++ tailWord_2704182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704182).length < 2 ^ (prefixWord ++ tailWord_2704182).sum := by decide
  have hdescent : baseEnd_2704182 < baseStart_2704182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704223 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 2, 5]
def baseStart_2704223 : Nat := 118140960795 + 2704223 * 2 ^ 59
def prefixEnd_2704223 : Nat := 4983230072969 + 3 ^ 40 * 2704223 * 2
def baseEnd_2704223 : Nat := 925710797295652299184007

theorem tailTrace_2704223 : CollatzResearch.WordTrace tailWord_2704223 prefixEnd_2704223 925710797295652299184007 := by
  unfold tailWord_2704223
  simp only [CollatzResearch.WordTrace]
  refine ⟨98631115682069390364189323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65754077121379593576126215 98631115682069390364189323)
  ·
    refine ⟨147946673523104085546283985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98631115682069390364189323 147946673523104085546283985)
    ·
      refine ⟨110960005142328064159712989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147946673523104085546283985 110960005142328064159712989)
      ·
        refine ⟨41610001928373024059892371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110960005142328064159712989 41610001928373024059892371)
        ·
          refine ⟨62415002892559536089838557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41610001928373024059892371 62415002892559536089838557)
          ·
            refine ⟨23405626084709826033689459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62415002892559536089838557 23405626084709826033689459)
            ·
              refine ⟨35108439127064739050534189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23405626084709826033689459 35108439127064739050534189)
              ·
                refine ⟨13165664672649277143950321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35108439127064739050534189 13165664672649277143950321)
                ·
                  refine ⟨9874248504486957857962741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13165664672649277143950321 9874248504486957857962741)
                  ·
                    refine ⟨925710797295652299184007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9874248504486957857962741 925710797295652299184007)
                    ·
                      rfl

theorem cell22_2704223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_2704223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704223 prefixEnd_2704223 := by exact prefixLift 2704223
  have htrace : WordTrace (prefixWord ++ tailWord_2704223) baseStart_2704223 baseEnd_2704223 := by
    simpa [prefixWord, tailWord_2704223, baseEnd_2704223] using wordTrace_append hprefix tailTrace_2704223
  have hstable : (prefixWord ++ tailWord_2704223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704223).length < 2 ^ (prefixWord ++ tailWord_2704223).sum := by decide
  have hdescent : baseEnd_2704223 < baseStart_2704223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704246 : List Nat := [5, 1, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_2704246 : Nat := 118140960795 + 2704246 * 2 ^ 59
def prefixEnd_2704246 : Nat := 4983230072969 + 3 ^ 40 * 2704246 * 2
def baseEnd_2704246 : Nat := 925718670665687905858937

theorem tailTrace_2704246 : CollatzResearch.WordTrace tailWord_2704246 prefixEnd_2704246 925718670665687905858937 := by
  unfold tailWord_2704246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164497160061629080767287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65754636373990710194851061 6164497160061629080767287)
  ·
    refine ⟨9246745740092443621150931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6164497160061629080767287 9246745740092443621150931)
    ·
      refine ⟨13870118610138665431726397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9246745740092443621150931 13870118610138665431726397)
      ·
        refine ⟨5201294478801999536897399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13870118610138665431726397 5201294478801999536897399)
        ·
          refine ⟨7801941718202999305346099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5201294478801999536897399 7801941718202999305346099)
          ·
            refine ⟨11702912577304498958019149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7801941718202999305346099 11702912577304498958019149)
            ·
              refine ⟨4388592216489187109257181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11702912577304498958019149 4388592216489187109257181)
              ·
                refine ⟨1645722081183445165971443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4388592216489187109257181 1645722081183445165971443)
                ·
                  refine ⟨2468583121775167748957165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1645722081183445165971443 2468583121775167748957165)
                  ·
                    refine ⟨925718670665687905858937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468583121775167748957165 925718670665687905858937)
                    ·
                      rfl

theorem cell22_2704246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_2704246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704246 prefixEnd_2704246 := by exact prefixLift 2704246
  have htrace : WordTrace (prefixWord ++ tailWord_2704246) baseStart_2704246 baseEnd_2704246 := by
    simpa [prefixWord, tailWord_2704246, baseEnd_2704246] using wordTrace_append hprefix tailTrace_2704246
  have hstable : (prefixWord ++ tailWord_2704246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704246).length < 2 ^ (prefixWord ++ tailWord_2704246).sum := by decide
  have hdescent : baseEnd_2704246 < baseStart_2704246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704253 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 8]
def baseStart_2704253 : Nat := 118140960795 + 2704253 * 2 ^ 59
def prefixEnd_2704253 : Nat := 4983230072969 + 3 ^ 40 * 2704253 * 2
def baseEnd_2704253 : Nat := 308573688969580740311305

theorem tailTrace_2704253 : CollatzResearch.WordTrace tailWord_2704253 prefixEnd_2704253 308573688969580740311305 := by
  unfold tailWord_2704253
  simp only [CollatzResearch.WordTrace]
  refine ⟨98632209871960705487781413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65754806581307136991854275 98632209871960705487781413)
  ·
    refine ⟨18493539350992632278959015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98632209871960705487781413 18493539350992632278959015)
    ·
      refine ⟨27740309026488948418438523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18493539350992632278959015 27740309026488948418438523)
      ·
        refine ⟨41610463539733422627657785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27740309026488948418438523 41610463539733422627657785)
        ·
          refine ⟨31207847654800066970743339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41610463539733422627657785 31207847654800066970743339)
          ·
            refine ⟨46811771482200100456115009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31207847654800066970743339 46811771482200100456115009)
            ·
              refine ⟨35108828611650075342086257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46811771482200100456115009 35108828611650075342086257)
              ·
                refine ⟨26331621458737556506564693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35108828611650075342086257 26331621458737556506564693)
                ·
                  refine ⟨308573688969580740311305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26331621458737556506564693 308573688969580740311305)
                  ·
                    rfl

theorem cell22_2704253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_2704253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704253 prefixEnd_2704253 := by exact prefixLift 2704253
  have htrace : WordTrace (prefixWord ++ tailWord_2704253) baseStart_2704253 baseEnd_2704253 := by
    simpa [prefixWord, tailWord_2704253, baseEnd_2704253] using wordTrace_append hprefix tailTrace_2704253
  have hstable : (prefixWord ++ tailWord_2704253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704253).length < 2 ^ (prefixWord ++ tailWord_2704253).sum := by decide
  have hdescent : baseEnd_2704253 < baseStart_2704253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704255 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 1, 4]
def baseStart_2704255 : Nat := 118140960795 + 2704255 * 2 ^ 59
def prefixEnd_2704255 : Nat := 4983230072969 + 3 ^ 40 * 2704255 * 2
def baseEnd_2704255 : Nat := 925721751549614882383909

theorem tailTrace_2704255 : CollatzResearch.WordTrace tailWord_2704255 prefixEnd_2704255 925721751549614882383909 := by
  unfold tailWord_2704255
  simp only [CollatzResearch.WordTrace]
  refine ⟨98632282817953459829354219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65754855211968973219569479 98632282817953459829354219)
  ·
    refine ⟨147948424226930189744031329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98632282817953459829354219 147948424226930189744031329)
    ·
      refine ⟨110961318170197642308023497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147948424226930189744031329 110961318170197642308023497)
      ·
        refine ⟨83220988627648231731017623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110961318170197642308023497 83220988627648231731017623)
        ·
          refine ⟨124831482941472347596526435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83220988627648231731017623 124831482941472347596526435)
          ·
            refine ⟨187247224412208521394789653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124831482941472347596526435 187247224412208521394789653)
            ·
              refine ⟨8777213644322274440380765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187247224412208521394789653 8777213644322274440380765)
              ·
                refine ⟨3291455116620852915142787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8777213644322274440380765 3291455116620852915142787)
                ·
                  refine ⟨4937182674931279372714181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291455116620852915142787 4937182674931279372714181)
                  ·
                    refine ⟨925721751549614882383909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4937182674931279372714181 925721751549614882383909)
                    ·
                      rfl

theorem cell22_2704255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_2704255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704255 prefixEnd_2704255 := by exact prefixLift 2704255
  have htrace : WordTrace (prefixWord ++ tailWord_2704255) baseStart_2704255 baseEnd_2704255 := by
    simpa [prefixWord, tailWord_2704255, baseEnd_2704255] using wordTrace_append hprefix tailTrace_2704255
  have hstable : (prefixWord ++ tailWord_2704255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704255).length < 2 ^ (prefixWord ++ tailWord_2704255).sum := by decide
  have hdescent : baseEnd_2704255 < baseStart_2704255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704285 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_2704285 : Nat := 118140960795 + 2704285 * 2 ^ 59
def prefixEnd_2704285 : Nat := 4983230072969 + 3 ^ 40 * 2704285 * 2
def baseEnd_2704285 : Nat := 925732021162704804133817

theorem tailTrace_2704285 : CollatzResearch.WordTrace tailWord_2704285 prefixEnd_2704285 925732021162704804133817 := by
  unfold tailWord_2704285
  simp only [CollatzResearch.WordTrace]
  refine ⟨98633377007844774952946309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65755584671896516635297539 98633377007844774952946309)
  ·
    refine ⟨18493758188970895303677433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98633377007844774952946309 18493758188970895303677433)
    ·
      refine ⟨13870318641728171477758075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18493758188970895303677433 13870318641728171477758075)
      ·
        refine ⟨20805477962592257216637113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13870318641728171477758075 20805477962592257216637113)
        ·
          refine ⟨15604108471944192912477835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20805477962592257216637113 15604108471944192912477835)
          ·
            refine ⟨23406162707916289368716753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15604108471944192912477835 23406162707916289368716753)
            ·
              refine ⟨17554622030937217026537565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23406162707916289368716753 17554622030937217026537565)
              ·
                refine ⟨6582983261601456384951587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17554622030937217026537565 6582983261601456384951587)
                ·
                  refine ⟨9874474892402184577427381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6582983261601456384951587 9874474892402184577427381)
                  ·
                    refine ⟨925732021162704804133817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9874474892402184577427381 925732021162704804133817)
                    ·
                      rfl

theorem cell22_2704285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_2704285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704285 prefixEnd_2704285 := by exact prefixLift 2704285
  have htrace : WordTrace (prefixWord ++ tailWord_2704285) baseStart_2704285 baseEnd_2704285 := by
    simpa [prefixWord, tailWord_2704285, baseEnd_2704285] using wordTrace_append hprefix tailTrace_2704285
  have hstable : (prefixWord ++ tailWord_2704285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704285).length < 2 ^ (prefixWord ++ tailWord_2704285).sum := by decide
  have hdescent : baseEnd_2704285 < baseStart_2704285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704289 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 1, 4]
def baseStart_2704289 : Nat := 118140960795 + 2704289 * 2 ^ 59
def prefixEnd_2704289 : Nat := 4983230072969 + 3 ^ 40 * 2704289 * 2
def baseEnd_2704289 : Nat := 925733390444450127033805

theorem tailTrace_2704289 : CollatzResearch.WordTrace tailWord_2704289 prefixEnd_2704289 925733390444450127033805 := by
  unfold tailWord_2704289
  simp only [CollatzResearch.WordTrace]
  refine ⟨98633522899830283636091921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65755681933220189090727947 98633522899830283636091921)
  ·
    refine ⟨73975142174872712727068941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98633522899830283636091921 73975142174872712727068941)
    ·
      refine ⟨27740678315577267272650853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73975142174872712727068941 27740678315577267272650853)
      ·
        refine ⟨5201377184170737613622035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27740678315577267272650853 5201377184170737613622035)
        ·
          refine ⟨7802065776256106420433053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5201377184170737613622035 7802065776256106420433053)
          ·
            refine ⟨2925774666096039907662395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7802065776256106420433053 2925774666096039907662395)
            ·
              refine ⟨4388661999144059861493593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2925774666096039907662395 4388661999144059861493593)
              ·
                refine ⟨3291496499358044896120195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4388661999144059861493593 3291496499358044896120195)
                ·
                  refine ⟨4937244749037067344180293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291496499358044896120195 4937244749037067344180293)
                  ·
                    refine ⟨925733390444450127033805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4937244749037067344180293 925733390444450127033805)
                    ·
                      rfl

theorem cell22_2704289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_2704289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704289 prefixEnd_2704289 := by exact prefixLift 2704289
  have htrace : WordTrace (prefixWord ++ tailWord_2704289) baseStart_2704289 baseEnd_2704289 := by
    simpa [prefixWord, tailWord_2704289, baseEnd_2704289] using wordTrace_append hprefix tailTrace_2704289
  have hstable : (prefixWord ++ tailWord_2704289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704289).length < 2 ^ (prefixWord ++ tailWord_2704289).sum := by decide
  have hdescent : baseEnd_2704289 < baseStart_2704289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704394 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 5]
def baseStart_2704394 : Nat := 118140960795 + 2704394 * 2 ^ 59
def prefixEnd_2704394 : Nat := 4983230072969 + 3 ^ 40 * 2704394 * 2
def baseEnd_2704394 : Nat := 308589778030088284386161

theorem tailTrace_2704394 : CollatzResearch.WordTrace tailWord_2704394 prefixEnd_2704394 308589778030088284386161 := by
  unfold tailWord_2704394
  simp only [CollatzResearch.WordTrace]
  refine ⟨24659338141112471642166059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65758235042966591045776157 24659338141112471642166059)
  ·
    refine ⟨36989007211668707463249089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24659338141112471642166059 36989007211668707463249089)
    ·
      refine ⟨27741755408751530597436817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36989007211668707463249089 27741755408751530597436817)
      ·
        refine ⟨20806316556563647948077613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27741755408751530597436817 20806316556563647948077613)
        ·
          refine ⟨7802368708711367980529105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20806316556563647948077613 7802368708711367980529105)
          ·
            refine ⟨5851776531533525985396829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7802368708711367980529105 5851776531533525985396829)
            ·
              refine ⟨2194416199325072244523811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5851776531533525985396829 2194416199325072244523811)
              ·
                refine ⟨3291624298987608366785717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194416199325072244523811 3291624298987608366785717)
                ·
                  refine ⟨308589778030088284386161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3291624298987608366785717 308589778030088284386161)
                  ·
                    rfl

theorem cell22_2704394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_2704394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704394 prefixEnd_2704394 := by exact prefixLift 2704394
  have htrace : WordTrace (prefixWord ++ tailWord_2704394) baseStart_2704394 baseEnd_2704394 := by
    simpa [prefixWord, tailWord_2704394, baseEnd_2704394] using wordTrace_append hprefix tailTrace_2704394
  have hstable : (prefixWord ++ tailWord_2704394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704394).length < 2 ^ (prefixWord ++ tailWord_2704394).sum := by decide
  have hdescent : baseEnd_2704394 < baseStart_2704394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704465 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_2704465 : Nat := 118140960795 + 2704465 * 2 ^ 59
def prefixEnd_2704465 : Nat := 4983230072969 + 3 ^ 40 * 2704465 * 2
def baseEnd_2704465 : Nat := 925793638841244334633265

theorem tailTrace_2704465 : CollatzResearch.WordTrace tailWord_2704465 prefixEnd_2704465 925793638841244334633265 := by
  unfold tailWord_2704465
  simp only [CollatzResearch.WordTrace]
  refine ⟨98639942147192665694498849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65759961431461777129665899 98639942147192665694498849)
  ·
    refine ⟨73979956610394499270874137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98639942147192665694498849 73979956610394499270874137)
    ·
      refine ⟨55484967457795874453155603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73979956610394499270874137 55484967457795874453155603)
      ·
        refine ⟨83227451186693811679733405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55484967457795874453155603 83227451186693811679733405)
        ·
          refine ⟨31210294195010179379900027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83227451186693811679733405 31210294195010179379900027)
          ·
            refine ⟨46815441292515269069850041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31210294195010179379900027 46815441292515269069850041)
            ·
              refine ⟨35111580969386451802387531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46815441292515269069850041 35111580969386451802387531)
              ·
                refine ⟨52667371454079677703581297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35111580969386451802387531 52667371454079677703581297)
                ·
                  refine ⟨39500528590559758277685973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52667371454079677703581297 39500528590559758277685973)
                  ·
                    refine ⟨925793638841244334633265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39500528590559758277685973 925793638841244334633265)
                    ·
                      rfl

theorem cell22_2704465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_2704465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704465 prefixEnd_2704465 := by exact prefixLift 2704465
  have htrace : WordTrace (prefixWord ++ tailWord_2704465) baseStart_2704465 baseEnd_2704465 := by
    simpa [prefixWord, tailWord_2704465, baseEnd_2704465] using wordTrace_append hprefix tailTrace_2704465
  have hstable : (prefixWord ++ tailWord_2704465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704465).length < 2 ^ (prefixWord ++ tailWord_2704465).sum := by decide
  have hdescent : baseEnd_2704465 < baseStart_2704465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704488 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 2, 3]
def baseStart_2704488 : Nat := 118140960795 + 2704488 * 2 ^ 59
def prefixEnd_2704488 : Nat := 4983230072969 + 3 ^ 40 * 2704488 * 2
def baseEnd_2704488 : Nat := 925801512211279941308195

theorem tailTrace_2704488 : CollatzResearch.WordTrace tailWord_2704488 prefixEnd_2704488 925801512211279941308195 := by
  unfold tailWord_2704488
  simp only [CollatzResearch.WordTrace]
  refine ⟨49320390513054670311293059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65760520684072893748390745 49320390513054670311293059)
  ·
    refine ⟨73980585769582005466939589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49320390513054670311293059 73980585769582005466939589)
    ·
      refine ⟨13871359831796626025051173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73980585769582005466939589 13871359831796626025051173)
      ·
        refine ⟨2600879968461867379697095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13871359831796626025051173 2600879968461867379697095)
        ·
          refine ⟨3901319952692801069545643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600879968461867379697095 3901319952692801069545643)
          ·
            refine ⟨5851979929039201604318465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901319952692801069545643 5851979929039201604318465)
            ·
              refine ⟨4388984946779401203238849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5851979929039201604318465 4388984946779401203238849)
              ·
                refine ⟨3291738710084550902429137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4388984946779401203238849 3291738710084550902429137)
                ·
                  refine ⟨2468804032563413176821853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3291738710084550902429137 2468804032563413176821853)
                  ·
                    refine ⟨925801512211279941308195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468804032563413176821853 925801512211279941308195)
                    ·
                      rfl

theorem cell22_2704488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_2704488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704488 prefixEnd_2704488 := by exact prefixLift 2704488
  have htrace : WordTrace (prefixWord ++ tailWord_2704488) baseStart_2704488 baseEnd_2704488 := by
    simpa [prefixWord, tailWord_2704488, baseEnd_2704488] using wordTrace_append hprefix tailTrace_2704488
  have hstable : (prefixWord ++ tailWord_2704488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704488).length < 2 ^ (prefixWord ++ tailWord_2704488).sum := by decide
  have hdescent : baseEnd_2704488 < baseStart_2704488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704501 : List Nat := [1, 3, 4, 3, 1, 2, 1, 7]
def baseStart_2704501 : Nat := 118140960795 + 2704501 * 2 ^ 59
def prefixEnd_2704501 : Nat := 4983230072969 + 3 ^ 40 * 2704501 * 2
def baseEnd_2704501 : Nat := 102867329152994693414795

theorem tailTrace_2704501 : CollatzResearch.WordTrace tailWord_2704501 prefixEnd_2704501 102867329152994693414795 := by
  unfold tailWord_2704501
  simp only [CollatzResearch.WordTrace]
  refine ⟨98641255175062243842809357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65760836783374829228539571 98641255175062243842809357)
  ·
    refine ⟨36990470690648341441053509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98641255175062243842809357 36990470690648341441053509)
    ·
      refine ⟨6935713254496564020197533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36990470690648341441053509 6935713254496564020197533)
      ·
        refine ⟨2600892470436211507574075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6935713254496564020197533 2600892470436211507574075)
        ·
          refine ⟨3901338705654317261361113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600892470436211507574075 3901338705654317261361113)
          ·
            refine ⟨2926004029240737946020835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3901338705654317261361113 2926004029240737946020835)
            ·
              refine ⟨4389006043861106919031253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926004029240737946020835 4389006043861106919031253)
              ·
                refine ⟨102867329152994693414795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4389006043861106919031253 102867329152994693414795)
                ·
                  rfl

theorem cell22_2704501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 7].length) (baseStart_2704501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704501 prefixEnd_2704501 := by exact prefixLift 2704501
  have htrace : WordTrace (prefixWord ++ tailWord_2704501) baseStart_2704501 baseEnd_2704501 := by
    simpa [prefixWord, tailWord_2704501, baseEnd_2704501] using wordTrace_append hprefix tailTrace_2704501
  have hstable : (prefixWord ++ tailWord_2704501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704501).length < 2 ^ (prefixWord ++ tailWord_2704501).sum := by decide
  have hdescent : baseEnd_2704501 < baseStart_2704501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704512 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 5]
def baseStart_2704512 : Nat := 118140960795 + 2704512 * 2 ^ 59
def prefixEnd_2704512 : Nat := 4983230072969 + 3 ^ 40 * 2704512 * 2
def baseEnd_2704512 : Nat := 308603242633917292902707

theorem tailTrace_2704512 : CollatzResearch.WordTrace tailWord_2704512 prefixEnd_2704512 308603242633917292902707 := by
  unfold tailWord_2704512
  simp only [CollatzResearch.WordTrace]
  refine ⟨49320828189011196360729895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65761104252014928480973193 49320828189011196360729895)
  ·
    refine ⟨73981242283516794541094843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49320828189011196360729895 73981242283516794541094843)
    ·
      refine ⟨110971863425275191811642265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73981242283516794541094843 110971863425275191811642265)
      ·
        refine ⟨83228897568956393858731699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110971863425275191811642265 83228897568956393858731699)
        ·
          refine ⟨124843346353434590788097549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83228897568956393858731699 124843346353434590788097549)
          ·
            refine ⟨46816254882537971545536581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124843346353434590788097549 46816254882537971545536581)
            ·
              refine ⟨8778047790475869664788109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46816254882537971545536581 8778047790475869664788109)
              ·
                refine ⟨3291767921428451124295541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8778047790475869664788109 3291767921428451124295541)
                ·
                  refine ⟨308603242633917292902707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3291767921428451124295541 308603242633917292902707)
                  ·
                    rfl

theorem cell22_2704512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_2704512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704512 prefixEnd_2704512 := by exact prefixLift 2704512
  have htrace : WordTrace (prefixWord ++ tailWord_2704512) baseStart_2704512 baseEnd_2704512 := by
    simpa [prefixWord, tailWord_2704512, baseEnd_2704512] using wordTrace_append hprefix tailTrace_2704512
  have hstable : (prefixWord ++ tailWord_2704512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704512).length < 2 ^ (prefixWord ++ tailWord_2704512).sum := by decide
  have hdescent : baseEnd_2704512 < baseStart_2704512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704574 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_2704574 : Nat := 118140960795 + 2704574 * 2 ^ 59
def prefixEnd_2704574 : Nat := 4983230072969 + 3 ^ 40 * 2704574 * 2
def baseEnd_2704574 : Nat := 308610317256268127885977

theorem tailTrace_2704574 : CollatzResearch.WordTrace tailWord_2704574 prefixEnd_2704574 308610317256268127885977 := by
  unfold tailWord_2704574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12330489712974722163777097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65762611802531851540144517 12330489712974722163777097)
  ·
    refine ⟨9247867284731041622832823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12330489712974722163777097 9247867284731041622832823)
    ·
      refine ⟨13871800927096562434249235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9247867284731041622832823 13871800927096562434249235)
      ·
        refine ⟨20807701390644843651373853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13871800927096562434249235 20807701390644843651373853)
        ·
          refine ⟨7802888021491816369265195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20807701390644843651373853 7802888021491816369265195)
          ·
            refine ⟨11704332032237724553897793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7802888021491816369265195 11704332032237724553897793)
            ·
              refine ⟨8778249024178293415423345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11704332032237724553897793 8778249024178293415423345)
              ·
                refine ⟨6583686768133720061567509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8778249024178293415423345 6583686768133720061567509)
                ·
                  refine ⟨308610317256268127885977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6583686768133720061567509 308610317256268127885977)
                  ·
                    rfl

theorem cell22_2704574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_2704574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704574 prefixEnd_2704574 := by exact prefixLift 2704574
  have htrace : WordTrace (prefixWord ++ tailWord_2704574) baseStart_2704574 baseEnd_2704574 := by
    simpa [prefixWord, tailWord_2704574, baseEnd_2704574] using wordTrace_append hprefix tailTrace_2704574
  have hstable : (prefixWord ++ tailWord_2704574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704574).length < 2 ^ (prefixWord ++ tailWord_2704574).sum := by decide
  have hdescent : baseEnd_2704574 < baseStart_2704574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704576 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 1, 4]
def baseStart_2704576 : Nat := 118140960795 + 2704576 * 2 ^ 59
def prefixEnd_2704576 : Nat := 4983230072969 + 3 ^ 40 * 2704576 * 2
def baseEnd_2704576 : Nat := 925831636409677045107925

theorem tailTrace_2704576 : CollatzResearch.WordTrace tailWord_2704576 prefixEnd_2704576 925831636409677045107925 := by
  unfold tailWord_2704576
  simp only [CollatzResearch.WordTrace]
  refine ⟨49321995324895265825894791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65762660433193687767859721 49321995324895265825894791)
  ·
    refine ⟨73982992987342898738842187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49321995324895265825894791 73982992987342898738842187)
    ·
      refine ⟨110974489481014348108263281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73982992987342898738842187 110974489481014348108263281)
      ·
        refine ⟨83230867110760761081197461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110974489481014348108263281 83230867110760761081197461)
        ·
          refine ⟨3901446895816910675681131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83230867110760761081197461 3901446895816910675681131)
          ·
            refine ⟨5852170343725366013521697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901446895816910675681131 5852170343725366013521697)
            ·
              refine ⟨4389127757794024510141273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5852170343725366013521697 4389127757794024510141273)
              ·
                refine ⟨3291845818345518382605955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4389127757794024510141273 3291845818345518382605955)
                ·
                  refine ⟨4937768727518277573908933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291845818345518382605955 4937768727518277573908933)
                  ·
                    refine ⟨925831636409677045107925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4937768727518277573908933 925831636409677045107925)
                    ·
                      rfl

theorem cell22_2704576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_2704576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704576 prefixEnd_2704576 := by exact prefixLift 2704576
  have htrace : WordTrace (prefixWord ++ tailWord_2704576) baseStart_2704576 baseEnd_2704576 := by
    simpa [prefixWord, tailWord_2704576, baseEnd_2704576] using wordTrace_append hprefix tailTrace_2704576
  have hstable : (prefixWord ++ tailWord_2704576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704576).length < 2 ^ (prefixWord ++ tailWord_2704576).sum := by decide
  have hdescent : baseEnd_2704576 < baseStart_2704576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704634 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 5, 3]
def baseStart_2704634 : Nat := 118140960795 + 2704634 * 2 ^ 59
def prefixEnd_2704634 : Nat := 4983230072969 + 3 ^ 40 * 2704634 * 2
def baseEnd_2704634 : Nat := 925851490994984227157747

theorem tailTrace_2704634 : CollatzResearch.WordTrace tailWord_2704634 prefixEnd_2704634 925851490994984227157747 := by
  unfold tailWord_2704634
  simp only [CollatzResearch.WordTrace]
  refine ⟨24661526520895101889350239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65764070722386938371600637 24661526520895101889350239)
  ·
    refine ⟨36992289781342652834025359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24661526520895101889350239 36992289781342652834025359)
    ·
      refine ⟨55488434672013979251038039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36992289781342652834025359 55488434672013979251038039)
      ·
        refine ⟨83232652008020968876557059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55488434672013979251038039 83232652008020968876557059)
        ·
          refine ⟨124848978012031453314835589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83232652008020968876557059 124848978012031453314835589)
          ·
            refine ⟨23409183377255897496531673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124848978012031453314835589 23409183377255897496531673)
            ·
              refine ⟨17556887532941923122398755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23409183377255897496531673 17556887532941923122398755)
              ·
                refine ⟨26335331299412884683598133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17556887532941923122398755 26335331299412884683598133)
                ·
                  refine ⟨2468937309319957939087325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26335331299412884683598133 2468937309319957939087325)
                  ·
                    refine ⟨925851490994984227157747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468937309319957939087325 925851490994984227157747)
                    ·
                      rfl

theorem cell22_2704634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_2704634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704634 prefixEnd_2704634 := by exact prefixLift 2704634
  have htrace : WordTrace (prefixWord ++ tailWord_2704634) baseStart_2704634 baseEnd_2704634 := by
    simpa [prefixWord, tailWord_2704634, baseEnd_2704634] using wordTrace_append hprefix tailTrace_2704634
  have hstable : (prefixWord ++ tailWord_2704634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704634).length < 2 ^ (prefixWord ++ tailWord_2704634).sum := by decide
  have hdescent : baseEnd_2704634 < baseStart_2704634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704664 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 5]
def baseStart_2704664 : Nat := 118140960795 + 2704664 * 2 ^ 59
def prefixEnd_2704664 : Nat := 4983230072969 + 3 ^ 40 * 2704664 * 2
def baseEnd_2704664 : Nat := 308620586869358049635885

theorem tailTrace_2704664 : CollatzResearch.WordTrace tailWord_2704664 prefixEnd_2704664 308620586869358049635885 := by
  unfold tailWord_2704664
  simp only [CollatzResearch.WordTrace]
  refine ⟨49323600136735861340496523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65764800182314481787328697 49323600136735861340496523)
  ·
    refine ⟨73985400205103792010744785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49323600136735861340496523 73985400205103792010744785)
    ·
      refine ⟨55489050153827844008058589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73985400205103792010744785 55489050153827844008058589)
      ·
        refine ⟨20808393807685441503021971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55489050153827844008058589 20808393807685441503021971)
        ·
          refine ⟨31212590711528162254532957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20808393807685441503021971 31212590711528162254532957)
          ·
            refine ⟨11704721516823060845449859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31212590711528162254532957 11704721516823060845449859)
            ·
              refine ⟨17557082275234591268174789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11704721516823060845449859 17557082275234591268174789)
              ·
                refine ⟨3291952926606485862782773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17557082275234591268174789 3291952926606485862782773)
                ·
                  refine ⟨308620586869358049635885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3291952926606485862782773 308620586869358049635885)
                  ·
                    rfl

theorem cell22_2704664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_2704664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704664 prefixEnd_2704664 := by exact prefixLift 2704664
  have htrace : WordTrace (prefixWord ++ tailWord_2704664) baseStart_2704664 baseEnd_2704664 := by
    simpa [prefixWord, tailWord_2704664, baseEnd_2704664] using wordTrace_append hprefix tailTrace_2704664
  have hstable : (prefixWord ++ tailWord_2704664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704664).length < 2 ^ (prefixWord ++ tailWord_2704664).sum := by decide
  have hdescent : baseEnd_2704664 < baseStart_2704664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704670 : List Nat := [4, 3, 2, 1, 3, 1, 1, 7]
def baseStart_2704670 : Nat := 118140960795 + 2704670 * 2 ^ 59
def prefixEnd_2704670 : Nat := 4983230072969 + 3 ^ 40 * 2704670 * 2
def baseEnd_2704670 : Nat := 102873757170076903695293

theorem tailTrace_2704670 : CollatzResearch.WordTrace tailWord_2704670 prefixEnd_2704670 102873757170076903695293 := by
  unfold tailWord_2704670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12330927388931248213213933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65764946074299990470474309 12330927388931248213213933)
  ·
    refine ⟨4624097770849218079955225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12330927388931248213213933 4624097770849218079955225)
    ·
      refine ⟨3468073328136913559966419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4624097770849218079955225 3468073328136913559966419)
      ·
        refine ⟨5202109992205370339949629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3468073328136913559966419 5202109992205370339949629)
        ·
          refine ⟨1950791247077013877481111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5202109992205370339949629 1950791247077013877481111)
          ·
            refine ⟨2926186870615520816221667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950791247077013877481111 2926186870615520816221667)
            ·
              refine ⟨4389280305923281224332501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926186870615520816221667 4389280305923281224332501)
              ·
                refine ⟨102873757170076903695293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4389280305923281224332501 102873757170076903695293)
                ·
                  rfl

theorem cell22_2704670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_2704670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704670 prefixEnd_2704670 := by exact prefixLift 2704670
  have htrace : WordTrace (prefixWord ++ tailWord_2704670) baseStart_2704670 baseEnd_2704670 := by
    simpa [prefixWord, tailWord_2704670, baseEnd_2704670] using wordTrace_append hprefix tailTrace_2704670
  have hstable : (prefixWord ++ tailWord_2704670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704670).length < 2 ^ (prefixWord ++ tailWord_2704670).sum := by decide
  have hdescent : baseEnd_2704670 < baseStart_2704670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704711 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 1, 4]
def baseStart_2704711 : Nat := 118140960795 + 2704711 * 2 ^ 59
def prefixEnd_2704711 : Nat := 4983230072969 + 3 ^ 40 * 2704711 * 2
def baseEnd_2704711 : Nat := 925877849668581692982511

theorem tailTrace_2704711 : CollatzResearch.WordTrace tailWord_2704711 prefixEnd_2704711 925877849668581692982511 := by
  unfold tailWord_2704711
  simp only [CollatzResearch.WordTrace]
  refine ⟨98648914504301449707953987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65765943002867633138635991 98648914504301449707953987)
  ·
    refine ⟨147973371756452174561930981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98648914504301449707953987 147973371756452174561930981)
    ·
      refine ⟨27745007204334782730362059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 147973371756452174561930981 27745007204334782730362059)
      ·
        refine ⟨41617510806502174095543089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27745007204334782730362059 41617510806502174095543089)
        ·
          refine ⟨31213133104876630571657317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41617510806502174095543089 31213133104876630571657317)
          ·
            refine ⟨5852462457164368232185747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31213133104876630571657317 5852462457164368232185747)
            ·
              refine ⟨8778693685746552348278621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5852462457164368232185747 8778693685746552348278621)
              ·
                refine ⟨3292010132154957130604483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8778693685746552348278621 3292010132154957130604483)
                ·
                  refine ⟨4938015198232435695906725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292010132154957130604483 4938015198232435695906725)
                  ·
                    refine ⟨925877849668581692982511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4938015198232435695906725 925877849668581692982511)
                    ·
                      rfl

theorem cell22_2704711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_2704711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704711 prefixEnd_2704711 := by exact prefixLift 2704711
  have htrace : WordTrace (prefixWord ++ tailWord_2704711) baseStart_2704711 baseEnd_2704711 := by
    simpa [prefixWord, tailWord_2704711, baseEnd_2704711] using wordTrace_append hprefix tailTrace_2704711
  have hstable : (prefixWord ++ tailWord_2704711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704711).length < 2 ^ (prefixWord ++ tailWord_2704711).sum := by decide
  have hdescent : baseEnd_2704711 < baseStart_2704711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704739 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 1, 6]
def baseStart_2704739 : Nat := 118140960795 + 2704739 * 2 ^ 59
def prefixEnd_2704739 : Nat := 4983230072969 + 3 ^ 40 * 2704739 * 2
def baseEnd_2704739 : Nat := 925887434640798953282425

theorem tailTrace_2704739 : CollatzResearch.WordTrace tailWord_2704739 prefixEnd_2704739 925887434640798953282425 := by
  unfold tailWord_2704739
  simp only [CollatzResearch.WordTrace]
  refine ⟨98649935748200010489973271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65766623832133340326648847 98649935748200010489973271)
  ·
    refine ⟨147974903622300015734959907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98649935748200010489973271 147974903622300015734959907)
    ·
      refine ⟨221962355433450023602439861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147974903622300015734959907 221962355433450023602439861)
      ·
        refine ⟨20808970821885939712728737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 221962355433450023602439861 20808970821885939712728737)
        ·
          refine ⟨15606728116414454784546553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20808970821885939712728737 15606728116414454784546553)
          ·
            refine ⟨11705046087310841088409915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15606728116414454784546553 11705046087310841088409915)
            ·
              refine ⟨17557569130966261632614873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11705046087310841088409915 17557569130966261632614873)
              ·
                refine ⟨13168176848224696224461155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17557569130966261632614873 13168176848224696224461155)
                ·
                  refine ⟨19752265272337044336691733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13168176848224696224461155 19752265272337044336691733)
                  ·
                    refine ⟨925887434640798953282425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19752265272337044336691733 925887434640798953282425)
                    ·
                      rfl

theorem cell22_2704739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 6].length) (baseStart_2704739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704739 prefixEnd_2704739 := by exact prefixLift 2704739
  have htrace : WordTrace (prefixWord ++ tailWord_2704739) baseStart_2704739 baseEnd_2704739 := by
    simpa [prefixWord, tailWord_2704739, baseEnd_2704739] using wordTrace_append hprefix tailTrace_2704739
  have hstable : (prefixWord ++ tailWord_2704739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704739).length < 2 ^ (prefixWord ++ tailWord_2704739).sum := by decide
  have hdescent : baseEnd_2704739 < baseStart_2704739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704754 : List Nat := [3, 2, 1, 2, 1, 2, 3, 8]
def baseStart_2704754 : Nat := 118140960795 + 2704754 * 2 ^ 59
def prefixEnd_2704754 : Nat := 4983230072969 + 3 ^ 40 * 2704754 * 2
def baseEnd_2704754 : Nat := 102876952160815990461931

theorem tailTrace_2704754 : CollatzResearch.WordTrace tailWord_2704754 prefixEnd_2704754 102876952160815990461931 := by
  unfold tailWord_2704754
  simp only [CollatzResearch.WordTrace]
  refine ⟨24662620710786417012942329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65766988562097112034512877 24662620710786417012942329)
  ·
    refine ⟨18496965533089812759706747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24662620710786417012942329 18496965533089812759706747)
    ·
      refine ⟨27745448299634719139560121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18496965533089812759706747 27745448299634719139560121)
      ·
        refine ⟨20809086224726039354670091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27745448299634719139560121 20809086224726039354670091)
        ·
          refine ⟨31213629337089059032005137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20809086224726039354670091 31213629337089059032005137)
          ·
            refine ⟨23410222002816794274003853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31213629337089059032005137 23410222002816794274003853)
            ·
              refine ⟨8778833251056297852751445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23410222002816794274003853 8778833251056297852751445)
              ·
                refine ⟨102876952160815990461931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8778833251056297852751445 102876952160815990461931)
                ·
                  rfl

theorem cell22_2704754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_2704754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704754 prefixEnd_2704754 := by exact prefixLift 2704754
  have htrace : WordTrace (prefixWord ++ tailWord_2704754) baseStart_2704754 baseEnd_2704754 := by
    simpa [prefixWord, tailWord_2704754, baseEnd_2704754] using wordTrace_append hprefix tailTrace_2704754
  have hstable : (prefixWord ++ tailWord_2704754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704754).length < 2 ^ (prefixWord ++ tailWord_2704754).sum := by decide
  have hdescent : baseEnd_2704754 < baseStart_2704754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704792 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 2, 3]
def baseStart_2704792 : Nat := 118140960795 + 2704792 * 2 ^ 59
def prefixEnd_2704792 : Nat := 4983230072969 + 3 ^ 40 * 2704792 * 2
def baseEnd_2704792 : Nat := 925905577623924481707263

theorem tailTrace_2704792 : CollatzResearch.WordTrace tailWord_2704792 prefixEnd_2704792 925905577623924481707263 := by
  unfold tailWord_2704792
  simp only [CollatzResearch.WordTrace]
  refine ⟨49325934408504000270826315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65767912544672000361101753 49325934408504000270826315)
  ·
    refine ⟨73988901612756000406239473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49325934408504000270826315 73988901612756000406239473)
    ·
      refine ⟨55491676209567000304679605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73988901612756000406239473 55491676209567000304679605)
      ·
        refine ⟨5202344644646906278563713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55491676209567000304679605 5202344644646906278563713)
        ·
          refine ⟨3901758483485179708922785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5202344644646906278563713 3901758483485179708922785)
          ·
            refine ⟨2926318862613884781692089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3901758483485179708922785 2926318862613884781692089)
            ·
              refine ⟨2194739146960413586269067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926318862613884781692089 2194739146960413586269067)
              ·
                refine ⟨3292108720440620379403601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194739146960413586269067 3292108720440620379403601)
                ·
                  refine ⟨2469081540330465284552701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3292108720440620379403601 2469081540330465284552701)
                  ·
                    refine ⟨925905577623924481707263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2469081540330465284552701 925905577623924481707263)
                    ·
                      rfl

theorem cell22_2704792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 2, 3].length) (baseStart_2704792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704792 prefixEnd_2704792 := by exact prefixLift 2704792
  have htrace : WordTrace (prefixWord ++ tailWord_2704792) baseStart_2704792 baseEnd_2704792 := by
    simpa [prefixWord, tailWord_2704792, baseEnd_2704792] using wordTrace_append hprefix tailTrace_2704792
  have hstable : (prefixWord ++ tailWord_2704792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704792).length < 2 ^ (prefixWord ++ tailWord_2704792).sum := by decide
  have hdescent : baseEnd_2704792 < baseStart_2704792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704846 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_2704846 : Nat := 118140960795 + 2704846 * 2 ^ 59
def prefixEnd_2704846 : Nat := 4983230072969 + 3 ^ 40 * 2704846 * 2
def baseEnd_2704846 : Nat := 925924062927486340857097

theorem tailTrace_2704846 : CollatzResearch.WordTrace tailWord_2704846 prefixEnd_2704846 925924062927486340857097 := by
  unfold tailWord_2704846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12331729794851545970514799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65769225572541578509412261 12331729794851545970514799)
  ·
    refine ⟨18497594692277318955772199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12331729794851545970514799 18497594692277318955772199)
    ·
      refine ⟨27746392038415978433658299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18497594692277318955772199 27746392038415978433658299)
      ·
        refine ⟨41619588057623967650487449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27746392038415978433658299 41619588057623967650487449)
        ·
          refine ⟨31214691043217975737865587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41619588057623967650487449 31214691043217975737865587)
          ·
            refine ⟨46822036564826963606798381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31214691043217975737865587 46822036564826963606798381)
            ·
              refine ⟨17558263711810111352549393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46822036564826963606798381 17558263711810111352549393)
              ·
                refine ⟨13168697783857583514412045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17558263711810111352549393 13168697783857583514412045)
                ·
                  refine ⟨4938261668946593817904517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13168697783857583514412045 4938261668946593817904517)
                  ·
                    refine ⟨925924062927486340857097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4938261668946593817904517 925924062927486340857097)
                    ·
                      rfl

theorem cell22_2704846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_2704846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704846 prefixEnd_2704846 := by exact prefixLift 2704846
  have htrace : WordTrace (prefixWord ++ tailWord_2704846) baseStart_2704846 baseEnd_2704846 := by
    simpa [prefixWord, tailWord_2704846, baseEnd_2704846] using wordTrace_append hprefix tailTrace_2704846
  have hstable : (prefixWord ++ tailWord_2704846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704846).length < 2 ^ (prefixWord ++ tailWord_2704846).sum := by decide
  have hdescent : baseEnd_2704846 < baseStart_2704846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704861 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 8]
def baseStart_2704861 : Nat := 118140960795 + 2704861 * 2 ^ 59
def prefixEnd_2704861 : Nat := 4983230072969 + 3 ^ 40 * 2704861 * 2
def baseEnd_2704861 : Nat := 308643065911343767244017

theorem tailTrace_2704861 : CollatzResearch.WordTrace tailWord_2704861 prefixEnd_2704861 308643065911343767244017 := by
  unfold tailWord_2704861
  simp only [CollatzResearch.WordTrace]
  refine ⟨98654385453758025325914437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65769590302505350217276291 98654385453758025325914437)
  ·
    refine ⟨18497697272579629748608957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98654385453758025325914437 18497697272579629748608957)
    ·
      refine ⟨6936636477217361155728359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18497697272579629748608957 6936636477217361155728359)
      ·
        refine ⟨10404954715826041733592539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6936636477217361155728359 10404954715826041733592539)
        ·
          refine ⟨15607432073739062600388809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10404954715826041733592539 15607432073739062600388809)
          ·
            refine ⟨11705574055304296950291607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15607432073739062600388809 11705574055304296950291607)
            ·
              refine ⟨17558361082956445425437411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11705574055304296950291607 17558361082956445425437411)
              ·
                refine ⟨26337541624434668138156117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17558361082956445425437411 26337541624434668138156117)
                ·
                  refine ⟨308643065911343767244017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26337541624434668138156117 308643065911343767244017)
                  ·
                    rfl

theorem cell22_2704861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_2704861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704861 prefixEnd_2704861 := by exact prefixLift 2704861
  have htrace : WordTrace (prefixWord ++ tailWord_2704861) baseStart_2704861 baseEnd_2704861 := by
    simpa [prefixWord, tailWord_2704861, baseEnd_2704861] using wordTrace_append hprefix tailTrace_2704861
  have hstable : (prefixWord ++ tailWord_2704861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704861).length < 2 ^ (prefixWord ++ tailWord_2704861).sum := by decide
  have hdescent : baseEnd_2704861 < baseStart_2704861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704880 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 1, 4]
def baseStart_2704880 : Nat := 118140960795 + 2704880 * 2 ^ 59
def prefixEnd_2704880 : Nat := 4983230072969 + 3 ^ 40 * 2704880 * 2
def baseEnd_2704880 : Nat := 925935701822321585506993

theorem tailTrace_2704880 : CollatzResearch.WordTrace tailWord_2704880 prefixEnd_2704880 925935701822321585506993 := by
  unfold tailWord_2704880
  simp only [CollatzResearch.WordTrace]
  refine ⟨49327539220344595785428047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65770052293792794380570729 49327539220344595785428047)
  ·
    refine ⟨73991308830516893678142071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49327539220344595785428047 73991308830516893678142071)
    ·
      refine ⟨110986963245775340517213107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73991308830516893678142071 110986963245775340517213107)
      ·
        refine ⟨166480444868663010775819661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110986963245775340517213107 166480444868663010775819661)
        ·
          refine ⟨62430166825748629040932373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166480444868663010775819661 62430166825748629040932373)
          ·
            refine ⟨2926414069956966986293705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62430166825748629040932373 2926414069956966986293705)
            ·
              refine ⟨2194810552467725239720279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926414069956966986293705 2194810552467725239720279)
              ·
                refine ⟨3292215828701587859580419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194810552467725239720279 3292215828701587859580419)
                ·
                  refine ⟨4938323743052381789370629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292215828701587859580419 4938323743052381789370629)
                  ·
                    refine ⟨925935701822321585506993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4938323743052381789370629 925935701822321585506993)
                    ·
                      rfl

theorem cell22_2704880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 1, 4].length) (baseStart_2704880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704880 prefixEnd_2704880 := by exact prefixLift 2704880
  have htrace : WordTrace (prefixWord ++ tailWord_2704880) baseStart_2704880 baseEnd_2704880 := by
    simpa [prefixWord, tailWord_2704880, baseEnd_2704880] using wordTrace_append hprefix tailTrace_2704880
  have hstable : (prefixWord ++ tailWord_2704880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704880).length < 2 ^ (prefixWord ++ tailWord_2704880).sum := by decide
  have hdescent : baseEnd_2704880 < baseStart_2704880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704893 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_2704893 : Nat := 118140960795 + 2704893 * 2 ^ 59
def prefixEnd_2704893 : Nat := 4983230072969 + 3 ^ 40 * 2704893 * 2
def baseEnd_2704893 : Nat := 925940151987993884931953

theorem tailTrace_2704893 : CollatzResearch.WordTrace tailWord_2704893 prefixEnd_2704893 925940151987993884931953 := by
  unfold tailWord_2704893
  simp only [CollatzResearch.WordTrace]
  refine ⟨98655552589642094791079333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65770368393094729860719555 98655552589642094791079333)
  ·
    refine ⟨18497916110557892773327375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98655552589642094791079333 18497916110557892773327375)
    ·
      refine ⟨27746874165836839159991063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18497916110557892773327375 27746874165836839159991063)
      ·
        refine ⟨41620311248755258739986595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27746874165836839159991063 41620311248755258739986595)
        ·
          refine ⟨62430466873132888109979893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41620311248755258739986595 62430466873132888109979893)
          ·
            refine ⟨5852856269356208260310615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62430466873132888109979893 5852856269356208260310615)
            ·
              refine ⟨8779284404034312390465923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5852856269356208260310615 8779284404034312390465923)
              ·
                refine ⟨13168926606051468585698885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8779284404034312390465923 13168926606051468585698885)
                ·
                  refine ⟨2469173738634650359818541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13168926606051468585698885 2469173738634650359818541)
                  ·
                    refine ⟨925940151987993884931953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2469173738634650359818541 925940151987993884931953)
                    ·
                      rfl

theorem cell22_2704893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_2704893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704893 prefixEnd_2704893 := by exact prefixLift 2704893
  have htrace : WordTrace (prefixWord ++ tailWord_2704893) baseStart_2704893 baseEnd_2704893 := by
    simpa [prefixWord, tailWord_2704893, baseEnd_2704893] using wordTrace_append hprefix tailTrace_2704893
  have hstable : (prefixWord ++ tailWord_2704893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704893).length < 2 ^ (prefixWord ++ tailWord_2704893).sum := by decide
  have hdescent : baseEnd_2704893 < baseStart_2704893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704910 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_2704910 : Nat := 118140960795 + 2704910 * 2 ^ 59
def prefixEnd_2704910 : Nat := 4983230072969 + 3 ^ 40 * 2704910 * 2
def baseEnd_2704910 : Nat := 925945971435411507256901

theorem tailTrace_2704910 : CollatzResearch.WordTrace tailWord_2704910 prefixEnd_2704910 925945971435411507256901 := by
  unfold tailWord_2704910
  simp only [CollatzResearch.WordTrace]
  refine ⟨12332021578822563336806023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65770781753720337796298789 12332021578822563336806023)
  ·
    refine ⟨18498032368233845005209035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12332021578822563336806023 18498032368233845005209035)
    ·
      refine ⟨27747048552350767507813553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18498032368233845005209035 27747048552350767507813553)
      ·
        refine ⟨20810286414263075630860165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27747048552350767507813553 20810286414263075630860165)
        ·
          refine ⟨3901928702674326680786281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20810286414263075630860165 3901928702674326680786281)
          ·
            refine ⟨2926446527005745010589711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3901928702674326680786281 2926446527005745010589711)
            ·
              refine ⟨4389669790508617515884567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926446527005745010589711 4389669790508617515884567)
              ·
                refine ⟨6584504685762926273826851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4389669790508617515884567 6584504685762926273826851)
                ·
                  refine ⟨9876757028644389410740277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6584504685762926273826851 9876757028644389410740277)
                  ·
                    refine ⟨925945971435411507256901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9876757028644389410740277 925945971435411507256901)
                    ·
                      rfl

theorem cell22_2704910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_2704910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704910 prefixEnd_2704910 := by exact prefixLift 2704910
  have htrace : WordTrace (prefixWord ++ tailWord_2704910) baseStart_2704910 baseEnd_2704910 := by
    simpa [prefixWord, tailWord_2704910, baseEnd_2704910] using wordTrace_append hprefix tailTrace_2704910
  have hstable : (prefixWord ++ tailWord_2704910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704910).length < 2 ^ (prefixWord ++ tailWord_2704910).sum := by decide
  have hdescent : baseEnd_2704910 < baseStart_2704910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704951 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 7]
def baseStart_2704951 : Nat := 118140960795 + 2704951 * 2 ^ 59
def prefixEnd_2704951 : Nat := 4983230072969 + 3 ^ 40 * 2704951 * 2
def baseEnd_2704951 : Nat := 308653335524433688993925

theorem tailTrace_2704951 : CollatzResearch.WordTrace tailWord_2704951 prefixEnd_2704951 308653335524433688993925 := by
  unfold tailWord_2704951
  simp only [CollatzResearch.WordTrace]
  refine ⟨98657668023431970696690707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65771778682287980464460471 98657668023431970696690707)
  ·
    refine ⟨147986502035147956045036061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98657668023431970696690707 147986502035147956045036061)
    ·
      refine ⟨55494938263180483516888523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147986502035147956045036061 55494938263180483516888523)
      ·
        refine ⟨83242407394770725275332785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55494938263180483516888523 83242407394770725275332785)
        ·
          refine ⟨62431805546078043956499589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83242407394770725275332785 62431805546078043956499589)
          ·
            refine ⟨11705963539889633241843673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62431805546078043956499589 11705963539889633241843673)
            ·
              refine ⟨8779472654917224931382755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11705963539889633241843673 8779472654917224931382755)
              ·
                refine ⟨13169208982375837397074133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8779472654917224931382755 13169208982375837397074133)
                ·
                  refine ⟨308653335524433688993925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13169208982375837397074133 308653335524433688993925)
                  ·
                    rfl

theorem cell22_2704951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 7].length) (baseStart_2704951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2704951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2704951 prefixEnd_2704951 := by exact prefixLift 2704951
  have htrace : WordTrace (prefixWord ++ tailWord_2704951) baseStart_2704951 baseEnd_2704951 := by
    simpa [prefixWord, tailWord_2704951, baseEnd_2704951] using wordTrace_append hprefix tailTrace_2704951
  have hstable : (prefixWord ++ tailWord_2704951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704951).length < 2 ^ (prefixWord ++ tailWord_2704951).sum := by decide
  have hdescent : baseEnd_2704951 < baseStart_2704951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705006 : List Nat := [4, 1, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_2705006 : Nat := 118140960795 + 2705006 * 2 ^ 59
def prefixEnd_2705006 : Nat := 4983230072969 + 3 ^ 40 * 2705006 * 2
def baseEnd_2705006 : Nat := 925978834197299256856607

theorem tailTrace_2705006 : CollatzResearch.WordTrace tailWord_2705006 prefixEnd_2705006 925978834197299256856607 := by
  unfold tailWord_2705006
  simp only [CollatzResearch.WordTrace]
  refine ⟨12332459254779089386242859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65773116025488476726628581 12332459254779089386242859)
  ·
    refine ⟨18498688882168634079364289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12332459254779089386242859 18498688882168634079364289)
    ·
      refine ⟨13874016661626475559523217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18498688882168634079364289 13874016661626475559523217)
      ·
        refine ⟨10405512496219856669642413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13874016661626475559523217 10405512496219856669642413)
        ·
          refine ⟨3902067186082446251115905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10405512496219856669642413 3902067186082446251115905)
          ·
            refine ⟨2926550389561834688336929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3902067186082446251115905 2926550389561834688336929)
            ·
              refine ⟨2194912792171376016252697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926550389561834688336929 2194912792171376016252697)
              ·
                refine ⟨1646184594128532012189523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2194912792171376016252697 1646184594128532012189523)
                ·
                  refine ⟨2469276891192798018284285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646184594128532012189523 2469276891192798018284285)
                  ·
                    refine ⟨925978834197299256856607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2469276891192798018284285 925978834197299256856607)
                    ·
                      rfl

theorem cell22_2705006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_2705006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705006 prefixEnd_2705006 := by exact prefixLift 2705006
  have htrace : WordTrace (prefixWord ++ tailWord_2705006) baseStart_2705006 baseEnd_2705006 := by
    simpa [prefixWord, tailWord_2705006, baseEnd_2705006] using wordTrace_append hprefix tailTrace_2705006
  have hstable : (prefixWord ++ tailWord_2705006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705006).length < 2 ^ (prefixWord ++ tailWord_2705006).sum := by decide
  have hdescent : baseEnd_2705006 < baseStart_2705006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705064 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 6]
def baseStart_2705064 : Nat := 118140960795 + 2705064 * 2 ^ 59
def prefixEnd_2705064 : Nat := 4983230072969 + 3 ^ 40 * 2705064 * 2
def baseEnd_2705064 : Nat := 308666229594202146302143

theorem tailTrace_2705064 : CollatzResearch.WordTrace tailWord_2705064 prefixEnd_2705064 308666229594202146302143 := by
  unfold tailWord_2705064
  simp only [CollatzResearch.WordTrace]
  refine ⟨49330894736011295497777123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65774526314681727330369497 49330894736011295497777123)
  ·
    refine ⟨73996342104016943246665685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49330894736011295497777123 73996342104016943246665685)
    ·
      refine ⟨1734289268062897107343727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 73996342104016943246665685 1734289268062897107343727)
      ·
        refine ⟨2601433902094345661015591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734289268062897107343727 2601433902094345661015591)
        ·
          refine ⟨3902150853141518491523387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601433902094345661015591 3902150853141518491523387)
          ·
            refine ⟨5853226279712277737285081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902150853141518491523387 5853226279712277737285081)
            ·
              refine ⟨4389919709784208302963811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5853226279712277737285081 4389919709784208302963811)
              ·
                refine ⟨6584879564676312454445717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4389919709784208302963811 6584879564676312454445717)
                ·
                  refine ⟨308666229594202146302143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6584879564676312454445717 308666229594202146302143)
                  ·
                    rfl

theorem cell22_2705064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 6].length) (baseStart_2705064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705064 prefixEnd_2705064 := by exact prefixLift 2705064
  have htrace : WordTrace (prefixWord ++ tailWord_2705064) baseStart_2705064 baseEnd_2705064 := by
    simpa [prefixWord, tailWord_2705064, baseEnd_2705064] using wordTrace_append hprefix tailTrace_2705064
  have hstable : (prefixWord ++ tailWord_2705064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705064).length < 2 ^ (prefixWord ++ tailWord_2705064).sum := by decide
  have hdescent : baseEnd_2705064 < baseStart_2705064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705124 : List Nat := [2, 3, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_2705124 : Nat := 118140960795 + 2705124 * 2 ^ 59
def prefixEnd_2705124 : Nat := 4983230072969 + 3 ^ 40 * 2705124 * 2
def baseEnd_2705124 : Nat := 926019228008786282406245

theorem tailTrace_2705124 : CollatzResearch.WordTrace tailWord_2705124 prefixEnd_2705124 926019228008786282406245 := by
  unfold tailWord_2705124
  simp only [CollatzResearch.WordTrace]
  refine ⟨49331988925902610621369213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65775985234536814161825617 49331988925902610621369213)
  ·
    refine ⟨18499495847213478983013455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49331988925902610621369213 18499495847213478983013455)
    ·
      refine ⟨27749243770820218474520183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18499495847213478983013455 27749243770820218474520183)
      ·
        refine ⟨41623865656230327711780275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27749243770820218474520183 41623865656230327711780275)
        ·
          refine ⟨62435798484345491567670413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41623865656230327711780275 62435798484345491567670413)
          ·
            refine ⟨23413424431629559337876405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62435798484345491567670413 23413424431629559337876405)
            ·
              refine ⟨2195008540465271187925913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23413424431629559337876405 2195008540465271187925913)
              ·
                refine ⟨1646256405348953390944435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2195008540465271187925913 1646256405348953390944435)
                ·
                  refine ⟨2469384608023430086416653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646256405348953390944435 2469384608023430086416653)
                  ·
                    refine ⟨926019228008786282406245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2469384608023430086416653 926019228008786282406245)
                    ·
                      rfl

theorem cell22_2705124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_2705124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705124 prefixEnd_2705124 := by exact prefixLift 2705124
  have htrace : WordTrace (prefixWord ++ tailWord_2705124) baseStart_2705124 baseEnd_2705124 := by
    simpa [prefixWord, tailWord_2705124, baseEnd_2705124] using wordTrace_append hprefix tailTrace_2705124
  have hstable : (prefixWord ++ tailWord_2705124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705124).length < 2 ^ (prefixWord ++ tailWord_2705124).sum := by decide
  have hdescent : baseEnd_2705124 < baseStart_2705124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705137 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 5]
def baseStart_2705137 : Nat := 118140960795 + 2705137 * 2 ^ 59
def prefixEnd_2705137 : Nat := 4983230072969 + 3 ^ 40 * 2705137 * 2
def baseEnd_2705137 : Nat := 308674559391486193943735

theorem tailTrace_2705137 : CollatzResearch.WordTrace tailWord_2705137 prefixEnd_2705137 308674559391486193943735 := by
  unfold tailWord_2705137
  simp only [CollatzResearch.WordTrace]
  refine ⟨98664452000758124462961665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65776301333838749641974443 98664452000758124462961665)
  ·
    refine ⟨73998339000568593347221249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98664452000758124462961665 73998339000568593347221249)
    ·
      refine ⟨55498754250426445010415937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73998339000568593347221249 55498754250426445010415937)
      ·
        refine ⟨41624065687819833757811953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55498754250426445010415937 41624065687819833757811953)
        ·
          refine ⟨31218049265864875318358965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41624065687819833757811953 31218049265864875318358965)
          ·
            refine ⟨2926692118674832061096153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31218049265864875318358965 2926692118674832061096153)
            ·
              refine ⟨2195019089006124045822115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926692118674832061096153 2195019089006124045822115)
              ·
                refine ⟨3292528633509186068733173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195019089006124045822115 3292528633509186068733173)
                ·
                  refine ⟨308674559391486193943735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3292528633509186068733173 308674559391486193943735)
                  ·
                    rfl

theorem cell22_2705137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 5].length) (baseStart_2705137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705137 prefixEnd_2705137 := by exact prefixLift 2705137
  have htrace : WordTrace (prefixWord ++ tailWord_2705137) baseStart_2705137 baseEnd_2705137 := by
    simpa [prefixWord, tailWord_2705137, baseEnd_2705137] using wordTrace_append hprefix tailTrace_2705137
  have hstable : (prefixWord ++ tailWord_2705137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705137).length < 2 ^ (prefixWord ++ tailWord_2705137).sum := by decide
  have hdescent : baseEnd_2705137 < baseStart_2705137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705148 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 8]
def baseStart_2705148 : Nat := 118140960795 + 2705148 * 2 ^ 59
def prefixEnd_2705148 : Nat := 4983230072969 + 3 ^ 40 * 2705148 * 2
def baseEnd_2705148 : Nat := 308675814566419406602057

theorem tailTrace_2705148 : CollatzResearch.WordTrace tailWord_2705148 prefixEnd_2705148 308675814566419406602057 := by
  unfold tailWord_2705148
  simp only [CollatzResearch.WordTrace]
  refine ⟨49332426601859136670806049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65776568802478848894408065 49332426601859136670806049)
  ·
    refine ⟨36999319951394352503104537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49332426601859136670806049 36999319951394352503104537)
    ·
      refine ⟨27749489963545764377328403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36999319951394352503104537 27749489963545764377328403)
      ·
        refine ⟨41624234945318646565992605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27749489963545764377328403 41624234945318646565992605)
        ·
          refine ⟨15609088104494492462247227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41624234945318646565992605 15609088104494492462247227)
          ·
            refine ⟨23413632156741738693370841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15609088104494492462247227 23413632156741738693370841)
            ·
              refine ⟨17560224117556304020028131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23413632156741738693370841 17560224117556304020028131)
              ·
                refine ⟨26340336176334456030042197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17560224117556304020028131 26340336176334456030042197)
                ·
                  refine ⟨308675814566419406602057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26340336176334456030042197 308675814566419406602057)
                  ·
                    rfl

theorem cell22_2705148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_2705148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705148 prefixEnd_2705148 := by exact prefixLift 2705148
  have htrace : WordTrace (prefixWord ++ tailWord_2705148) baseStart_2705148 baseEnd_2705148 := by
    simpa [prefixWord, tailWord_2705148, baseEnd_2705148] using wordTrace_append hprefix tailTrace_2705148
  have hstable : (prefixWord ++ tailWord_2705148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705148).length < 2 ^ (prefixWord ++ tailWord_2705148).sum := by decide
  have hdescent : baseEnd_2705148 < baseStart_2705148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705163 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 3, 5]
def baseStart_2705163 : Nat := 118140960795 + 2705163 * 2 ^ 59
def prefixEnd_2705163 : Nat := 4983230072969 + 3 ^ 40 * 2705163 * 2
def baseEnd_2705163 : Nat := 926032578505803180681125

theorem tailTrace_2705163 : CollatzResearch.WordTrace tailWord_2705163 prefixEnd_2705163 926032578505803180681125 := by
  unfold tailWord_2705163
  simp only [CollatzResearch.WordTrace]
  refine ⟨98665400298663930903408143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65776933532442620602272095 98665400298663930903408143)
  ·
    refine ⟨147998100447995896355112215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98665400298663930903408143 147998100447995896355112215)
    ·
      refine ⟨221997150671993844532668323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147998100447995896355112215 221997150671993844532668323)
      ·
        refine ⟨332995726007990766799002485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221997150671993844532668323 332995726007990766799002485)
        ·
          refine ⟨31218349313249134387406483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 332995726007990766799002485 31218349313249134387406483)
          ·
            refine ⟨46827523969873701581109725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31218349313249134387406483 46827523969873701581109725)
            ·
              refine ⟨17560321488702638092916147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46827523969873701581109725 17560321488702638092916147)
              ·
                refine ⟨26340482233053957139374221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17560321488702638092916147 26340482233053957139374221)
                ·
                  refine ⟨9877680837395233927265333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26340482233053957139374221 9877680837395233927265333)
                  ·
                    refine ⟨926032578505803180681125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9877680837395233927265333 926032578505803180681125)
                    ·
                      rfl

theorem cell22_2705163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 5].length) (baseStart_2705163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705163 prefixEnd_2705163 := by exact prefixLift 2705163
  have htrace : WordTrace (prefixWord ++ tailWord_2705163) baseStart_2705163 baseEnd_2705163 := by
    simpa [prefixWord, tailWord_2705163, baseEnd_2705163] using wordTrace_append hprefix tailTrace_2705163
  have hstable : (prefixWord ++ tailWord_2705163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705163).length < 2 ^ (prefixWord ++ tailWord_2705163).sum := by decide
  have hdescent : baseEnd_2705163 < baseStart_2705163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705225 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 5, 3]
def baseStart_2705225 : Nat := 118140960795 + 2705225 * 2 ^ 59
def prefixEnd_2705225 : Nat := 4983230072969 + 3 ^ 40 * 2705225 * 2
def baseEnd_2705225 : Nat := 926053802372855685630935

theorem tailTrace_2705225 : CollatzResearch.WordTrace tailWord_2705225 prefixEnd_2705225 926053802372855685630935 := by
  unfold tailWord_2705225
  simp only [CollatzResearch.WordTrace]
  refine ⟨98667661624439315492165129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65778441082959543661443419 98667661624439315492165129)
  ·
    refine ⟨74000746218329486619123847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98667661624439315492165129 74000746218329486619123847)
    ·
      refine ⟨111001119327494229928685771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74000746218329486619123847 111001119327494229928685771)
      ·
        refine ⟨166501678991241344893028657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111001119327494229928685771 166501678991241344893028657)
        ·
          refine ⟨124876259243431008669771493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166501678991241344893028657 124876259243431008669771493)
          ·
            refine ⟨23414298608143314125582155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124876259243431008669771493 23414298608143314125582155)
            ·
              refine ⟨35121447912214971188373233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23414298608143314125582155 35121447912214971188373233)
              ·
                refine ⟨26341085934161228391279925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35121447912214971188373233 26341085934161228391279925)
                ·
                  refine ⟨2469476806327615161682493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26341085934161228391279925 2469476806327615161682493)
                  ·
                    refine ⟨926053802372855685630935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2469476806327615161682493 926053802372855685630935)
                    ·
                      rfl

theorem cell22_2705225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 3].length) (baseStart_2705225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705225 prefixEnd_2705225 := by exact prefixLift 2705225
  have htrace : WordTrace (prefixWord ++ tailWord_2705225) baseStart_2705225 baseEnd_2705225 := by
    simpa [prefixWord, tailWord_2705225, baseEnd_2705225] using wordTrace_append hprefix tailTrace_2705225
  have hstable : (prefixWord ++ tailWord_2705225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705225).length < 2 ^ (prefixWord ++ tailWord_2705225).sum := by decide
  have hdescent : baseEnd_2705225 < baseStart_2705225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705242 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 3, 3]
def baseStart_2705242 : Nat := 118140960795 + 2705242 * 2 ^ 59
def prefixEnd_2705242 : Nat := 4983230072969 + 3 ^ 40 * 2705242 * 2
def baseEnd_2705242 : Nat := 926059621820273307955883

theorem tailTrace_2705242 : CollatzResearch.WordTrace tailWord_2705242 prefixEnd_2705242 926059621820273307955883 := by
  unfold tailWord_2705242
  simp only [CollatzResearch.WordTrace]
  refine ⟨24667070416344431848883495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65778854443585151597022653 24667070416344431848883495)
  ·
    refine ⟨37000605624516647773325243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24667070416344431848883495 37000605624516647773325243)
    ·
      refine ⟨55500908436774971659987865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37000605624516647773325243 55500908436774971659987865)
      ·
        refine ⟨41625681327581228744990899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55500908436774971659987865 41625681327581228744990899)
        ·
          refine ⟨62438521991371843117486349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41625681327581228744990899 62438521991371843117486349)
          ·
            refine ⟨23414445746764441169057381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62438521991371843117486349 23414445746764441169057381)
            ·
              refine ⟨4390208577518332719198259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23414445746764441169057381 4390208577518332719198259)
              ·
                refine ⟨6585312866277499078797389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390208577518332719198259 6585312866277499078797389)
                ·
                  refine ⟨2469492324854062154549021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6585312866277499078797389 2469492324854062154549021)
                  ·
                    refine ⟨926059621820273307955883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2469492324854062154549021 926059621820273307955883)
                    ·
                      rfl

theorem cell22_2705242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_2705242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705242 prefixEnd_2705242 := by exact prefixLift 2705242
  have htrace : WordTrace (prefixWord ++ tailWord_2705242) baseStart_2705242 baseEnd_2705242 := by
    simpa [prefixWord, tailWord_2705242, baseEnd_2705242] using wordTrace_append hprefix tailTrace_2705242
  have hstable : (prefixWord ++ tailWord_2705242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705242).length < 2 ^ (prefixWord ++ tailWord_2705242).sum := by decide
  have hdescent : baseEnd_2705242 < baseStart_2705242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705315 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 1, 5]
def baseStart_2705315 : Nat := 118140960795 + 2705315 * 2 ^ 59
def prefixEnd_2705315 : Nat := 4983230072969 + 3 ^ 40 * 2705315 * 2
def baseEnd_2705315 : Nat := 926084611212125450880659

theorem tailTrace_2705315 : CollatzResearch.WordTrace tailWord_2705315 prefixEnd_2705315 926084611212125450880659 := by
  unfold tailWord_2705315
  simp only [CollatzResearch.WordTrace]
  refine ⟨98670944194113260862941399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65780629462742173908627599 98670944194113260862941399)
  ·
    refine ⟨148006416291169891294412099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98670944194113260862941399 148006416291169891294412099)
    ·
      refine ⟨222009624436754836941618149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148006416291169891294412099 222009624436754836941618149)
      ·
        refine ⟨41626804581891531926553403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222009624436754836941618149 41626804581891531926553403)
        ·
          refine ⟨62440206872837297889830105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41626804581891531926553403 62440206872837297889830105)
          ·
            refine ⟨46830155154627973417372579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62440206872837297889830105 46830155154627973417372579)
            ·
              refine ⟨70245232731941960126058869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46830155154627973417372579 70245232731941960126058869)
              ·
                refine ⟨6585490568619558761818019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70245232731941960126058869 6585490568619558761818019)
                ·
                  refine ⟨9878235852929338142727029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585490568619558761818019 9878235852929338142727029)
                  ·
                    refine ⟨926084611212125450880659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9878235852929338142727029 926084611212125450880659)
                    ·
                      rfl

theorem cell22_2705315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 5].length) (baseStart_2705315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705315 prefixEnd_2705315 := by exact prefixLift 2705315
  have htrace : WordTrace (prefixWord ++ tailWord_2705315) baseStart_2705315 baseEnd_2705315 := by
    simpa [prefixWord, tailWord_2705315, baseEnd_2705315] using wordTrace_append hprefix tailTrace_2705315
  have hstable : (prefixWord ++ tailWord_2705315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705315).length < 2 ^ (prefixWord ++ tailWord_2705315).sum := by decide
  have hdescent : baseEnd_2705315 < baseStart_2705315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705319 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 1, 4]
def baseStart_2705319 : Nat := 118140960795 + 2705319 * 2 ^ 59
def prefixEnd_2705319 : Nat := 4983230072969 + 3 ^ 40 * 2705319 * 2
def baseEnd_2705319 : Nat := 926085980493870773780647

theorem tailTrace_2705319 : CollatzResearch.WordTrace tailWord_2705319 prefixEnd_2705319 926085980493870773780647 := by
  unfold tailWord_2705319
  simp only [CollatzResearch.WordTrace]
  refine ⟨98671090086098769546087011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65780726724065846364058007 98671090086098769546087011)
  ·
    refine ⟨148006635129148154319130517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98671090086098769546087011 148006635129148154319130517)
    ·
      refine ⟨6937811021678819733709243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 148006635129148154319130517 6937811021678819733709243)
      ·
        refine ⟨10406716532518229600563865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6937811021678819733709243 10406716532518229600563865)
        ·
          refine ⟨7805037399388672200422899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10406716532518229600563865 7805037399388672200422899)
          ·
            refine ⟨11707556099083008300634349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7805037399388672200422899 11707556099083008300634349)
            ·
              refine ⟨4390333537156128112737881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11707556099083008300634349 4390333537156128112737881)
              ·
                refine ⟨3292750152867096084553411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4390333537156128112737881 3292750152867096084553411)
                ·
                  refine ⟨4939125229300644126830117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292750152867096084553411 4939125229300644126830117)
                  ·
                    refine ⟨926085980493870773780647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4939125229300644126830117 926085980493870773780647)
                    ·
                      rfl

theorem cell22_2705319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_2705319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705319 prefixEnd_2705319 := by exact prefixLift 2705319
  have htrace : WordTrace (prefixWord ++ tailWord_2705319) baseStart_2705319 baseEnd_2705319 := by
    simpa [prefixWord, tailWord_2705319, baseEnd_2705319] using wordTrace_append hprefix tailTrace_2705319
  have hstable : (prefixWord ++ tailWord_2705319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705319).length < 2 ^ (prefixWord ++ tailWord_2705319).sum := by decide
  have hdescent : baseEnd_2705319 < baseStart_2705319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705330 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_2705330 : Nat := 118140960795 + 2705330 * 2 ^ 59
def prefixEnd_2705330 : Nat := 4983230072969 + 3 ^ 40 * 2705330 * 2
def baseEnd_2705330 : Nat := 926089746018670411755613

theorem tailTrace_2705330 : CollatzResearch.WordTrace tailWord_2705330 prefixEnd_2705330 926089746018670411755613 := by
  unfold tailWord_2705330
  simp only [CollatzResearch.WordTrace]
  refine ⟨24667872822264729606184361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65780994192705945616491629 24667872822264729606184361)
  ·
    refine ⟨18500904616698547204638271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24667872822264729606184361 18500904616698547204638271)
    ·
      refine ⟨27751356925047820806957407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18500904616698547204638271 27751356925047820806957407)
      ·
        refine ⟨41627035387571731210436111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27751356925047820806957407 41627035387571731210436111)
        ·
          refine ⟨62440553081357596815654167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41627035387571731210436111 62440553081357596815654167)
          ·
            refine ⟨93660829622036395223481251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62440553081357596815654167 93660829622036395223481251)
            ·
              refine ⟨140491244433054592835221877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93660829622036395223481251 140491244433054592835221877)
              ·
                refine ⟨13171054165598868078302051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140491244433054592835221877 13171054165598868078302051)
                ·
                  refine ⟨19756581248398302117453077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13171054165598868078302051 19756581248398302117453077)
                  ·
                    refine ⟨926089746018670411755613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19756581248398302117453077 926089746018670411755613)
                    ·
                      rfl

theorem cell22_2705330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_2705330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705330 prefixEnd_2705330 := by exact prefixLift 2705330
  have htrace : WordTrace (prefixWord ++ tailWord_2705330) baseStart_2705330 baseEnd_2705330 := by
    simpa [prefixWord, tailWord_2705330, baseEnd_2705330] using wordTrace_append hprefix tailTrace_2705330
  have hstable : (prefixWord ++ tailWord_2705330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705330).length < 2 ^ (prefixWord ++ tailWord_2705330).sum := by decide
  have hdescent : baseEnd_2705330 < baseStart_2705330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705366 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2705366 : Nat := 118140960795 + 2705366 * 2 ^ 59
def prefixEnd_2705366 : Nat := 4983230072969 + 3 ^ 40 * 2705366 * 2
def baseEnd_2705366 : Nat := 926102069554378317855503

theorem tailTrace_2705366 : CollatzResearch.WordTrace tailWord_2705366 prefixEnd_2705366 926102069554378317855503 := by
  unfold tailWord_2705366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6167050269808031035815497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65781869544618997715365301 6167050269808031035815497)
  ·
    refine ⟨4625287702356023276861623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6167050269808031035815497 4625287702356023276861623)
    ·
      refine ⟨6937931553534034915292435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4625287702356023276861623 6937931553534034915292435)
      ·
        refine ⟨10406897330301052372938653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6937931553534034915292435 10406897330301052372938653)
        ·
          refine ⟨3902586498862894639851995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10406897330301052372938653 3902586498862894639851995)
          ·
            refine ⟨5853879748294341959777993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902586498862894639851995 5853879748294341959777993)
            ·
              refine ⟨4390409811220756469833495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5853879748294341959777993 4390409811220756469833495)
              ·
                refine ⟨6585614716831134704750243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390409811220756469833495 6585614716831134704750243)
                ·
                  refine ⟨9878422075246702057125365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585614716831134704750243 9878422075246702057125365)
                  ·
                    refine ⟨926102069554378317855503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9878422075246702057125365 926102069554378317855503)
                    ·
                      rfl

theorem cell22_2705366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2705366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705366 prefixEnd_2705366 := by exact prefixLift 2705366
  have htrace : WordTrace (prefixWord ++ tailWord_2705366) baseStart_2705366 baseEnd_2705366 := by
    simpa [prefixWord, tailWord_2705366, baseEnd_2705366] using wordTrace_append hprefix tailTrace_2705366
  have hstable : (prefixWord ++ tailWord_2705366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705366).length < 2 ^ (prefixWord ++ tailWord_2705366).sum := by decide
  have hdescent : baseEnd_2705366 < baseStart_2705366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705377 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 5, 3]
def baseStart_2705377 : Nat := 118140960795 + 2705377 * 2 ^ 59
def prefixEnd_2705377 : Nat := 4983230072969 + 3 ^ 40 * 2705377 * 2
def baseEnd_2705377 : Nat := 926105835079177955830469

theorem tailTrace_2705377 : CollatzResearch.WordTrace tailWord_2705377 prefixEnd_2705377 926105835079177955830469 := by
  unfold tailWord_2705377
  simp only [CollatzResearch.WordTrace]
  refine ⟨98673205519888645451698385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65782137013259096967798923 98673205519888645451698385)
  ·
    refine ⟨74004904139916484088773789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98673205519888645451698385 74004904139916484088773789)
    ·
      refine ⟨27751839052468681533290171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74004904139916484088773789 27751839052468681533290171)
      ·
        refine ⟨41627758578703022299935257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27751839052468681533290171 41627758578703022299935257)
        ·
          refine ⟨31220818934027266724951443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41627758578703022299935257 31220818934027266724951443)
          ·
            refine ⟨46831228401040900087427165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31220818934027266724951443 46831228401040900087427165)
            ·
              refine ⟨17561710650390337532785187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46831228401040900087427165 17561710650390337532785187)
              ·
                refine ⟨26342565975585506299177781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17561710650390337532785187 26342565975585506299177781)
                ·
                  refine ⟨2469615560211141215547917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26342565975585506299177781 2469615560211141215547917)
                  ·
                    refine ⟨926105835079177955830469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2469615560211141215547917 926105835079177955830469)
                    ·
                      rfl

theorem cell22_2705377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_2705377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705377 prefixEnd_2705377 := by exact prefixLift 2705377
  have htrace : WordTrace (prefixWord ++ tailWord_2705377) baseStart_2705377 baseEnd_2705377 := by
    simpa [prefixWord, tailWord_2705377, baseEnd_2705377] using wordTrace_append hprefix tailTrace_2705377
  have hstable : (prefixWord ++ tailWord_2705377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705377).length < 2 ^ (prefixWord ++ tailWord_2705377).sum := by decide
  have hdescent : baseEnd_2705377 < baseStart_2705377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705422 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_2705422 : Nat := 118140960795 + 2705422 * 2 ^ 59
def prefixEnd_2705422 : Nat := 4983230072969 + 3 ^ 40 * 2705422 * 2
def baseEnd_2705422 : Nat := 926121239498812838455331

theorem tailTrace_2705422 : CollatzResearch.WordTrace tailWord_2705422 prefixEnd_2705422 926121239498812838455331 := by
  unfold tailWord_2705422
  simp only [CollatzResearch.WordTrace]
  refine ⟨12334355850590702267135815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65783231203150412091391013 12334355850590702267135815)
  ·
    refine ⟨18501533775886053400703723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12334355850590702267135815 18501533775886053400703723)
    ·
      refine ⟨27752300663829080101055585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18501533775886053400703723 27752300663829080101055585)
      ·
        refine ⟨20814225497871810075791689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27752300663829080101055585 20814225497871810075791689)
        ·
          refine ⟨15610669123403857556843767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20814225497871810075791689 15610669123403857556843767)
          ·
            refine ⟨23416003685105786335265651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15610669123403857556843767 23416003685105786335265651)
            ·
              refine ⟨35124005527658679502898477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23416003685105786335265651 35124005527658679502898477)
              ·
                refine ⟨13171502072872004813586929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35124005527658679502898477 13171502072872004813586929)
                ·
                  refine ⟨9878626554654003610190197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13171502072872004813586929 9878626554654003610190197)
                  ·
                    refine ⟨926121239498812838455331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9878626554654003610190197 926121239498812838455331)
                    ·
                      rfl

theorem cell22_2705422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_2705422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705422 prefixEnd_2705422 := by exact prefixLift 2705422
  have htrace : WordTrace (prefixWord ++ tailWord_2705422) baseStart_2705422 baseEnd_2705422 := by
    simpa [prefixWord, tailWord_2705422, baseEnd_2705422] using wordTrace_append hprefix tailTrace_2705422
  have hstable : (prefixWord ++ tailWord_2705422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705422).length < 2 ^ (prefixWord ++ tailWord_2705422).sum := by decide
  have hdescent : baseEnd_2705422 < baseStart_2705422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705435 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 8]
def baseStart_2705435 : Nat := 118140960795 + 2705435 * 2 ^ 59
def prefixEnd_2705435 : Nat := 4983230072969 + 3 ^ 40 * 2705435 * 2
def baseEnd_2705435 : Nat := 308708563221495045960097

theorem tailTrace_2705435 : CollatzResearch.WordTrace tailWord_2705435 prefixEnd_2705435 308708563221495045960097 := by
  unfold tailWord_2705435
  simp only [CollatzResearch.WordTrace]
  refine ⟨98675320953678521357309759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65783547302452347571539839 98675320953678521357309759)
  ·
    refine ⟨148012981430517782035964639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98675320953678521357309759 148012981430517782035964639)
    ·
      refine ⟨222019472145776673053946959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148012981430517782035964639 222019472145776673053946959)
      ·
        refine ⟨333029208218665009580920439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222019472145776673053946959 333029208218665009580920439)
        ·
          refine ⟨499543812327997514371380659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333029208218665009580920439 499543812327997514371380659)
          ·
            refine ⟨749315718491996271557070989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499543812327997514371380659 749315718491996271557070989)
            ·
              refine ⟨280993394434498601833901621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749315718491996271557070989 280993394434498601833901621)
              ·
                refine ⟨26343130728234243921928277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 280993394434498601833901621 26343130728234243921928277)
                ·
                  refine ⟨308708563221495045960097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26343130728234243921928277 308708563221495045960097)
                  ·
                    rfl

theorem cell22_2705435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 8].length) (baseStart_2705435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705435 prefixEnd_2705435 := by exact prefixLift 2705435
  have htrace : WordTrace (prefixWord ++ tailWord_2705435) baseStart_2705435 baseEnd_2705435 := by
    simpa [prefixWord, tailWord_2705435, baseEnd_2705435] using wordTrace_append hprefix tailTrace_2705435
  have hstable : (prefixWord ++ tailWord_2705435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705435).length < 2 ^ (prefixWord ++ tailWord_2705435).sum := by decide
  have hdescent : baseEnd_2705435 < baseStart_2705435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705482 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_2705482 : Nat := 118140960795 + 2705482 * 2 ^ 59
def prefixEnd_2705482 : Nat := 4983230072969 + 3 ^ 40 * 2705482 * 2
def baseEnd_2705482 : Nat := 926141778724992681955147

theorem tailTrace_2705482 : CollatzResearch.WordTrace tailWord_2705482 prefixEnd_2705482 926141778724992681955147 := by
  unfold tailWord_2705482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24669258796127062096067675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65784690123005498922847133 24669258796127062096067675)
  ·
    refine ⟨37003888194190593144101513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24669258796127062096067675 37003888194190593144101513)
    ·
      refine ⟨27752916145642944858076135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37003888194190593144101513 27752916145642944858076135)
      ·
        refine ⟨41629374218464417287114203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27752916145642944858076135 41629374218464417287114203)
        ·
          refine ⟨62444061327696625930671305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41629374218464417287114203 62444061327696625930671305)
          ·
            refine ⟨46833045995772469448003479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62444061327696625930671305 46833045995772469448003479)
            ·
              refine ⟨70249568993658704172005219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46833045995772469448003479 70249568993658704172005219)
              ·
                refine ⟨105374353490488056258007829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70249568993658704172005219 105374353490488056258007829)
                ·
                  refine ⟨4939422819866627637094117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105374353490488056258007829 4939422819866627637094117)
                  ·
                    refine ⟨926141778724992681955147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4939422819866627637094117 926141778724992681955147)
                    ·
                      rfl

theorem cell22_2705482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_2705482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705482 prefixEnd_2705482 := by exact prefixLift 2705482
  have htrace : WordTrace (prefixWord ++ tailWord_2705482) baseStart_2705482 baseEnd_2705482 := by
    simpa [prefixWord, tailWord_2705482, baseEnd_2705482] using wordTrace_append hprefix tailTrace_2705482
  have hstable : (prefixWord ++ tailWord_2705482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705482).length < 2 ^ (prefixWord ++ tailWord_2705482).sum := by decide
  have hdescent : baseEnd_2705482 < baseStart_2705482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705501 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2705501 : Nat := 118140960795 + 2705501 * 2 ^ 59
def prefixEnd_2705501 : Nat := 4983230072969 + 3 ^ 40 * 2705501 * 2
def baseEnd_2705501 : Nat := 926148282813282965730089

theorem tailTrace_2705501 : CollatzResearch.WordTrace tailWord_2705501 prefixEnd_2705501 926148282813282965730089 := by
  unfold tailWord_2705501
  simp only [CollatzResearch.WordTrace]
  refine ⟨98677728171439414629212357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65785152114292943086141571 98677728171439414629212357)
  ·
    refine ⟨18502074032144890242977317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98677728171439414629212357 18502074032144890242977317)
    ·
      refine ⟨3469138881027166920558247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18502074032144890242977317 3469138881027166920558247)
      ·
        refine ⟨5203708321540750380837371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3469138881027166920558247 5203708321540750380837371)
        ·
          refine ⟨7805562482311125571256057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5203708321540750380837371 7805562482311125571256057)
          ·
            refine ⟨5854171861733344178442043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7805562482311125571256057 5854171861733344178442043)
            ·
              refine ⟨8781257792600016267663065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854171861733344178442043 8781257792600016267663065)
              ·
                refine ⟨6585943344450012200747299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8781257792600016267663065 6585943344450012200747299)
                ·
                  refine ⟨9878915016675018301120949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585943344450012200747299 9878915016675018301120949)
                  ·
                    refine ⟨926148282813282965730089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9878915016675018301120949 926148282813282965730089)
                    ·
                      rfl

theorem cell22_2705501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2705501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705501 prefixEnd_2705501 := by exact prefixLift 2705501
  have htrace : WordTrace (prefixWord ++ tailWord_2705501) baseStart_2705501 baseEnd_2705501 := by
    simpa [prefixWord, tailWord_2705501, baseEnd_2705501] using wordTrace_append hprefix tailTrace_2705501
  have hstable : (prefixWord ++ tailWord_2705501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705501).length < 2 ^ (prefixWord ++ tailWord_2705501).sum := by decide
  have hdescent : baseEnd_2705501 < baseStart_2705501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705514 : List Nat := [3, 1, 3, 2, 4, 9]
def baseStart_2705514 : Nat := 118140960795 + 2705514 * 2 ^ 59
def prefixEnd_2705514 : Nat := 4983230072969 + 3 ^ 40 * 2705514 * 2
def baseEnd_2705514 : Nat := 11433984357764879816729

theorem tailTrace_2705514 : CollatzResearch.WordTrace tailWord_2705514 prefixEnd_2705514 11433984357764879816729 := by
  unfold tailWord_2705514
  simp only [CollatzResearch.WordTrace]
  refine ⟨24669550580098079462358899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65785468213594878566290397 24669550580098079462358899)
  ·
    refine ⟨37004325870147119193538349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24669550580098079462358899 37004325870147119193538349)
    ·
      refine ⟨13876622201305169697576881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37004325870147119193538349 13876622201305169697576881)
      ·
        refine ⟨10407466650978877273182661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13876622201305169697576881 10407466650978877273182661)
        ·
          refine ⟨1951399997058539488721749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10407466650978877273182661 1951399997058539488721749)
          ·
            refine ⟨11433984357764879816729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1951399997058539488721749 11433984357764879816729)
            ·
              rfl

theorem cell22_2705514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 9].length) (baseStart_2705514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705514 prefixEnd_2705514 := by exact prefixLift 2705514
  have htrace : WordTrace (prefixWord ++ tailWord_2705514) baseStart_2705514 baseEnd_2705514 := by
    simpa [prefixWord, tailWord_2705514, baseEnd_2705514] using wordTrace_append hprefix tailTrace_2705514
  have hstable : (prefixWord ++ tailWord_2705514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705514).length < 2 ^ (prefixWord ++ tailWord_2705514).sum := by decide
  have hdescent : baseEnd_2705514 < baseStart_2705514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705527 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 2, 6]
def baseStart_2705527 : Nat := 118140960795 + 2705527 * 2 ^ 59
def prefixEnd_2705527 : Nat := 4983230072969 + 3 ^ 40 * 2705527 * 2
def baseEnd_2705527 : Nat := 926157183144627564580009

theorem tailTrace_2705527 : CollatzResearch.WordTrace tailWord_2705527 prefixEnd_2705527 926157183144627564580009 := by
  unfold tailWord_2705527
  simp only [CollatzResearch.WordTrace]
  refine ⟨98678676469345221069658835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65785784312896814046439223 98678676469345221069658835)
  ·
    refine ⟨148018014704017831604488253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98678676469345221069658835 148018014704017831604488253)
    ·
      refine ⟨55506755514006686851683095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148018014704017831604488253 55506755514006686851683095)
      ·
        refine ⟨83260133271010030277524643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55506755514006686851683095 83260133271010030277524643)
        ·
          refine ⟨124890199906515045416286965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83260133271010030277524643 124890199906515045416286965)
          ·
            refine ⟨11708456241235785507776903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124890199906515045416286965 11708456241235785507776903)
            ·
              refine ⟨17562684361853678261665355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11708456241235785507776903 17562684361853678261665355)
              ·
                refine ⟨26344026542780517392498033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17562684361853678261665355 26344026542780517392498033)
                ·
                  refine ⟨19758019907085388044373525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26344026542780517392498033 19758019907085388044373525)
                  ·
                    refine ⟨926157183144627564580009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19758019907085388044373525 926157183144627564580009)
                    ·
                      rfl

theorem cell22_2705527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_2705527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705527 prefixEnd_2705527 := by exact prefixLift 2705527
  have htrace : WordTrace (prefixWord ++ tailWord_2705527) baseStart_2705527 baseEnd_2705527 := by
    simpa [prefixWord, tailWord_2705527, baseEnd_2705527] using wordTrace_append hprefix tailTrace_2705527
  have hstable : (prefixWord ++ tailWord_2705527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705527).length < 2 ^ (prefixWord ++ tailWord_2705527).sum := by decide
  have hdescent : baseEnd_2705527 < baseStart_2705527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705546 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 3, 3]
def baseStart_2705546 : Nat := 118140960795 + 2705546 * 2 ^ 59
def prefixEnd_2705546 : Nat := 4983230072969 + 3 ^ 40 * 2705546 * 2
def baseEnd_2705546 : Nat := 926163687232917848354951

theorem tailTrace_2705546 : CollatzResearch.WordTrace tailWord_2705546 prefixEnd_2705546 926163687232917848354951 := by
  unfold tailWord_2705546
  simp only [CollatzResearch.WordTrace]
  refine ⟨24669842364069096828650123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65786246304184258209733661 24669842364069096828650123)
  ·
    refine ⟨37004763546103645242975185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24669842364069096828650123 37004763546103645242975185)
    ·
      refine ⟨27753572659577733932231389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37004763546103645242975185 27753572659577733932231389)
      ·
        refine ⟨10407589747341650224586771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27753572659577733932231389 10407589747341650224586771)
        ·
          refine ⟨15611384621012475336880157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10407589747341650224586771 15611384621012475336880157)
          ·
            refine ⟨5854269232879678251330059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15611384621012475336880157 5854269232879678251330059)
            ·
              refine ⟨8781403849319517376995089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854269232879678251330059 8781403849319517376995089)
              ·
                refine ⟨6586052886989638032746317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8781403849319517376995089 6586052886989638032746317)
                ·
                  refine ⟨2469769832621114262279869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6586052886989638032746317 2469769832621114262279869)
                  ·
                    refine ⟨926163687232917848354951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2469769832621114262279869 926163687232917848354951)
                    ·
                      rfl

theorem cell22_2705546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_2705546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705546 prefixEnd_2705546 := by exact prefixLift 2705546
  have htrace : WordTrace (prefixWord ++ tailWord_2705546) baseStart_2705546 baseEnd_2705546 := by
    simpa [prefixWord, tailWord_2705546, baseEnd_2705546] using wordTrace_append hprefix tailTrace_2705546
  have hstable : (prefixWord ++ tailWord_2705546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705546).length < 2 ^ (prefixWord ++ tailWord_2705546).sum := by decide
  have hdescent : baseEnd_2705546 < baseStart_2705546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705557 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2705557 : Nat := 118140960795 + 2705557 * 2 ^ 59
def prefixEnd_2705557 : Nat := 4983230072969 + 3 ^ 40 * 2705557 * 2
def baseEnd_2705557 : Nat := 926167452757717486329917

theorem tailTrace_2705557 : CollatzResearch.WordTrace tailWord_2705557 prefixEnd_2705557 926167452757717486329917 := by
  unfold tailWord_2705557
  simp only [CollatzResearch.WordTrace]
  refine ⟨98679770659236536193250925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65786513772824357462167283 98679770659236536193250925)
  ·
    refine ⟨37004913997213701072469097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98679770659236536193250925 37004913997213701072469097)
    ·
      refine ⟨27753685497910275804351823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37004913997213701072469097 27753685497910275804351823)
      ·
        refine ⟨41630528246865413706527735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27753685497910275804351823 41630528246865413706527735)
        ·
          refine ⟨62445792370298120559791603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41630528246865413706527735 62445792370298120559791603)
          ·
            refine ⟨93668688555447180839687405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62445792370298120559791603 93668688555447180839687405)
            ·
              refine ⟨35125758208292692814882777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93668688555447180839687405 35125758208292692814882777)
              ·
                refine ⟨26344318656219519611162083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35125758208292692814882777 26344318656219519611162083)
                ·
                  refine ⟨39516477984329279416743125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26344318656219519611162083 39516477984329279416743125)
                  ·
                    refine ⟨926167452757717486329917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39516477984329279416743125 926167452757717486329917)
                    ·
                      rfl

theorem cell22_2705557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2705557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705557 prefixEnd_2705557 := by exact prefixLift 2705557
  have htrace : WordTrace (prefixWord ++ tailWord_2705557) baseStart_2705557 baseEnd_2705557 := by
    simpa [prefixWord, tailWord_2705557, baseEnd_2705557] using wordTrace_append hprefix tailTrace_2705557
  have hstable : (prefixWord ++ tailWord_2705557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705557).length < 2 ^ (prefixWord ++ tailWord_2705557).sum := by decide
  have hdescent : baseEnd_2705557 < baseStart_2705557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705636 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_2705636 : Nat := 118140960795 + 2705636 * 2 ^ 59
def prefixEnd_2705636 : Nat := 4983230072969 + 3 ^ 40 * 2705636 * 2
def baseEnd_2705636 : Nat := 926194496072187613604675

theorem tailTrace_2705636 : CollatzResearch.WordTrace tailWord_2705636 prefixEnd_2705636 926194496072187613604675 := by
  unfold tailWord_2705636
  simp only [CollatzResearch.WordTrace]
  refine ⟨49341326012975166342688381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65788434683966888456917841 49341326012975166342688381)
  ·
    refine ⟨18502997254865687378508143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49341326012975166342688381 18502997254865687378508143)
    ·
      refine ⟨27754495882298531067762215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18502997254865687378508143 27754495882298531067762215)
      ·
        refine ⟨41631743823447796601643323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27754495882298531067762215 41631743823447796601643323)
        ·
          refine ⟨62447615735171694902464985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41631743823447796601643323 62447615735171694902464985)
          ·
            refine ⟨46835711801378771176848739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62447615735171694902464985 46835711801378771176848739)
            ·
              refine ⟨70253567702068156765273109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46835711801378771176848739 70253567702068156765273109)
              ·
                refine ⟨3293135986034444848372177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70253567702068156765273109 3293135986034444848372177)
                ·
                  refine ⟨2469851989525833636279133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3293135986034444848372177 2469851989525833636279133)
                  ·
                    refine ⟨926194496072187613604675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2469851989525833636279133 926194496072187613604675)
                    ·
                      rfl

theorem cell22_2705636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_2705636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705636 prefixEnd_2705636 := by exact prefixLift 2705636
  have htrace : WordTrace (prefixWord ++ tailWord_2705636) baseStart_2705636 baseEnd_2705636 := by
    simpa [prefixWord, tailWord_2705636, baseEnd_2705636] using wordTrace_append hprefix tailTrace_2705636
  have hstable : (prefixWord ++ tailWord_2705636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705636).length < 2 ^ (prefixWord ++ tailWord_2705636).sum := by decide
  have hdescent : baseEnd_2705636 < baseStart_2705636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705666 : List Nat := [3, 4, 1, 1, 2, 1, 2, 8]
def baseStart_2705666 : Nat := 118140960795 + 2705666 * 2 ^ 59
def prefixEnd_2705666 : Nat := 4983230072969 + 3 ^ 40 * 2705666 * 2
def baseEnd_2705666 : Nat := 102911640631697503928287

theorem tailTrace_2705666 : CollatzResearch.WordTrace tailWord_2705666 prefixEnd_2705666 102911640631697503928287 := by
  unfold tailWord_2705666
  simp only [CollatzResearch.WordTrace]
  refine ⟨24670936553960411952242213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65789164143894431872645901 24670936553960411952242213)
  ·
    refine ⟨4625800603867577241045415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24670936553960411952242213 4625800603867577241045415)
    ·
      refine ⟨6938700905801365861568123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4625800603867577241045415 6938700905801365861568123)
      ·
        refine ⟨10408051358702048792352185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6938700905801365861568123 10408051358702048792352185)
        ·
          refine ⟨7806038519026536594264139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10408051358702048792352185 7806038519026536594264139)
          ·
            refine ⟨11709057778539804891396209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7806038519026536594264139 11709057778539804891396209)
            ·
              refine ⟨8781793333904853668547157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11709057778539804891396209 8781793333904853668547157)
              ·
                refine ⟨102911640631697503928287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8781793333904853668547157 102911640631697503928287)
                ·
                  rfl

theorem cell22_2705666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_2705666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705666 prefixEnd_2705666 := by exact prefixLift 2705666
  have htrace : WordTrace (prefixWord ++ tailWord_2705666) baseStart_2705666 baseEnd_2705666 := by
    simpa [prefixWord, tailWord_2705666, baseEnd_2705666] using wordTrace_append hprefix tailTrace_2705666
  have hstable : (prefixWord ++ tailWord_2705666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705666).length < 2 ^ (prefixWord ++ tailWord_2705666).sum := by decide
  have hdescent : baseEnd_2705666 < baseStart_2705666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705668 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_2705668 : Nat := 118140960795 + 2705668 * 2 ^ 59
def prefixEnd_2705668 : Nat := 4983230072969 + 3 ^ 40 * 2705668 * 2
def baseEnd_2705668 : Nat := 926205450326150196804577

theorem tailTrace_2705668 : CollatzResearch.WordTrace tailWord_2705668 prefixEnd_2705668 926205450326150196804577 := by
  unfold tailWord_2705668
  simp only [CollatzResearch.WordTrace]
  refine ⟨49341909580917201075270829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65789212774556268100361105 49341909580917201075270829)
  ·
    refine ⟨18503216092843950403226561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49341909580917201075270829 18503216092843950403226561)
    ·
      refine ⟨13877412069632962802419921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18503216092843950403226561 13877412069632962802419921)
      ·
        refine ⟨10408059052224722101814941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13877412069632962802419921 10408059052224722101814941)
        ·
          refine ⟨3903022144584270788180603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10408059052224722101814941 3903022144584270788180603)
          ·
            refine ⟨5854533216876406182270905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3903022144584270788180603 5854533216876406182270905)
            ·
              refine ⟨4390899912657304636703179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5854533216876406182270905 4390899912657304636703179)
              ·
                refine ⟨6586349868985956955054769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390899912657304636703179 6586349868985956955054769)
                ·
                  refine ⟨4939762401739467716291077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6586349868985956955054769 4939762401739467716291077)
                  ·
                    refine ⟨926205450326150196804577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4939762401739467716291077 926205450326150196804577)
                    ·
                      rfl

theorem cell22_2705668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_2705668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705668 prefixEnd_2705668 := by exact prefixLift 2705668
  have htrace : WordTrace (prefixWord ++ tailWord_2705668) baseStart_2705668 baseEnd_2705668 := by
    simpa [prefixWord, tailWord_2705668, baseEnd_2705668] using wordTrace_append hprefix tailTrace_2705668
  have hstable : (prefixWord ++ tailWord_2705668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705668).length < 2 ^ (prefixWord ++ tailWord_2705668).sum := by decide
  have hdescent : baseEnd_2705668 < baseStart_2705668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705769 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 3, 6]
def baseStart_2705769 : Nat := 118140960795 + 2705769 * 2 ^ 59
def prefixEnd_2705769 : Nat := 4983230072969 + 3 ^ 40 * 2705769 * 2
def baseEnd_2705769 : Nat := 926240024690219600029267

theorem tailTrace_2705769 : CollatzResearch.WordTrace tailWord_2705769 prefixEnd_2705769 926240024690219600029267 := by
  unfold tailWord_2705769
  simp only [CollatzResearch.WordTrace]
  refine ⟨98687502934468496399968361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65791668622978997599978907 98687502934468496399968361)
  ·
    refine ⟨74015627200851372299976271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98687502934468496399968361 74015627200851372299976271)
    ·
      refine ⟨111023440801277058449964407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74015627200851372299976271 111023440801277058449964407)
      ·
        refine ⟨166535161201915587674946611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111023440801277058449964407 166535161201915587674946611)
        ·
          refine ⟨249802741802873381512419917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166535161201915587674946611 249802741802873381512419917)
          ·
            refine ⟨93676028176077518067157469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249802741802873381512419917 93676028176077518067157469)
            ·
              refine ⟨35128510566029069275184051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93676028176077518067157469 35128510566029069275184051)
              ·
                refine ⟨52692765849043603912776077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35128510566029069275184051 52692765849043603912776077)
                ·
                  refine ⟨19759787193391351467291029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52692765849043603912776077 19759787193391351467291029)
                  ·
                    refine ⟨926240024690219600029267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19759787193391351467291029 926240024690219600029267)
                    ·
                      rfl

theorem cell22_2705769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_2705769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705769 prefixEnd_2705769 := by exact prefixLift 2705769
  have htrace : WordTrace (prefixWord ++ tailWord_2705769) baseStart_2705769 baseEnd_2705769 := by
    simpa [prefixWord, tailWord_2705769, baseEnd_2705769] using wordTrace_append hprefix tailTrace_2705769
  have hstable : (prefixWord ++ tailWord_2705769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705769).length < 2 ^ (prefixWord ++ tailWord_2705769).sum := by decide
  have hdescent : baseEnd_2705769 < baseStart_2705769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705801 : List Nat := [1, 2, 1, 1, 6, 3, 8]
def baseStart_2705801 : Nat := 118140960795 + 2705801 * 2 ^ 59
def prefixEnd_2705801 : Nat := 4983230072969 + 3 ^ 40 * 2705801 * 2
def baseEnd_2705801 : Nat := 34305591812747488267747

theorem tailTrace_2705801 : CollatzResearch.WordTrace tailWord_2705801 prefixEnd_2705801 34305591812747488267747 := by
  unfold tailWord_2705801
  simp only [CollatzResearch.WordTrace]
  refine ⟨98688670070352565865133257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65792446713568377243422171 98688670070352565865133257)
  ·
    refine ⟨74016502552764424398849943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98688670070352565865133257 74016502552764424398849943)
    ·
      refine ⟨111024753829146636598274915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74016502552764424398849943 111024753829146636598274915)
      ·
        refine ⟨166537130743719954897412373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111024753829146636598274915 166537130743719954897412373)
        ·
          refine ⟨7806428003611872885816205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 166537130743719954897412373 7806428003611872885816205)
          ·
            refine ⟨2927410501354452332181077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7806428003611872885816205 2927410501354452332181077)
            ·
              refine ⟨34305591812747488267747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2927410501354452332181077 34305591812747488267747)
              ·
                rfl

theorem cell22_2705801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 8].length) (baseStart_2705801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705801 prefixEnd_2705801 := by exact prefixLift 2705801
  have htrace : WordTrace (prefixWord ++ tailWord_2705801) baseStart_2705801 baseEnd_2705801 := by
    simpa [prefixWord, tailWord_2705801, baseEnd_2705801] using wordTrace_append hprefix tailTrace_2705801
  have hstable : (prefixWord ++ tailWord_2705801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705801).length < 2 ^ (prefixWord ++ tailWord_2705801).sum := by decide
  have hdescent : baseEnd_2705801 < baseStart_2705801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705822 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_2705822 : Nat := 118140960795 + 2705822 * 2 ^ 59
def prefixEnd_2705822 : Nat := 4983230072969 + 3 ^ 40 * 2705822 * 2
def baseEnd_2705822 : Nat := 926258167673345128454105

theorem tailTrace_2705822 : CollatzResearch.WordTrace tailWord_2705822 prefixEnd_2705822 926258167673345128454105 := by
  unfold tailWord_2705822
  simp only [CollatzResearch.WordTrace]
  refine ⟨12336179500409560806455965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65792957335517657634431813 12336179500409560806455965)
  ·
    refine ⟨4626067312653585302420987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12336179500409560806455965 4626067312653585302420987)
    ·
      refine ⟨6939100968980377953631481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4626067312653585302420987 6939100968980377953631481)
      ·
        refine ⟨5204325726735283465223611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6939100968980377953631481 5204325726735283465223611)
        ·
          refine ⟨7806488590102925197835417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204325726735283465223611 7806488590102925197835417)
          ·
            refine ⟨5854866442577193898376563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7806488590102925197835417 5854866442577193898376563)
            ·
              refine ⟨8782299663865790847564845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854866442577193898376563 8782299663865790847564845)
              ·
                refine ⟨3293362373949671567836817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8782299663865790847564845 3293362373949671567836817)
                ·
                  refine ⟨2470021780462253675877613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3293362373949671567836817 2470021780462253675877613)
                  ·
                    refine ⟨926258167673345128454105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470021780462253675877613 926258167673345128454105)
                    ·
                      rfl

theorem cell22_2705822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_2705822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705822 prefixEnd_2705822 := by exact prefixLift 2705822
  have htrace : WordTrace (prefixWord ++ tailWord_2705822) baseStart_2705822 baseEnd_2705822 := by
    simpa [prefixWord, tailWord_2705822, baseEnd_2705822] using wordTrace_append hprefix tailTrace_2705822
  have hstable : (prefixWord ++ tailWord_2705822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705822).length < 2 ^ (prefixWord ++ tailWord_2705822).sum := by decide
  have hdescent : baseEnd_2705822 < baseStart_2705822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705863 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 5]
def baseStart_2705863 : Nat := 118140960795 + 2705863 * 2 ^ 59
def prefixEnd_2705863 : Nat := 4983230072969 + 3 ^ 40 * 2705863 * 2
def baseEnd_2705863 : Nat := 308757400937078229392993

theorem tailTrace_2705863 : CollatzResearch.WordTrace tailWord_2705863 prefixEnd_2705863 308757400937078229392993 := by
  unfold tailWord_2705863
  simp only [CollatzResearch.WordTrace]
  refine ⟨98690931396127950453890243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65793954264085300302593495 98690931396127950453890243)
  ·
    refine ⟨148036397094191925680835365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98690931396127950453890243 148036397094191925680835365)
    ·
      refine ⟨27756824455160986065156631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148036397094191925680835365 27756824455160986065156631)
      ·
        refine ⟨41635236682741479097734947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27756824455160986065156631 41635236682741479097734947)
        ·
          refine ⟨62452855024112218646602421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41635236682741479097734947 62452855024112218646602421)
          ·
            refine ⟨5854955158510520498118977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62452855024112218646602421 5854955158510520498118977)
            ·
              refine ⟨4391216368882890373589233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5854955158510520498118977 4391216368882890373589233)
              ·
                refine ⟨3293412276662167780191925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4391216368882890373589233 3293412276662167780191925)
                ·
                  refine ⟨308757400937078229392993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3293412276662167780191925 308757400937078229392993)
                  ·
                    rfl

theorem cell22_2705863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 5].length) (baseStart_2705863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705863 prefixEnd_2705863 := by exact prefixLift 2705863
  have htrace : WordTrace (prefixWord ++ tailWord_2705863) baseStart_2705863 baseEnd_2705863 := by
    simpa [prefixWord, tailWord_2705863, baseEnd_2705863] using wordTrace_append hprefix tailTrace_2705863
  have hstable : (prefixWord ++ tailWord_2705863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705863).length < 2 ^ (prefixWord ++ tailWord_2705863).sum := by decide
  have hdescent : baseEnd_2705863 < baseStart_2705863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705910 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_2705910 : Nat := 118140960795 + 2705910 * 2 ^ 59
def prefixEnd_2705910 : Nat := 4983230072969 + 3 ^ 40 * 2705910 * 2
def baseEnd_2705910 : Nat := 926288291871742232253835

theorem tailTrace_2705910 : CollatzResearch.WordTrace tailWord_2705910 prefixEnd_2705910 926288291871742232253835 := by
  unfold tailWord_2705910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6168290351684854842553199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65795097084638451653900789 6168290351684854842553199)
  ·
    refine ⟨9252435527527282263829799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6168290351684854842553199 9252435527527282263829799)
    ·
      refine ⟨13878653291290923395744699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9252435527527282263829799 13878653291290923395744699)
      ·
        refine ⟨20817979936936385093617049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13878653291290923395744699 20817979936936385093617049)
        ·
          refine ⟨15613484952702288820212787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20817979936936385093617049 15613484952702288820212787)
          ·
            refine ⟨23420227429053433230319181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15613484952702288820212787 23420227429053433230319181)
            ·
              refine ⟨8782585285895037461369693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23420227429053433230319181 8782585285895037461369693)
              ·
                refine ⟨3293469482210639048013635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8782585285895037461369693 3293469482210639048013635)
                ·
                  refine ⟨4940204223315958572020453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3293469482210639048013635 4940204223315958572020453)
                  ·
                    refine ⟨926288291871742232253835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4940204223315958572020453 926288291871742232253835)
                    ·
                      rfl

theorem cell22_2705910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_2705910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705910 prefixEnd_2705910 := by exact prefixLift 2705910
  have htrace : WordTrace (prefixWord ++ tailWord_2705910) baseStart_2705910 baseEnd_2705910 := by
    simpa [prefixWord, tailWord_2705910, baseEnd_2705910] using wordTrace_append hprefix tailTrace_2705910
  have hstable : (prefixWord ++ tailWord_2705910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705910).length < 2 ^ (prefixWord ++ tailWord_2705910).sum := by decide
  have hdescent : baseEnd_2705910 < baseStart_2705910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705923 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 4, 3]
def baseStart_2705923 : Nat := 118140960795 + 2705923 * 2 ^ 59
def prefixEnd_2705923 : Nat := 4983230072969 + 3 ^ 40 * 2705923 * 2
def baseEnd_2705923 : Nat := 926292742037414531678795

theorem tailTrace_2705923 : CollatzResearch.WordTrace tailWord_2705923 prefixEnd_2705923 926292742037414531678795 := by
  unfold tailWord_2705923
  simp only [CollatzResearch.WordTrace]
  refine ⟨98693119775910580701074423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65795413183940387134049615 98693119775910580701074423)
  ·
    refine ⟨148039679663865871051611635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98693119775910580701074423 148039679663865871051611635)
    ·
      refine ⟨222059519495798806577417453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148039679663865871051611635 222059519495798806577417453)
      ·
        refine ⟨83272319810924552466531545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222059519495798806577417453 83272319810924552466531545)
        ·
          refine ⟨62454239858193414349898659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83272319810924552466531545 62454239858193414349898659)
          ·
            refine ⟨93681359787290121524847989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62454239858193414349898659 93681359787290121524847989)
            ·
              refine ⟨8782627480058448892954499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93681359787290121524847989 8782627480058448892954499)
              ·
                refine ⟨13173941220087673339431749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8782627480058448892954499 13173941220087673339431749)
                ·
                  refine ⟨2470113978766438751143453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13173941220087673339431749 2470113978766438751143453)
                  ·
                    refine ⟨926292742037414531678795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470113978766438751143453 926292742037414531678795)
                    ·
                      rfl

theorem cell22_2705923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 3].length) (baseStart_2705923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705923 prefixEnd_2705923 := by exact prefixLift 2705923
  have htrace : WordTrace (prefixWord ++ tailWord_2705923) baseStart_2705923 baseEnd_2705923 := by
    simpa [prefixWord, tailWord_2705923, baseEnd_2705923] using wordTrace_append hprefix tailTrace_2705923
  have hstable : (prefixWord ++ tailWord_2705923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705923).length < 2 ^ (prefixWord ++ tailWord_2705923).sum := by decide
  have hdescent : baseEnd_2705923 < baseStart_2705923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705951 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 1, 9]
def baseStart_2705951 : Nat := 118140960795 + 2705951 * 2 ^ 59
def prefixEnd_2705951 : Nat := 4983230072969 + 3 ^ 40 * 2705951 * 2
def baseEnd_2705951 : Nat := 926302327009631791978709

theorem tailTrace_2705951 : CollatzResearch.WordTrace tailWord_2705951 prefixEnd_2705951 926302327009631791978709 := by
  unfold tailWord_2705951
  simp only [CollatzResearch.WordTrace]
  refine ⟨98694141019809141483093707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65796094013206094322062471 98694141019809141483093707)
  ·
    refine ⟨148041211529713712224640561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98694141019809141483093707 148041211529713712224640561)
    ·
      refine ⟨111030908647285284168480421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148041211529713712224640561 111030908647285284168480421)
      ·
        refine ⟨20818295371365990781590079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111030908647285284168480421 20818295371365990781590079)
        ·
          refine ⟨31227443057048986172385119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20818295371365990781590079 31227443057048986172385119)
          ·
            refine ⟨46841164585573479258577679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31227443057048986172385119 46841164585573479258577679)
            ·
              refine ⟨70261746878360218887866519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46841164585573479258577679 70261746878360218887866519)
              ·
                refine ⟨105392620317540328331799779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70261746878360218887866519 105392620317540328331799779)
                ·
                  refine ⟨158088930476310492497699669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105392620317540328331799779 158088930476310492497699669)
                  ·
                    refine ⟨926302327009631791978709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 158088930476310492497699669 926302327009631791978709)
                    ·
                      rfl

theorem cell22_2705951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_2705951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705951 prefixEnd_2705951 := by exact prefixLift 2705951
  have htrace : WordTrace (prefixWord ++ tailWord_2705951) baseStart_2705951 baseEnd_2705951 := by
    simpa [prefixWord, tailWord_2705951, baseEnd_2705951] using wordTrace_append hprefix tailTrace_2705951
  have hstable : (prefixWord ++ tailWord_2705951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705951).length < 2 ^ (prefixWord ++ tailWord_2705951).sum := by decide
  have hdescent : baseEnd_2705951 < baseStart_2705951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705968 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 5, 3]
def baseStart_2705968 : Nat := 118140960795 + 2705968 * 2 ^ 59
def prefixEnd_2705968 : Nat := 4983230072969 + 3 ^ 40 * 2705968 * 2
def baseEnd_2705968 : Nat := 926308146457049414303657

theorem tailTrace_2705968 : CollatzResearch.WordTrace tailWord_2705968 prefixEnd_2705968 926308146457049414303657 := by
  unfold tailWord_2705968
  simp only [CollatzResearch.WordTrace]
  refine ⟨49347380530373776693231279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65796507373831702257641705 49347380530373776693231279)
  ·
    refine ⟨74021070795560665039846919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49347380530373776693231279 74021070795560665039846919)
    ·
      refine ⟨111031606193340997559770379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74021070795560665039846919 111031606193340997559770379)
      ·
        refine ⟨166547409290011496339655569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111031606193340997559770379 166547409290011496339655569)
        ·
          refine ⟨124910556967508622254741677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166547409290011496339655569 124910556967508622254741677)
          ·
            refine ⟨46841458862815733345528129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124910556967508622254741677 46841458862815733345528129)
            ·
              refine ⟨35131094147111800009146097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46841458862815733345528129 35131094147111800009146097)
              ·
                refine ⟨26348320610333850006859573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35131094147111800009146097 26348320610333850006859573)
                ·
                  refine ⟨2470155057218798438143085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26348320610333850006859573 2470155057218798438143085)
                  ·
                    refine ⟨926308146457049414303657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470155057218798438143085 926308146457049414303657)
                    ·
                      rfl

theorem cell22_2705968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 5, 3].length) (baseStart_2705968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2705968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2705968 prefixEnd_2705968 := by exact prefixLift 2705968
  have htrace : WordTrace (prefixWord ++ tailWord_2705968) baseStart_2705968 baseEnd_2705968 := by
    simpa [prefixWord, tailWord_2705968, baseEnd_2705968] using wordTrace_append hprefix tailTrace_2705968
  have hstable : (prefixWord ++ tailWord_2705968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705968).length < 2 ^ (prefixWord ++ tailWord_2705968).sum := by decide
  have hdescent : baseEnd_2705968 < baseStart_2705968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706073 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 1, 6]
def baseStart_2706073 : Nat := 118140960795 + 2706073 * 2 ^ 59
def prefixEnd_2706073 : Nat := 4983230072969 + 3 ^ 40 * 2706073 * 2
def baseEnd_2706073 : Nat := 926344090102864140428335

theorem tailTrace_2706073 : CollatzResearch.WordTrace tailWord_2706073 prefixEnd_2706073 926344090102864140428335 := by
  unfold tailWord_2706073
  simp only [CollatzResearch.WordTrace]
  refine ⟨98698590725367156319034873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65799060483578104212689915 98698590725367156319034873)
  ·
    refine ⟨74023943044025367239276155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98698590725367156319034873 74023943044025367239276155)
    ·
      refine ⟨111035914566038050858914233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74023943044025367239276155 111035914566038050858914233)
      ·
        refine ⟨83276935924528538144185675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111035914566038050858914233 83276935924528538144185675)
        ·
          refine ⟨124915403886792807216278513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83276935924528538144185675 124915403886792807216278513)
          ·
            refine ⟨93686552915094605412208885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124915403886792807216278513 93686552915094605412208885)
            ·
              refine ⟨8783114335790119257394583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93686552915094605412208885 8783114335790119257394583)
              ·
                refine ⟨13174671503685178886091875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8783114335790119257394583 13174671503685178886091875)
                ·
                  refine ⟨19762007255527768329137813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13174671503685178886091875 19762007255527768329137813)
                  ·
                    refine ⟨926344090102864140428335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19762007255527768329137813 926344090102864140428335)
                    ·
                      rfl

theorem cell22_2706073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_2706073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706073 prefixEnd_2706073 := by exact prefixLift 2706073
  have htrace : WordTrace (prefixWord ++ tailWord_2706073) baseStart_2706073 baseEnd_2706073 := by
    simpa [prefixWord, tailWord_2706073, baseEnd_2706073] using wordTrace_append hprefix tailTrace_2706073
  have hstable : (prefixWord ++ tailWord_2706073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706073).length < 2 ^ (prefixWord ++ tailWord_2706073).sum := by decide
  have hdescent : baseEnd_2706073 < baseStart_2706073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706094 : List Nat := [4, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_2706094 : Nat := 118140960795 + 2706094 * 2 ^ 59
def prefixEnd_2706094 : Nat := 4983230072969 + 3 ^ 40 * 2706094 * 2
def baseEnd_2706094 : Nat := 308783759610675695217757

theorem tailTrace_2706094 : CollatzResearch.WordTrace tailWord_2706094 prefixEnd_2706094 308783759610675695217757 := by
  unfold tailWord_2706094
  simp only [CollatzResearch.WordTrace]
  refine ⟨12337419582286384613193667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65799571105527384603699557 12337419582286384613193667)
  ·
    refine ⟨18506129373429576919790501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12337419582286384613193667 18506129373429576919790501)
    ·
      refine ⟨3469899257518045672460719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18506129373429576919790501 3469899257518045672460719)
      ·
        refine ⟨5204848886277068508691079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3469899257518045672460719 5204848886277068508691079)
        ·
          refine ⟨7807273329415602763036619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204848886277068508691079 7807273329415602763036619)
          ·
            refine ⟨11710909994123404144554929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7807273329415602763036619 11710909994123404144554929)
            ·
              refine ⟨8783182495592553108416197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11710909994123404144554929 8783182495592553108416197)
              ·
                refine ⟨1646846717923603707828037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8783182495592553108416197 1646846717923603707828037)
                ·
                  refine ⟨308783759610675695217757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1646846717923603707828037 308783759610675695217757)
                  ·
                    rfl

theorem cell22_2706094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_2706094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706094 prefixEnd_2706094 := by exact prefixLift 2706094
  have htrace : WordTrace (prefixWord ++ tailWord_2706094) baseStart_2706094 baseEnd_2706094 := by
    simpa [prefixWord, tailWord_2706094, baseEnd_2706094] using wordTrace_append hprefix tailTrace_2706094
  have hstable : (prefixWord ++ tailWord_2706094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706094).length < 2 ^ (prefixWord ++ tailWord_2706094).sum := by decide
  have hdescent : baseEnd_2706094 < baseStart_2706094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706109 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_2706109 : Nat := 118140960795 + 2706109 * 2 ^ 59
def prefixEnd_2706109 : Nat := 4983230072969 + 3 ^ 40 * 2706109 * 2
def baseEnd_2706109 : Nat := 926356413638572046528225

theorem tailTrace_2706109 : CollatzResearch.WordTrace tailWord_2706109 prefixEnd_2706109 926356413638572046528225 := by
  unfold tailWord_2706109
  simp only [CollatzResearch.WordTrace]
  refine ⟨98699903753236734467345381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65799935835491156311563587 98699903753236734467345381)
  ·
    refine ⟨18506231953731887712627259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98699903753236734467345381 18506231953731887712627259)
    ·
      refine ⟨27759347930597831568940889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18506231953731887712627259 27759347930597831568940889)
      ·
        refine ⟨20819510947948373676705667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27759347930597831568940889 20819510947948373676705667)
        ·
          refine ⟨31229266421922560515058501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20819510947948373676705667 31229266421922560515058501)
          ·
            refine ⟨5855487454110480096573469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31229266421922560515058501 5855487454110480096573469)
            ·
              refine ⟨2195807795291430036215051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5855487454110480096573469 2195807795291430036215051)
              ·
                refine ⟨3293711692937145054322577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195807795291430036215051 3293711692937145054322577)
                ·
                  refine ⟨2470283769702858790741933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3293711692937145054322577 2470283769702858790741933)
                  ·
                    refine ⟨926356413638572046528225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470283769702858790741933 926356413638572046528225)
                    ·
                      rfl

theorem cell22_2706109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_2706109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706109 prefixEnd_2706109 := by exact prefixLift 2706109
  have htrace : WordTrace (prefixWord ++ tailWord_2706109) baseStart_2706109 baseEnd_2706109 := by
    simpa [prefixWord, tailWord_2706109, baseEnd_2706109] using wordTrace_append hprefix tailTrace_2706109
  have hstable : (prefixWord ++ tailWord_2706109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706109).length < 2 ^ (prefixWord ++ tailWord_2706109).sum := by decide
  have hdescent : baseEnd_2706109 < baseStart_2706109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706122 : List Nat := [3, 1, 2, 1, 4, 3, 2, 6]
def baseStart_2706122 : Nat := 118140960795 + 2706122 * 2 ^ 59
def prefixEnd_2706122 : Nat := 4983230072969 + 3 ^ 40 * 2706122 * 2
def baseEnd_2706122 : Nat := 102928984867138260661465

theorem tailTrace_2706122 : CollatzResearch.WordTrace tailWord_2706122 prefixEnd_2706122 102928984867138260661465 := by
  unfold tailWord_2706122
  simp only [CollatzResearch.WordTrace]
  refine ⟨24675094475547409421892155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65800251934793091791712413 24675094475547409421892155)
  ·
    refine ⟨37012641713321114132838233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24675094475547409421892155 37012641713321114132838233)
    ·
      refine ⟨27759481284990835599628675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37012641713321114132838233 27759481284990835599628675)
      ·
        refine ⟨41639221927486253399443013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27759481284990835599628675 41639221927486253399443013)
        ·
          refine ⟨7807354111403672512395565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41639221927486253399443013 7807354111403672512395565)
          ·
            refine ⟨2927757791776377192148337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7807354111403672512395565 2927757791776377192148337)
            ·
              refine ⟨2195818343832282894111253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2927757791776377192148337 2195818343832282894111253)
              ·
                refine ⟨102928984867138260661465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2195818343832282894111253 102928984867138260661465)
                ·
                  rfl

theorem cell22_2706122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_2706122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706122 prefixEnd_2706122 := by exact prefixLift 2706122
  have htrace : WordTrace (prefixWord ++ tailWord_2706122) baseStart_2706122 baseEnd_2706122 := by
    simpa [prefixWord, tailWord_2706122, baseEnd_2706122] using wordTrace_append hprefix tailTrace_2706122
  have hstable : (prefixWord ++ tailWord_2706122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706122).length < 2 ^ (prefixWord ++ tailWord_2706122).sum := by decide
  have hdescent : baseEnd_2706122 < baseStart_2706122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706163 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 2, 8]
def baseStart_2706163 : Nat := 118140960795 + 2706163 * 2 ^ 59
def prefixEnd_2706163 : Nat := 4983230072969 + 3 ^ 40 * 2706163 * 2
def baseEnd_2706163 : Nat := 926374898942133905678059

theorem tailTrace_2706163 : CollatzResearch.WordTrace tailWord_2706163 prefixEnd_2706163 926374898942133905678059 := by
  unfold tailWord_2706163
  simp only [CollatzResearch.WordTrace]
  refine ⟨98701873295041101689811143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65801248863360734459874095 98701873295041101689811143)
  ·
    refine ⟨148052809942561652534716715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98701873295041101689811143 148052809942561652534716715)
    ·
      refine ⟨222079214913842478802075073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148052809942561652534716715 222079214913842478802075073)
      ·
        refine ⟨166559411185381859101556305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222079214913842478802075073 166559411185381859101556305)
        ·
          refine ⟨124919558389036394326167229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166559411185381859101556305 124919558389036394326167229)
          ·
            refine ⟨46844834395888647872312711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124919558389036394326167229 46844834395888647872312711)
            ·
              refine ⟨70267251593832971808469067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46844834395888647872312711 70267251593832971808469067)
              ·
                refine ⟨105400877390749457712703601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70267251593832971808469067 105400877390749457712703601)
                ·
                  refine ⟨79050658043062093284527701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105400877390749457712703601 79050658043062093284527701)
                  ·
                    refine ⟨926374898942133905678059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79050658043062093284527701 926374898942133905678059)
                    ·
                      rfl

theorem cell22_2706163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_2706163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706163 prefixEnd_2706163 := by exact prefixLift 2706163
  have htrace : WordTrace (prefixWord ++ tailWord_2706163) baseStart_2706163 baseEnd_2706163 := by
    simpa [prefixWord, tailWord_2706163, baseEnd_2706163] using wordTrace_append hprefix tailTrace_2706163
  have hstable : (prefixWord ++ tailWord_2706163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706163).length < 2 ^ (prefixWord ++ tailWord_2706163).sum := by decide
  have hdescent : baseEnd_2706163 < baseStart_2706163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706205 : List Nat := [1, 4, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_2706205 : Nat := 118140960795 + 2706205 * 2 ^ 59
def prefixEnd_2706205 : Nat := 4983230072969 + 3 ^ 40 * 2706205 * 2
def baseEnd_2706205 : Nat := 926389276400459796127931

theorem tailTrace_2706205 : CollatzResearch.WordTrace tailWord_2706205 prefixEnd_2706205 926389276400459796127931 := by
  unfold tailWord_2706205
  simp only [CollatzResearch.WordTrace]
  refine ⟨98703405160888942862840069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65802270107259295241893379 98703405160888942862840069)
  ·
    refine ⟨18506888467666676786782513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98703405160888942862840069 18506888467666676786782513)
    ·
      refine ⟨13880166350750007590086885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18506888467666676786782513 13880166350750007590086885)
      ·
        refine ⟨2602531190765626423141291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13880166350750007590086885 2602531190765626423141291)
        ·
          refine ⟨3903796786148439634711937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602531190765626423141291 3903796786148439634711937)
          ·
            refine ⟨2927847589611329726033953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3903796786148439634711937 2927847589611329726033953)
            ·
              refine ⟨2195885692208497294525465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2927847589611329726033953 2195885692208497294525465)
              ·
                refine ⟨1646914269156372970894099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2195885692208497294525465 1646914269156372970894099)
                ·
                  refine ⟨2470371403734559456341149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646914269156372970894099 2470371403734559456341149)
                  ·
                    refine ⟨926389276400459796127931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470371403734559456341149 926389276400459796127931)
                    ·
                      rfl

theorem cell22_2706205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_2706205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706205 prefixEnd_2706205 := by exact prefixLift 2706205
  have htrace : WordTrace (prefixWord ++ tailWord_2706205) baseStart_2706205 baseEnd_2706205 := by
    simpa [prefixWord, tailWord_2706205, baseEnd_2706205] using wordTrace_append hprefix tailTrace_2706205
  have hstable : (prefixWord ++ tailWord_2706205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706205).length < 2 ^ (prefixWord ++ tailWord_2706205).sum := by decide
  have hdescent : baseEnd_2706205 < baseStart_2706205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706225 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_2706225 : Nat := 118140960795 + 2706225 * 2 ^ 59
def prefixEnd_2706225 : Nat := 4983230072969 + 3 ^ 40 * 2706225 * 2
def baseEnd_2706225 : Nat := 926396122809186410627869

theorem tailTrace_2706225 : CollatzResearch.WordTrace tailWord_2706225 prefixEnd_2706225 926396122809186410627869 := by
  unfold tailWord_2706225
  simp only [CollatzResearch.WordTrace]
  refine ⟨98704134620816486278568129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65802756413877657519045419 98704134620816486278568129)
  ·
    refine ⟨74028100965612364708926097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98704134620816486278568129 74028100965612364708926097)
    ·
      refine ⟨55521075724209273531694573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74028100965612364708926097 55521075724209273531694573)
      ·
        refine ⟨20820403396578477574385465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55521075724209273531694573 20820403396578477574385465)
        ·
          refine ⟨15615302547433858180789099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20820403396578477574385465 15615302547433858180789099)
          ·
            refine ⟨23422953821150787271183649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15615302547433858180789099 23422953821150787271183649)
            ·
              refine ⟨17567215365863090453387737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23422953821150787271183649 17567215365863090453387737)
              ·
                refine ⟨13175411524397317840040803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17567215365863090453387737 13175411524397317840040803)
                ·
                  refine ⟨19763117286595976760061205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13175411524397317840040803 19763117286595976760061205)
                  ·
                    refine ⟨926396122809186410627869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19763117286595976760061205 926396122809186410627869)
                    ·
                      rfl

theorem cell22_2706225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_2706225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706225 prefixEnd_2706225 := by exact prefixLift 2706225
  have htrace : WordTrace (prefixWord ++ tailWord_2706225) baseStart_2706225 baseEnd_2706225 := by
    simpa [prefixWord, tailWord_2706225, baseEnd_2706225] using wordTrace_append hprefix tailTrace_2706225
  have hstable : (prefixWord ++ tailWord_2706225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706225).length < 2 ^ (prefixWord ++ tailWord_2706225).sum := by decide
  have hdescent : baseEnd_2706225 < baseStart_2706225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706227 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 1, 5]
def baseStart_2706227 : Nat := 118140960795 + 2706227 * 2 ^ 59
def prefixEnd_2706227 : Nat := 4983230072969 + 3 ^ 40 * 2706227 * 2
def baseEnd_2706227 : Nat := 926396807450059072077863

theorem tailTrace_2706227 : CollatzResearch.WordTrace tailWord_2706227 prefixEnd_2706227 926396807450059072077863 := by
  unfold tailWord_2706227
  simp only [CollatzResearch.WordTrace]
  refine ⟨98704207566809240620140935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65802805044539493746760623 98704207566809240620140935)
  ·
    refine ⟨148056311350213860930211403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98704207566809240620140935 148056311350213860930211403)
    ·
      refine ⟨222084467025320791395317105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148056311350213860930211403 222084467025320791395317105)
      ·
        refine ⟨166563350268990593546487829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222084467025320791395317105 166563350268990593546487829)
        ·
          refine ⟨7807657043858934072491617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 166563350268990593546487829 7807657043858934072491617)
          ·
            refine ⟨5855742782894200554368713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7807657043858934072491617 5855742782894200554368713)
            ·
              refine ⟨4391807087170650415776535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5855742782894200554368713 4391807087170650415776535)
              ·
                refine ⟨6587710630755975623664803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4391807087170650415776535 6587710630755975623664803)
                ·
                  refine ⟨9881565946133963435497205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6587710630755975623664803 9881565946133963435497205)
                  ·
                    refine ⟨926396807450059072077863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9881565946133963435497205 926396807450059072077863)
                    ·
                      rfl

theorem cell22_2706227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 5].length) (baseStart_2706227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706227 prefixEnd_2706227 := by exact prefixLift 2706227
  have htrace : WordTrace (prefixWord ++ tailWord_2706227) baseStart_2706227 baseEnd_2706227 := by
    simpa [prefixWord, tailWord_2706227, baseEnd_2706227] using wordTrace_append hprefix tailTrace_2706227
  have hstable : (prefixWord ++ tailWord_2706227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706227).length < 2 ^ (prefixWord ++ tailWord_2706227).sum := by decide
  have hdescent : baseEnd_2706227 < baseStart_2706227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706300 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_2706300 : Nat := 118140960795 + 2706300 * 2 ^ 59
def prefixEnd_2706300 : Nat := 4983230072969 + 3 ^ 40 * 2706300 * 2
def baseEnd_2706300 : Nat := 926421796841911215002639

theorem tailTrace_2706300 : CollatzResearch.WordTrace tailWord_2706300 prefixEnd_2706300 926421796841911215002639 := by
  unfold tailWord_2706300
  simp only [CollatzResearch.WordTrace]
  refine ⟨49353435047772387043774177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65804580063696516058365569 49353435047772387043774177)
  ·
    refine ⟨37015076285829290282830633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49353435047772387043774177 37015076285829290282830633)
    ·
      refine ⟨27761307214371967712122975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37015076285829290282830633 27761307214371967712122975)
      ·
        refine ⟨41641960821557951568184463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27761307214371967712122975 41641960821557951568184463)
        ·
          refine ⟨62462941232336927352276695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41641960821557951568184463 62462941232336927352276695)
          ·
            refine ⟨93694411848505391028415043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62462941232336927352276695 93694411848505391028415043)
            ·
              refine ⟨140541617772758086542622565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93694411848505391028415043 140541617772758086542622565)
              ·
                refine ⟨26351553332392141226741731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140541617772758086542622565 26351553332392141226741731)
                ·
                  refine ⟨39527329998588211840112597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26351553332392141226741731 39527329998588211840112597)
                  ·
                    refine ⟨926421796841911215002639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39527329998588211840112597 926421796841911215002639)
                    ·
                      rfl

theorem cell22_2706300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_2706300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706300 prefixEnd_2706300 := by exact prefixLift 2706300
  have htrace : WordTrace (prefixWord ++ tailWord_2706300) baseStart_2706300 baseEnd_2706300 := by
    simpa [prefixWord, tailWord_2706300, baseEnd_2706300] using wordTrace_append hprefix tailTrace_2706300
  have hstable : (prefixWord ++ tailWord_2706300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706300).length < 2 ^ (prefixWord ++ tailWord_2706300).sum := by decide
  have hdescent : baseEnd_2706300 < baseStart_2706300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706362 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_2706362 : Nat := 118140960795 + 2706362 * 2 ^ 59
def prefixEnd_2706362 : Nat := 4983230072969 + 3 ^ 40 * 2706362 * 2
def baseEnd_2706362 : Nat := 926443020708963719952449

theorem tailTrace_2706362 : CollatzResearch.WordTrace tailWord_2706362 prefixEnd_2706362 926443020708963719952449 := by
  unfold tailWord_2706362
  simp only [CollatzResearch.WordTrace]
  refine ⟨24677282855330039669076335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65806087614213439117536893 24677282855330039669076335)
  ·
    refine ⟨37015924282995059503614503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24677282855330039669076335 37015924282995059503614503)
    ·
      refine ⟨55523886424492589255421755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37015924282995059503614503 55523886424492589255421755)
      ·
        refine ⟨83285829636738883883132633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55523886424492589255421755 83285829636738883883132633)
        ·
          refine ⟨62464372227554162912349475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83285829636738883883132633 62464372227554162912349475)
          ·
            refine ⟨93696558341331244368524213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62464372227554162912349475 93696558341331244368524213)
            ·
              refine ⟨8784052344499804159549145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93696558341331244368524213 8784052344499804159549145)
              ·
                refine ⟨6588039258374853119661859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8784052344499804159549145 6588039258374853119661859)
                ·
                  refine ⟨9882058887562279679492789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6588039258374853119661859 9882058887562279679492789)
                  ·
                    refine ⟨926443020708963719952449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9882058887562279679492789 926443020708963719952449)
                    ·
                      rfl

theorem cell22_2706362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_2706362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706362 prefixEnd_2706362 := by exact prefixLift 2706362
  have htrace : WordTrace (prefixWord ++ tailWord_2706362) baseStart_2706362 baseEnd_2706362 := by
    simpa [prefixWord, tailWord_2706362, baseEnd_2706362] using wordTrace_append hprefix tailTrace_2706362
  have hstable : (prefixWord ++ tailWord_2706362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706362).length < 2 ^ (prefixWord ++ tailWord_2706362).sum := by decide
  have hdescent : baseEnd_2706362 < baseStart_2706362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706366 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_2706366 : Nat := 118140960795 + 2706366 * 2 ^ 59
def prefixEnd_2706366 : Nat := 4983230072969 + 3 ^ 40 * 2706366 * 2
def baseEnd_2706366 : Nat := 926444389990709042852437

theorem tailTrace_2706366 : CollatzResearch.WordTrace tailWord_2706366 prefixEnd_2706366 926444389990709042852437 := by
  unfold tailWord_2706366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12338659664163208419931369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65806184875537111572967301 12338659664163208419931369)
  ·
    refine ⟨9253994748122406314948527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12338659664163208419931369 9253994748122406314948527)
    ·
      refine ⟨13880992122183609472422791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9253994748122406314948527 13880992122183609472422791)
      ·
        refine ⟨20821488183275414208634187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13880992122183609472422791 20821488183275414208634187)
        ·
          refine ⟨31232232274913121312951281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20821488183275414208634187 31232232274913121312951281)
          ·
            refine ⟨23424174206184840984713461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31232232274913121312951281 23424174206184840984713461)
            ·
              refine ⟨2196016331829828842316887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23424174206184840984713461 2196016331829828842316887)
              ·
                refine ⟨3294024497744743263475331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2196016331829828842316887 3294024497744743263475331)
                ·
                  refine ⟨4941036746617114895212997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294024497744743263475331 4941036746617114895212997)
                  ·
                    refine ⟨926444389990709042852437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4941036746617114895212997 926444389990709042852437)
                    ·
                      rfl

theorem cell22_2706366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_2706366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706366 prefixEnd_2706366 := by exact prefixLift 2706366
  have htrace : WordTrace (prefixWord ++ tailWord_2706366) baseStart_2706366 baseEnd_2706366 := by
    simpa [prefixWord, tailWord_2706366, baseEnd_2706366] using wordTrace_append hprefix tailTrace_2706366
  have hstable : (prefixWord ++ tailWord_2706366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706366).length < 2 ^ (prefixWord ++ tailWord_2706366).sum := by decide
  have hdescent : baseEnd_2706366 < baseStart_2706366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706374 : List Nat := [6, 1, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2706374 : Nat := 118140960795 + 2706374 * 2 ^ 59
def prefixEnd_2706374 : Nat := 4983230072969 + 3 ^ 40 * 2706374 * 2
def baseEnd_2706374 : Nat := 926447128554199688652413

theorem tailTrace_2706374 : CollatzResearch.WordTrace tailWord_2706374 prefixEnd_2706374 926447128554199688652413 := by
  unfold tailWord_2706374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3084674034289896397679443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65806379398184456483828117 3084674034289896397679443)
  ·
    refine ⟨4627011051434844596519165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3084674034289896397679443 4627011051434844596519165)
    ·
      refine ⟨1735129144288066723694687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4627011051434844596519165 1735129144288066723694687)
      ·
        refine ⟨2602693716432100085542031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735129144288066723694687 2602693716432100085542031)
        ·
          refine ⟨3904040574648150128313047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602693716432100085542031 3904040574648150128313047)
          ·
            refine ⟨5856060861972225192469571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3904040574648150128313047 5856060861972225192469571)
            ·
              refine ⟨8784091292958337788704357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856060861972225192469571 8784091292958337788704357)
              ·
                refine ⟨1647017117429688335382067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8784091292958337788704357 1647017117429688335382067)
                ·
                  refine ⟨2470525676144532503073101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647017117429688335382067 2470525676144532503073101)
                  ·
                    refine ⟨926447128554199688652413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470525676144532503073101 926447128554199688652413)
                    ·
                      rfl

theorem cell22_2706374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2706374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706374 prefixEnd_2706374 := by exact prefixLift 2706374
  have htrace : WordTrace (prefixWord ++ tailWord_2706374) baseStart_2706374 baseEnd_2706374 := by
    simpa [prefixWord, tailWord_2706374, baseEnd_2706374] using wordTrace_append hprefix tailTrace_2706374
  have hstable : (prefixWord ++ tailWord_2706374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706374).length < 2 ^ (prefixWord ++ tailWord_2706374).sum := by decide
  have hdescent : baseEnd_2706374 < baseStart_2706374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706379 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 2, 3]
def baseStart_2706379 : Nat := 118140960795 + 2706379 * 2 ^ 59
def prefixEnd_2706379 : Nat := 4983230072969 + 3 ^ 40 * 2706379 * 2
def baseEnd_2706379 : Nat := 926448840156381342277397

theorem tailTrace_2706379 : CollatzResearch.WordTrace tailWord_2706379 prefixEnd_2706379 926448840156381342277397 := by
  unfold tailWord_2706379
  simp only [CollatzResearch.WordTrace]
  refine ⟨98709751462258570579674191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65806500974839047053116127 98709751462258570579674191)
  ·
    refine ⟨148064627193387855869511287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98709751462258570579674191 148064627193387855869511287)
    ·
      refine ⟨222096940790081783804266931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148064627193387855869511287 222096940790081783804266931)
      ·
        refine ⟨333145411185122675706400397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222096940790081783804266931 333145411185122675706400397)
        ·
          refine ⟨124929529194421003389900149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333145411185122675706400397 124929529194421003389900149)
          ·
            refine ⟨11712143361976969067803139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124929529194421003389900149 11712143361976969067803139)
            ·
              refine ⟨17568215042965453601704709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11712143361976969067803139 17568215042965453601704709)
              ·
                refine ⟨3294040320556022550319633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17568215042965453601704709 3294040320556022550319633)
                ·
                  refine ⟨2470530240417016912739725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3294040320556022550319633 2470530240417016912739725)
                  ·
                    refine ⟨926448840156381342277397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470530240417016912739725 926448840156381342277397)
                    ·
                      rfl

theorem cell22_2706379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 3].length) (baseStart_2706379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706379 prefixEnd_2706379 := by exact prefixLift 2706379
  have htrace : WordTrace (prefixWord ++ tailWord_2706379) baseStart_2706379 baseEnd_2706379 := by
    simpa [prefixWord, tailWord_2706379, baseEnd_2706379] using wordTrace_append hprefix tailTrace_2706379
  have hstable : (prefixWord ++ tailWord_2706379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706379).length < 2 ^ (prefixWord ++ tailWord_2706379).sum := by decide
  have hdescent : baseEnd_2706379 < baseStart_2706379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706392 : List Nat := [2, 1, 2, 2, 2, 3, 3, 7]
def baseStart_2706392 : Nat := 118140960795 + 2706392 * 2 ^ 59
def prefixEnd_2706392 : Nat := 4983230072969 + 3 ^ 40 * 2706392 * 2
def baseEnd_2706392 : Nat := 102939254480228182411373

theorem tailTrace_2706392 : CollatzResearch.WordTrace tailWord_2706392 prefixEnd_2706392 102939254480228182411373 := by
  unfold tailWord_2706392
  simp only [CollatzResearch.WordTrace]
  refine ⟨49355112805605736899948715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65806817074140982533264953 49355112805605736899948715)
  ·
    refine ⟨74032669208408605349923073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49355112805605736899948715 74032669208408605349923073)
    ·
      refine ⟨55524501906306454012442305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74032669208408605349923073 55524501906306454012442305)
      ·
        refine ⟨41643376429729840509331729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55524501906306454012442305 41643376429729840509331729)
        ·
          refine ⟨31232532322297380381998797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41643376429729840509331729 31232532322297380381998797)
          ·
            refine ⟨11712199620861517643249549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31232532322297380381998797 11712199620861517643249549)
            ·
              refine ⟨4392074857823069116218581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11712199620861517643249549 4392074857823069116218581)
              ·
                refine ⟨102939254480228182411373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4392074857823069116218581 102939254480228182411373)
                ·
                  rfl

theorem cell22_2706392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 7].length) (baseStart_2706392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706392 prefixEnd_2706392 := by exact prefixLift 2706392
  have htrace : WordTrace (prefixWord ++ tailWord_2706392) baseStart_2706392 baseEnd_2706392 := by
    simpa [prefixWord, tailWord_2706392, baseEnd_2706392] using wordTrace_append hprefix tailTrace_2706392
  have hstable : (prefixWord ++ tailWord_2706392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706392).length < 2 ^ (prefixWord ++ tailWord_2706392).sum := by decide
  have hdescent : baseEnd_2706392 < baseStart_2706392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706430 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2706430 : Nat := 118140960795 + 2706430 * 2 ^ 59
def prefixEnd_2706430 : Nat := 4983230072969 + 3 ^ 40 * 2706430 * 2
def baseEnd_2706430 : Nat := 926466298498634209252241

theorem tailTrace_2706430 : CollatzResearch.WordTrace tailWord_2706430 prefixEnd_2706430 926466298498634209252241 := by
  unfold tailWord_2706430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12338951448134225786222593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65807741056715870859853829 12338951448134225786222593)
  ·
    refine ⟨9254213586100669339666945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12338951448134225786222593 9254213586100669339666945)
    ·
      refine ⟨6940660189575502004750209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9254213586100669339666945 6940660189575502004750209)
      ·
        refine ⟨5205495142181626503562657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6940660189575502004750209 5205495142181626503562657)
        ·
          refine ⟨3904121356636219877671993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5205495142181626503562657 3904121356636219877671993)
          ·
            refine ⟨2928091017477164908253995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3904121356636219877671993 2928091017477164908253995)
            ·
              refine ⟨4392136526215747362380993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928091017477164908253995 4392136526215747362380993)
              ·
                refine ⟨3294102394661810521785745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4392136526215747362380993 3294102394661810521785745)
                ·
                  refine ⟨2470576795996357891339309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3294102394661810521785745 2470576795996357891339309)
                  ·
                    refine ⟨926466298498634209252241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470576795996357891339309 926466298498634209252241)
                    ·
                      rfl

theorem cell22_2706430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2706430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706430 prefixEnd_2706430 := by exact prefixLift 2706430
  have htrace : WordTrace (prefixWord ++ tailWord_2706430) baseStart_2706430 baseEnd_2706430 := by
    simpa [prefixWord, tailWord_2706430, baseEnd_2706430] using wordTrace_append hprefix tailTrace_2706430
  have hstable : (prefixWord ++ tailWord_2706430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706430).length < 2 ^ (prefixWord ++ tailWord_2706430).sum := by decide
  have hdescent : baseEnd_2706430 < baseStart_2706430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706437 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 7]
def baseStart_2706437 : Nat := 118140960795 + 2706437 * 2 ^ 59
def prefixEnd_2706437 : Nat := 4983230072969 + 3 ^ 40 * 2706437 * 2
def baseEnd_2706437 : Nat := 308822898247229508109073

theorem tailTrace_2706437 : CollatzResearch.WordTrace tailWord_2706437 prefixEnd_2706437 308822898247229508109073 := by
  unfold tailWord_2706437
  simp only [CollatzResearch.WordTrace]
  refine ⟨98711866896048446485285565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65807911264032297656857043 98711866896048446485285565)
  ·
    refine ⟨37016950086018167431982087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98711866896048446485285565 37016950086018167431982087)
    ·
      refine ⟨55525425129027251147973131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37016950086018167431982087 55525425129027251147973131)
      ·
        refine ⟨83288137693540876721959697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55525425129027251147973131 83288137693540876721959697)
        ·
          refine ⟨62466103270155657541469773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83288137693540876721959697 62466103270155657541469773)
          ·
            refine ⟨23424788726308371578051165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62466103270155657541469773 23424788726308371578051165)
            ·
              refine ⟨8784295772365639341769187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23424788726308371578051165 8784295772365639341769187)
              ·
                refine ⟨13176443658548459012653781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8784295772365639341769187 13176443658548459012653781)
                ·
                  refine ⟨308822898247229508109073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13176443658548459012653781 308822898247229508109073)
                  ·
                    rfl

theorem cell22_2706437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_2706437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706437 prefixEnd_2706437 := by exact prefixLift 2706437
  have htrace : WordTrace (prefixWord ++ tailWord_2706437) baseStart_2706437 baseEnd_2706437 := by
    simpa [prefixWord, tailWord_2706437, baseEnd_2706437] using wordTrace_append hprefix tailTrace_2706437
  have hstable : (prefixWord ++ tailWord_2706437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706437).length < 2 ^ (prefixWord ++ tailWord_2706437).sum := by decide
  have hdescent : baseEnd_2706437 < baseStart_2706437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706512 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_2706512 : Nat := 118140960795 + 2706512 * 2 ^ 59
def prefixEnd_2706512 : Nat := 4983230072969 + 3 ^ 40 * 2706512 * 2
def baseEnd_2706512 : Nat := 926494368774413328701989

theorem tailTrace_2706512 : CollatzResearch.WordTrace tailWord_2706512 prefixEnd_2706512 926494368774413328701989 := by
  unfold tailWord_2706512
  simp only [CollatzResearch.WordTrace]
  refine ⟨49357301185388367147132895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65809734913851156196177193 49357301185388367147132895)
  ·
    refine ⟨74035951778082550720699343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49357301185388367147132895 74035951778082550720699343)
    ·
      refine ⟨111053927667123826081049015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74035951778082550720699343 111053927667123826081049015)
      ·
        refine ⟨166580891500685739121573523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111053927667123826081049015 166580891500685739121573523)
        ·
          refine ⟨249871337251028608682360285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166580891500685739121573523 249871337251028608682360285)
          ·
            refine ⟨93701751469135728255885107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249871337251028608682360285 93701751469135728255885107)
            ·
              refine ⟨140552627203703592383827661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93701751469135728255885107 140552627203703592383827661)
              ·
                refine ⟨52707235201388847143935373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140552627203703592383827661 52707235201388847143935373)
                ·
                  refine ⟨19765213200520817678975765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52707235201388847143935373 19765213200520817678975765)
                  ·
                    refine ⟨926494368774413328701989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19765213200520817678975765 926494368774413328701989)
                    ·
                      rfl

theorem cell22_2706512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_2706512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706512 prefixEnd_2706512 := by exact prefixLift 2706512
  have htrace : WordTrace (prefixWord ++ tailWord_2706512) baseStart_2706512 baseEnd_2706512 := by
    simpa [prefixWord, tailWord_2706512, baseEnd_2706512] using wordTrace_append hprefix tailTrace_2706512
  have hstable : (prefixWord ++ tailWord_2706512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706512).length < 2 ^ (prefixWord ++ tailWord_2706512).sum := by decide
  have hdescent : baseEnd_2706512 < baseStart_2706512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706527 : List Nat := [1, 1, 2, 3, 1, 1, 3, 10]
def baseStart_2706527 : Nat := 118140960795 + 2706527 * 2 ^ 59
def prefixEnd_2706527 : Nat := 4983230072969 + 3 ^ 40 * 2706527 * 2
def baseEnd_2706527 : Nat := 102944389286773143286327

theorem tailTrace_2706527 : CollatzResearch.WordTrace tailWord_2706527 prefixEnd_2706527 102944389286773143286327 := by
  unfold tailWord_2706527
  simp only [CollatzResearch.WordTrace]
  refine ⟨98715149465722391856061835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65810099643814927904041223 98715149465722391856061835)
  ·
    refine ⟨148072724198583587784092753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98715149465722391856061835 148072724198583587784092753)
    ·
      refine ⟨111054543148937690838069565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148072724198583587784092753 111054543148937690838069565)
      ·
        refine ⟨41645453680851634064276087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111054543148937690838069565 41645453680851634064276087)
        ·
          refine ⟨62468180521277451096414131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41645453680851634064276087 62468180521277451096414131)
          ·
            refine ⟨93702270781916176644621197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62468180521277451096414131 93702270781916176644621197)
            ·
              refine ⟨35138351543218566241732949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93702270781916176644621197 35138351543218566241732949)
              ·
                refine ⟨102944389286773143286327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35138351543218566241732949 102944389286773143286327)
                ·
                  rfl

theorem cell22_2706527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 10].length) (baseStart_2706527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706527 prefixEnd_2706527 := by exact prefixLift 2706527
  have htrace : WordTrace (prefixWord ++ tailWord_2706527) baseStart_2706527 baseEnd_2706527 := by
    simpa [prefixWord, tailWord_2706527, baseEnd_2706527] using wordTrace_append hprefix tailTrace_2706527
  have hstable : (prefixWord ++ tailWord_2706527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706527).length < 2 ^ (prefixWord ++ tailWord_2706527).sum := by decide
  have hdescent : baseEnd_2706527 < baseStart_2706527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706529 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 2, 4]
def baseStart_2706529 : Nat := 118140960795 + 2706529 * 2 ^ 59
def prefixEnd_2706529 : Nat := 4983230072969 + 3 ^ 40 * 2706529 * 2
def baseEnd_2706529 : Nat := 926500188221830951026937

theorem tailTrace_2706529 : CollatzResearch.WordTrace tailWord_2706529 prefixEnd_2706529 926500188221830951026937 := by
  unfold tailWord_2706529
  simp only [CollatzResearch.WordTrace]
  refine ⟨98715222411715146197634641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65810148274476764131756427 98715222411715146197634641)
  ·
    refine ⟨74036416808786359648225981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98715222411715146197634641 74036416808786359648225981)
    ·
      refine ⟨27763656303294884868084743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74036416808786359648225981 27763656303294884868084743)
      ·
        refine ⟨41645484454942327302127115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27763656303294884868084743 41645484454942327302127115)
        ·
          refine ⟨62468226682413490953190673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41645484454942327302127115 62468226682413490953190673)
          ·
            refine ⟨46851170011810118214893005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62468226682413490953190673 46851170011810118214893005)
            ·
              refine ⟨17569188754428794330584877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46851170011810118214893005 17569188754428794330584877)
              ·
                refine ⟨6588445782910797873969329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17569188754428794330584877 6588445782910797873969329)
                ·
                  refine ⟨4941334337183098405476997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6588445782910797873969329 4941334337183098405476997)
                  ·
                    refine ⟨926500188221830951026937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4941334337183098405476997 926500188221830951026937)
                    ·
                      rfl

theorem cell22_2706529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_2706529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706529 prefixEnd_2706529 := by exact prefixLift 2706529
  have htrace : WordTrace (prefixWord ++ tailWord_2706529) baseStart_2706529 baseEnd_2706529 := by
    simpa [prefixWord, tailWord_2706529, baseEnd_2706529] using wordTrace_append hprefix tailTrace_2706529
  have hstable : (prefixWord ++ tailWord_2706529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706529).length < 2 ^ (prefixWord ++ tailWord_2706529).sum := by decide
  have hdescent : baseEnd_2706529 < baseStart_2706529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706559 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 9, 3]
def baseStart_2706559 : Nat := 118140960795 + 2706559 * 2 ^ 59
def prefixEnd_2706559 : Nat := 4983230072969 + 3 ^ 40 * 2706559 * 2
def baseEnd_2706559 : Nat := 926510457834920872776845

theorem tailTrace_2706559 : CollatzResearch.WordTrace tailWord_2706559 prefixEnd_2706559 926510457834920872776845 := by
  unfold tailWord_2706559
  simp only [CollatzResearch.WordTrace]
  refine ⟨98716316601606461321226731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65810877734404307547484487 98716316601606461321226731)
  ·
    refine ⟨148074474902409691981840097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98716316601606461321226731 148074474902409691981840097)
    ·
      refine ⟨111055856176807268986380073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148074474902409691981840097 111055856176807268986380073)
      ·
        refine ⟨83291892132605451739785055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111055856176807268986380073 83291892132605451739785055)
        ·
          refine ⟨124937838198908177609677583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83291892132605451739785055 124937838198908177609677583)
          ·
            refine ⟨187406757298362266414516375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124937838198908177609677583 187406757298362266414516375)
            ·
              refine ⟨281110135947543399621774563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187406757298362266414516375 281110135947543399621774563)
              ·
                refine ⟨421665203921315099432661845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281110135947543399621774563 421665203921315099432661845)
                ·
                  refine ⟨2470694554226455660738253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 421665203921315099432661845 2470694554226455660738253)
                  ·
                    refine ⟨926510457834920872776845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470694554226455660738253 926510457834920872776845)
                    ·
                      rfl

theorem cell22_2706559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 3].length) (baseStart_2706559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706559 prefixEnd_2706559 := by exact prefixLift 2706559
  have htrace : WordTrace (prefixWord ++ tailWord_2706559) baseStart_2706559 baseEnd_2706559 := by
    simpa [prefixWord, tailWord_2706559, baseEnd_2706559] using wordTrace_append hprefix tailTrace_2706559
  have hstable : (prefixWord ++ tailWord_2706559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706559).length < 2 ^ (prefixWord ++ tailWord_2706559).sum := by decide
  have hdescent : baseEnd_2706559 < baseStart_2706559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706561 : List Nat := [1, 2, 4, 2, 2, 3, 1, 7]
def baseStart_2706561 : Nat := 118140960795 + 2706561 * 2 ^ 59
def prefixEnd_2706561 : Nat := 4983230072969 + 3 ^ 40 * 2706561 * 2
def baseEnd_2706561 : Nat := 102945682497310392691871

theorem tailTrace_2706561 : CollatzResearch.WordTrace tailWord_2706561 prefixEnd_2706561 102945682497310392691871 := by
  unfold tailWord_2706561
  simp only [CollatzResearch.WordTrace]
  refine ⟨98716389547599215662799537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65810926365066143775199691 98716389547599215662799537)
  ·
    refine ⟨74037292160699411747099653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98716389547599215662799537 74037292160699411747099653)
    ·
      refine ⟨13881992280131139702581185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74037292160699411747099653 13881992280131139702581185)
      ·
        refine ⟨10411494210098354776935889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13881992280131139702581185 10411494210098354776935889)
        ·
          refine ⟨7808620657573766082701917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10411494210098354776935889 7808620657573766082701917)
          ·
            refine ⟨2928232746590162281013219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7808620657573766082701917 2928232746590162281013219)
            ·
              refine ⟨4392349119885243421519829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928232746590162281013219 4392349119885243421519829)
              ·
                refine ⟨102945682497310392691871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4392349119885243421519829 102945682497310392691871)
                ·
                  rfl

theorem cell22_2706561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 7].length) (baseStart_2706561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706561 prefixEnd_2706561 := by exact prefixLift 2706561
  have htrace : WordTrace (prefixWord ++ tailWord_2706561) baseStart_2706561 baseEnd_2706561 := by
    simpa [prefixWord, tailWord_2706561, baseEnd_2706561] using wordTrace_append hprefix tailTrace_2706561
  have hstable : (prefixWord ++ tailWord_2706561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706561).length < 2 ^ (prefixWord ++ tailWord_2706561).sum := by decide
  have hdescent : baseEnd_2706561 < baseStart_2706561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706589 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 7]
def baseStart_2706589 : Nat := 118140960795 + 2706589 * 2 ^ 59
def prefixEnd_2706589 : Nat := 4983230072969 + 3 ^ 40 * 2706589 * 2
def baseEnd_2706589 : Nat := 308840242482670264842251

theorem tailTrace_2706589 : CollatzResearch.WordTrace tailWord_2706589 prefixEnd_2706589 308840242482670264842251 := by
  unfold tailWord_2706589
  simp only [CollatzResearch.WordTrace]
  refine ⟨98717410791497776444818821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65811607194331850963212547 98717410791497776444818821)
  ·
    refine ⟨18509514523405833083403529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98717410791497776444818821 18509514523405833083403529)
    ·
      refine ⟨13882135892554374812552647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18509514523405833083403529 13882135892554374812552647)
      ·
        refine ⟨20823203838831562218828971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13882135892554374812552647 20823203838831562218828971)
        ·
          refine ⟨31234805758247343328243457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20823203838831562218828971 31234805758247343328243457)
          ·
            refine ⟨23426104318685507496182593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31234805758247343328243457 23426104318685507496182593)
            ·
              refine ⟨17569578239014130622136945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23426104318685507496182593 17569578239014130622136945)
              ·
                refine ⟨13177183679260597966602709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17569578239014130622136945 13177183679260597966602709)
                ·
                  refine ⟨308840242482670264842251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13177183679260597966602709 308840242482670264842251)
                  ·
                    rfl

theorem cell22_2706589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_2706589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706589 prefixEnd_2706589 := by exact prefixLift 2706589
  have htrace : WordTrace (prefixWord ++ tailWord_2706589) baseStart_2706589 baseEnd_2706589 := by
    simpa [prefixWord, tailWord_2706589, baseEnd_2706589] using wordTrace_append hprefix tailTrace_2706589
  have hstable : (prefixWord ++ tailWord_2706589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706589).length < 2 ^ (prefixWord ++ tailWord_2706589).sum := by decide
  have hdescent : baseEnd_2706589 < baseStart_2706589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706619 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 3, 4]
def baseStart_2706619 : Nat := 118140960795 + 2706619 * 2 ^ 59
def prefixEnd_2706619 : Nat := 4983230072969 + 3 ^ 40 * 2706619 * 2
def baseEnd_2706619 : Nat := 926530997061100716276661

theorem tailTrace_2706619 : CollatzResearch.WordTrace tailWord_2706619 prefixEnd_2706619 926530997061100716276661 := by
  unfold tailWord_2706619
  simp only [CollatzResearch.WordTrace]
  refine ⟨98718504981389091568410911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65812336654259394378940607 98718504981389091568410911)
  ·
    refine ⟨148077757472083637352616367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98718504981389091568410911 148077757472083637352616367)
    ·
      refine ⟨222116636208125456028924551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148077757472083637352616367 222116636208125456028924551)
      ·
        refine ⟨333174954312188184043386827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222116636208125456028924551 333174954312188184043386827)
        ·
          refine ⟨499762431468282276065080241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333174954312188184043386827 499762431468282276065080241)
          ·
            refine ⟨374821823601211707048810181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499762431468282276065080241 374821823601211707048810181)
            ·
              refine ⟨70279091925227195071651909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 374821823601211707048810181 70279091925227195071651909)
              ·
                refine ⟨13177329735980099075934733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70279091925227195071651909 13177329735980099075934733)
                ·
                  refine ⟨4941498650992537153475525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13177329735980099075934733 4941498650992537153475525)
                  ·
                    refine ⟨926530997061100716276661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4941498650992537153475525 926530997061100716276661)
                    ·
                      rfl

theorem cell22_2706619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 4].length) (baseStart_2706619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706619 prefixEnd_2706619 := by exact prefixLift 2706619
  have htrace : WordTrace (prefixWord ++ tailWord_2706619) baseStart_2706619 baseEnd_2706619 := by
    simpa [prefixWord, tailWord_2706619, baseEnd_2706619] using wordTrace_append hprefix tailTrace_2706619
  have hstable : (prefixWord ++ tailWord_2706619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706619).length < 2 ^ (prefixWord ++ tailWord_2706619).sum := by decide
  have hdescent : baseEnd_2706619 < baseStart_2706619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706644 : List Nat := [2, 4, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_2706644 : Nat := 118140960795 + 2706644 * 2 ^ 59
def prefixEnd_2706644 : Nat := 4983230072969 + 3 ^ 40 * 2706644 * 2
def baseEnd_2706644 : Nat := 926539555072008984401585

theorem tailTrace_2706644 : CollatzResearch.WordTrace tailWord_2706644 prefixEnd_2706644 926539555072008984401585 := by
  unfold tailWord_2706644
  simp only [CollatzResearch.WordTrace]
  refine ⟨49359708403149260419035493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65812944537532347225380657 49359708403149260419035493)
  ·
    refine ⟨9254945325590486328569155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49359708403149260419035493 9254945325590486328569155)
    ·
      refine ⟨13882417988385729492853733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9254945325590486328569155 13882417988385729492853733)
      ·
        refine ⟨2602953372822324279910075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13882417988385729492853733 2602953372822324279910075)
        ·
          refine ⟨3904430059233486419865113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602953372822324279910075 3904430059233486419865113)
          ·
            refine ⟨2928322544425114814898835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3904430059233486419865113 2928322544425114814898835)
            ·
              refine ⟨4392483816637672222348253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928322544425114814898835 4392483816637672222348253)
              ·
                refine ⟨1647181431239127083380595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4392483816637672222348253 1647181431239127083380595)
                ·
                  refine ⟨2470772146858690625070893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647181431239127083380595 2470772146858690625070893)
                  ·
                    refine ⟨926539555072008984401585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470772146858690625070893 926539555072008984401585)
                    ·
                      rfl

theorem cell22_2706644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_2706644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706644 prefixEnd_2706644 := by exact prefixLift 2706644
  have htrace : WordTrace (prefixWord ++ tailWord_2706644) baseStart_2706644 baseEnd_2706644 := by
    simpa [prefixWord, tailWord_2706644, baseEnd_2706644] using wordTrace_append hprefix tailTrace_2706644
  have hstable : (prefixWord ++ tailWord_2706644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706644).length < 2 ^ (prefixWord ++ tailWord_2706644).sum := by decide
  have hdescent : baseEnd_2706644 < baseStart_2706644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706649 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_2706649 : Nat := 118140960795 + 2706649 * 2 ^ 59
def prefixEnd_2706649 : Nat := 4983230072969 + 3 ^ 40 * 2706649 * 2
def baseEnd_2706649 : Nat := 926541266674190638026569

theorem tailTrace_2706649 : CollatzResearch.WordTrace tailWord_2706649 prefixEnd_2706649 926541266674190638026569 := by
  unfold tailWord_2706649
  simp only [CollatzResearch.WordTrace]
  refine ⟨98719599171280406692003001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65813066114186937794668667 98719599171280406692003001)
  ·
    refine ⟨74039699378460305019002251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98719599171280406692003001 74039699378460305019002251)
    ·
      refine ⟨111059549067690457528503377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74039699378460305019002251 111059549067690457528503377)
      ·
        refine ⟨83294661800767843146377533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111059549067690457528503377 83294661800767843146377533)
        ·
          refine ⟨31235498175287941179891575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83294661800767843146377533 31235498175287941179891575)
          ·
            refine ⟨46853247262931911769837363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31235498175287941179891575 46853247262931911769837363)
            ·
              refine ⟨70279870894397867654756045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46853247262931911769837363 70279870894397867654756045)
              ·
                refine ⟨26354951585399200370533517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70279870894397867654756045 26354951585399200370533517)
                ·
                  refine ⟨9883106844524700138950069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26354951585399200370533517 9883106844524700138950069)
                  ·
                    refine ⟨926541266674190638026569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9883106844524700138950069 926541266674190638026569)
                    ·
                      rfl

theorem cell22_2706649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_2706649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706649 prefixEnd_2706649 := by exact prefixLift 2706649
  have htrace : WordTrace (prefixWord ++ tailWord_2706649) baseStart_2706649 baseEnd_2706649 := by
    simpa [prefixWord, tailWord_2706649, baseEnd_2706649] using wordTrace_append hprefix tailTrace_2706649
  have hstable : (prefixWord ++ tailWord_2706649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706649).length < 2 ^ (prefixWord ++ tailWord_2706649).sum := by decide
  have hdescent : baseEnd_2706649 < baseStart_2706649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706745 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 3, 3]
def baseStart_2706745 : Nat := 118140960795 + 2706745 * 2 ^ 59
def prefixEnd_2706745 : Nat := 4983230072969 + 3 ^ 40 * 2706745 * 2
def baseEnd_2706745 : Nat := 926574129436078387626275

theorem tailTrace_2706745 : CollatzResearch.WordTrace tailWord_2706745 prefixEnd_2706745 926574129436078387626275 := by
  unfold tailWord_2706745
  simp only [CollatzResearch.WordTrace]
  refine ⟨98723100578932615087497689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65815400385955076724998459 98723100578932615087497689)
  ·
    refine ⟨74042325434199461315623267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98723100578932615087497689 74042325434199461315623267)
    ·
      refine ⟨111063488151299191973434901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74042325434199461315623267 111063488151299191973434901)
      ·
        refine ⟨5206101007092149623754761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111063488151299191973434901 5206101007092149623754761)
        ·
          refine ⟨3904575755319112217816071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5206101007092149623754761 3904575755319112217816071)
          ·
            refine ⟨5856863632978668326724107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3904575755319112217816071 5856863632978668326724107)
            ·
              refine ⟨8785295449468002490086161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856863632978668326724107 8785295449468002490086161)
              ·
                refine ⟨6588971587101001867564621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8785295449468002490086161 6588971587101001867564621)
                ·
                  refine ⟨2470864345162875700336733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6588971587101001867564621 2470864345162875700336733)
                  ·
                    refine ⟨926574129436078387626275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470864345162875700336733 926574129436078387626275)
                    ·
                      rfl

theorem cell22_2706745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 3].length) (baseStart_2706745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706745 prefixEnd_2706745 := by exact prefixLift 2706745
  have htrace : WordTrace (prefixWord ++ tailWord_2706745) baseStart_2706745 baseEnd_2706745 := by
    simpa [prefixWord, tailWord_2706745, baseEnd_2706745] using wordTrace_append hprefix tailTrace_2706745
  have hstable : (prefixWord ++ tailWord_2706745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706745).length < 2 ^ (prefixWord ++ tailWord_2706745).sum := by decide
  have hdescent : baseEnd_2706745 < baseStart_2706745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706816 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 6, 4]
def baseStart_2706816 : Nat := 118140960795 + 2706816 * 2 ^ 59
def prefixEnd_2706816 : Nat := 4983230072969 + 3 ^ 40 * 2706816 * 2
def baseEnd_2706816 : Nat := 926598434187057869101057

theorem tailTrace_2706816 : CollatzResearch.WordTrace tailWord_2706816 prefixEnd_2706816 926598434187057869101057 := by
  unfold tailWord_2706816
  simp only [CollatzResearch.WordTrace]
  refine ⟨49362845080837697106666151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65817126774450262808888201 49362845080837697106666151)
  ·
    refine ⟨74044267621256545659999227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49362845080837697106666151 74044267621256545659999227)
    ·
      refine ⟨111066401431884818489998841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74044267621256545659999227 111066401431884818489998841)
      ·
        refine ⟨83299801073913613867499131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111066401431884818489998841 83299801073913613867499131)
        ·
          refine ⟨124949701610870420801248697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83299801073913613867499131 124949701610870420801248697)
          ·
            refine ⟨93712276208152815600936523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124949701610870420801248697 93712276208152815600936523)
            ·
              refine ⟨140568414312229223401404785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93712276208152815600936523 140568414312229223401404785)
              ·
                refine ⟨105426310734171917551053589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140568414312229223401404785 105426310734171917551053589)
                ·
                  refine ⟨4941858315664308635205637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105426310734171917551053589 4941858315664308635205637)
                  ·
                    refine ⟨926598434187057869101057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4941858315664308635205637 926598434187057869101057)
                    ·
                      rfl

theorem cell22_2706816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_2706816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706816 prefixEnd_2706816 := by exact prefixLift 2706816
  have htrace : WordTrace (prefixWord ++ tailWord_2706816) baseStart_2706816 baseEnd_2706816 := by
    simpa [prefixWord, tailWord_2706816, baseEnd_2706816] using wordTrace_append hprefix tailTrace_2706816
  have hstable : (prefixWord ++ tailWord_2706816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706816).length < 2 ^ (prefixWord ++ tailWord_2706816).sum := by decide
  have hdescent : baseEnd_2706816 < baseStart_2706816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706820 : List Nat := [2, 3, 2, 1, 1, 3, 3, 3, 4]
def baseStart_2706820 : Nat := 118140960795 + 2706820 * 2 ^ 59
def prefixEnd_2706820 : Nat := 4983230072969 + 3 ^ 40 * 2706820 * 2
def baseEnd_2706820 : Nat := 308866601156267730667015

theorem tailTrace_2706820 : CollatzResearch.WordTrace tailWord_2706820 prefixEnd_2706820 308866601156267730667015 := by
  unfold tailWord_2706820
  simp only [CollatzResearch.WordTrace]
  refine ⟨49362918026830451448238957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65817224035773935264318609 49362918026830451448238957)
  ·
    refine ⟨18511094260061419293089609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49362918026830451448238957 18511094260061419293089609)
    ·
      refine ⟨13883320695046064469817207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18511094260061419293089609 13883320695046064469817207)
      ·
        refine ⟨20824981042569096704725811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13883320695046064469817207 20824981042569096704725811)
        ·
          refine ⟨31237471563853645057088717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20824981042569096704725811 31237471563853645057088717)
          ·
            refine ⟨11714051836445116896408269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31237471563853645057088717 11714051836445116896408269)
            ·
              refine ⟨4392769438666918836153101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11714051836445116896408269 4392769438666918836153101)
              ·
                refine ⟨1647288539500094563557413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4392769438666918836153101 1647288539500094563557413)
                ·
                  refine ⟨308866601156267730667015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647288539500094563557413 308866601156267730667015)
                  ·
                    rfl

theorem cell22_2706820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_2706820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706820 prefixEnd_2706820 := by exact prefixLift 2706820
  have htrace : WordTrace (prefixWord ++ tailWord_2706820) baseStart_2706820 baseEnd_2706820 := by
    simpa [prefixWord, tailWord_2706820, baseEnd_2706820] using wordTrace_append hprefix tailTrace_2706820
  have hstable : (prefixWord ++ tailWord_2706820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706820).length < 2 ^ (prefixWord ++ tailWord_2706820).sum := by decide
  have hdescent : baseEnd_2706820 < baseStart_2706820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706863 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 3, 3]
def baseStart_2706863 : Nat := 118140960795 + 2706863 * 2 ^ 59
def prefixEnd_2706863 : Nat := 4983230072969 + 3 ^ 40 * 2706863 * 2
def baseEnd_2706863 : Nat := 926614523247565413175913

theorem tailTrace_2706863 : CollatzResearch.WordTrace tailWord_2706863 prefixEnd_2706863 926614523247565413175913 := by
  unfold tailWord_2706863
  simp only [CollatzResearch.WordTrace]
  refine ⟨98727404392505121240293243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65818269595003414160195495 98727404392505121240293243)
  ·
    refine ⟨148091106588757681860439865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98727404392505121240293243 148091106588757681860439865)
    ·
      refine ⟨111068329941568261395329899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148091106588757681860439865 111068329941568261395329899)
      ·
        refine ⟨166602494912352392092994849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111068329941568261395329899 166602494912352392092994849)
        ·
          refine ⟨124951871184264294069746137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166602494912352392092994849 124951871184264294069746137)
          ·
            refine ⟨93713903388198220552309603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124951871184264294069746137 93713903388198220552309603)
            ·
              refine ⟨140570855082297330828464405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93713903388198220552309603 140570855082297330828464405)
              ·
                refine ⟨6589258831982687382584269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140570855082297330828464405 6589258831982687382584269)
                ·
                  refine ⟨2470972061993507768469101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6589258831982687382584269 2470972061993507768469101)
                  ·
                    refine ⟨926614523247565413175913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470972061993507768469101 926614523247565413175913)
                    ·
                      rfl

theorem cell22_2706863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 3].length) (baseStart_2706863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706863 prefixEnd_2706863 := by exact prefixLift 2706863
  have htrace : WordTrace (prefixWord ++ tailWord_2706863) baseStart_2706863 baseEnd_2706863 := by
    simpa [prefixWord, tailWord_2706863, baseEnd_2706863] using wordTrace_append hprefix tailTrace_2706863
  have hstable : (prefixWord ++ tailWord_2706863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706863).length < 2 ^ (prefixWord ++ tailWord_2706863).sum := by decide
  have hdescent : baseEnd_2706863 < baseStart_2706863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706882 : List Nat := [3, 5, 2, 1, 11]
def baseStart_2706882 : Nat := 118140960795 + 2706882 * 2 ^ 59
def prefixEnd_2706882 : Nat := 4983230072969 + 3 ^ 40 * 2706882 * 2
def baseEnd_2706882 : Nat := 3813255256526155131485

theorem tailTrace_2706882 : CollatzResearch.WordTrace tailWord_2706882 prefixEnd_2706882 3813255256526155131485 := by
  unfold tailWord_2706882
  simp only [CollatzResearch.WordTrace]
  refine ⟨24682024344859071871308725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65818731586290858323489933 24682024344859071871308725)
  ·
    refine ⟨2313939782330537987935193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24682024344859071871308725 2313939782330537987935193)
    ·
      refine ⟨1735454836747903490951395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2313939782330537987935193 1735454836747903490951395)
      ·
        refine ⟨2603182255121855236427093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735454836747903490951395 2603182255121855236427093)
        ·
          refine ⟨3813255256526155131485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2603182255121855236427093 3813255256526155131485)
          ·
            rfl

theorem cell22_2706882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 11].length) (baseStart_2706882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706882 prefixEnd_2706882 := by exact prefixLift 2706882
  have htrace : WordTrace (prefixWord ++ tailWord_2706882) baseStart_2706882 baseEnd_2706882 := by
    simpa [prefixWord, tailWord_2706882, baseEnd_2706882] using wordTrace_append hprefix tailTrace_2706882
  have hstable : (prefixWord ++ tailWord_2706882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706882).length < 2 ^ (prefixWord ++ tailWord_2706882).sum := by decide
  have hdescent : baseEnd_2706882 < baseStart_2706882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706955 : List Nat := [1, 1, 1, 1, 8, 1, 2, 1, 6]
def baseStart_2706955 : Nat := 118140960795 + 2706955 * 2 ^ 59
def prefixEnd_2706955 : Nat := 4983230072969 + 3 ^ 40 * 2706955 * 2
def baseEnd_2706955 : Nat := 308882005575902613291877

theorem tailTrace_2706955 : CollatzResearch.WordTrace tailWord_2706955 prefixEnd_2706955 308882005575902613291877 := by
  unfold tailWord_2706955
  simp only [CollatzResearch.WordTrace]
  refine ⟨98730759908171820952642319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65820506605447880635094879 98730759908171820952642319)
  ·
    refine ⟨148096139862257731428963479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98730759908171820952642319 148096139862257731428963479)
    ·
      refine ⟨222144209793386597143445219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148096139862257731428963479 222144209793386597143445219)
      ·
        refine ⟨333216314690079895715167829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222144209793386597143445219 333216314690079895715167829)
        ·
          refine ⟨3904878687774373777912123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 333216314690079895715167829 3904878687774373777912123)
          ·
            refine ⟨5857318031661560666868185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3904878687774373777912123 5857318031661560666868185)
            ·
              refine ⟨4392988523746170500151139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5857318031661560666868185 4392988523746170500151139)
              ·
                refine ⟨6589482785619255750226709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4392988523746170500151139 6589482785619255750226709)
                ·
                  refine ⟨308882005575902613291877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6589482785619255750226709 308882005575902613291877)
                  ·
                    rfl

theorem cell22_2706955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 1, 6].length) (baseStart_2706955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2706955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2706955 prefixEnd_2706955 := by exact prefixLift 2706955
  have htrace : WordTrace (prefixWord ++ tailWord_2706955) baseStart_2706955 baseEnd_2706955 := by
    simpa [prefixWord, tailWord_2706955, baseEnd_2706955] using wordTrace_append hprefix tailTrace_2706955
  have hstable : (prefixWord ++ tailWord_2706955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706955).length < 2 ^ (prefixWord ++ tailWord_2706955).sum := by decide
  have hdescent : baseEnd_2706955 < baseStart_2706955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707013 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_2707013 : Nat := 118140960795 + 2707013 * 2 ^ 59
def prefixEnd_2707013 : Nat := 4983230072969 + 3 ^ 40 * 2707013 * 2
def baseEnd_2707013 : Nat := 926665871313015021925453

theorem tailTrace_2707013 : CollatzResearch.WordTrace tailWord_2707013 prefixEnd_2707013 926665871313015021925453 := by
  unfold tailWord_2707013
  simp only [CollatzResearch.WordTrace]
  refine ⟨98732875341961696858253693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65821916894641131238835795 98732875341961696858253693)
  ·
    refine ⟨37024828253235636321845135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98732875341961696858253693 37024828253235636321845135)
    ·
      refine ⟨55537242379853454482767703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37024828253235636321845135 55537242379853454482767703)
      ·
        refine ⟨83305863569780181724151555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55537242379853454482767703 83305863569780181724151555)
        ·
          refine ⟨124958795354670272586227333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83305863569780181724151555 124958795354670272586227333)
          ·
            refine ⟨23429774129000676109917625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124958795354670272586227333 23429774129000676109917625)
            ·
              refine ⟨17572330596750507082438219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23429774129000676109917625 17572330596750507082438219)
              ·
                refine ⟨26358495895125760623657329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17572330596750507082438219 26358495895125760623657329)
                ·
                  refine ⟨19768871921344320467742997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26358495895125760623657329 19768871921344320467742997)
                  ·
                    refine ⟨926665871313015021925453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19768871921344320467742997 926665871313015021925453)
                    ·
                      rfl

theorem cell22_2707013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_2707013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707013 prefixEnd_2707013 := by exact prefixLift 2707013
  have htrace : WordTrace (prefixWord ++ tailWord_2707013) baseStart_2707013 baseEnd_2707013 := by
    simpa [prefixWord, tailWord_2707013, baseEnd_2707013] using wordTrace_append hprefix tailTrace_2707013
  have hstable : (prefixWord ++ tailWord_2707013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707013).length < 2 ^ (prefixWord ++ tailWord_2707013).sum := by decide
  have hdescent : baseEnd_2707013 < baseStart_2707013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707062 : List Nat := [5, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_2707062 : Nat := 118140960795 + 2707062 * 2 ^ 59
def prefixEnd_2707062 : Nat := 4983230072969 + 3 ^ 40 * 2707062 * 2
def baseEnd_2707062 : Nat := 308894215004798409150101

theorem tailTrace_2707062 : CollatzResearch.WordTrace tailWord_2707062 prefixEnd_2707062 308894215004798409150101 := by
  unfold tailWord_2707062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6170916407424011139174215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65823108345856118817858293 6170916407424011139174215)
  ·
    refine ⟨9256374611136016708761323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6170916407424011139174215 9256374611136016708761323)
    ·
      refine ⟨13884561916704025063141985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9256374611136016708761323 13884561916704025063141985)
      ·
        refine ⟨10413421437528018797356489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13884561916704025063141985 10413421437528018797356489)
        ·
          refine ⟨7810066078146014098017367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10413421437528018797356489 7810066078146014098017367)
          ·
            refine ⟨11715099117219021147026051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7810066078146014098017367 11715099117219021147026051)
            ·
              refine ⟨17572648675828531720539077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11715099117219021147026051 17572648675828531720539077)
              ·
                refine ⟨3294871626717849697601077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17572648675828531720539077 3294871626717849697601077)
                ·
                  refine ⟨308894215004798409150101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3294871626717849697601077 308894215004798409150101)
                  ·
                    rfl

theorem cell22_2707062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2707062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707062 prefixEnd_2707062 := by exact prefixLift 2707062
  have htrace : WordTrace (prefixWord ++ tailWord_2707062) baseStart_2707062 baseEnd_2707062 := by
    simpa [prefixWord, tailWord_2707062, baseEnd_2707062] using wordTrace_append hprefix tailTrace_2707062
  have hstable : (prefixWord ++ tailWord_2707062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707062).length < 2 ^ (prefixWord ++ tailWord_2707062).sum := by decide
  have hdescent : baseEnd_2707062 < baseStart_2707062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707107 : List Nat := [1, 1, 1, 4, 1, 1, 6, 3, 4]
def baseStart_2707107 : Nat := 118140960795 + 2707107 * 2 ^ 59
def prefixEnd_2707107 : Nat := 4983230072969 + 3 ^ 40 * 2707107 * 2
def baseEnd_2707107 : Nat := 308899349811343370025055

theorem tailTrace_2707107 : CollatzResearch.WordTrace tailWord_2707107 prefixEnd_2707107 308899349811343370025055 := by
  unfold tailWord_2707107
  simp only [CollatzResearch.WordTrace]
  refine ⟨98736303803621150912175575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65824202535747433941450383 98736303803621150912175575)
  ·
    refine ⟨148104455705431726368263363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98736303803621150912175575 148104455705431726368263363)
    ·
      refine ⟨222156683558147589552395045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148104455705431726368263363 222156683558147589552395045)
      ·
        refine ⟨41654378167152673041074071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222156683558147589552395045 41654378167152673041074071)
        ·
          refine ⟨62481567250729009561611107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41654378167152673041074071 62481567250729009561611107)
          ·
            refine ⟨93722350876093514342416661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62481567250729009561611107 93722350876093514342416661)
            ·
              refine ⟨4393235197316883484800781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93722350876093514342416661 4393235197316883484800781)
              ·
                refine ⟨1647463198993831306800293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4393235197316883484800781 1647463198993831306800293)
                ·
                  refine ⟨308899349811343370025055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647463198993831306800293 308899349811343370025055)
                  ·
                    rfl

theorem cell22_2707107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 3, 4].length) (baseStart_2707107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707107 prefixEnd_2707107 := by exact prefixLift 2707107
  have htrace : WordTrace (prefixWord ++ tailWord_2707107) baseStart_2707107 baseEnd_2707107 := by
    simpa [prefixWord, tailWord_2707107, baseEnd_2707107] using wordTrace_append hprefix tailTrace_2707107
  have hstable : (prefixWord ++ tailWord_2707107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707107).length < 2 ^ (prefixWord ++ tailWord_2707107).sum := by decide
  have hdescent : baseEnd_2707107 < baseStart_2707107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707120 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 2, 4]
def baseStart_2707120 : Nat := 118140960795 + 2707120 * 2 ^ 59
def prefixEnd_2707120 : Nat := 4983230072969 + 3 ^ 40 * 2707120 * 2
def baseEnd_2707120 : Nat := 926702499599702409500125

theorem tailTrace_2707120 : CollatzResearch.WordTrace tailWord_2707120 prefixEnd_2707120 926702499599702409500125 := by
  unfold tailWord_2707120
  simp only [CollatzResearch.WordTrace]
  refine ⟨49368388976287027066199407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65824518635049369421599209 49368388976287027066199407)
  ·
    refine ⟨74052583464430540599299111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49368388976287027066199407 74052583464430540599299111)
    ·
      refine ⟨111078875196645810898948667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74052583464430540599299111 111078875196645810898948667)
      ·
        refine ⟨166618312794968716348423001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111078875196645810898948667 166618312794968716348423001)
        ·
          refine ⟨124963734596226537261317251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166618312794968716348423001 124963734596226537261317251)
          ·
            refine ⟨187445601894339805891975877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124963734596226537261317251 187445601894339805891975877)
            ·
              refine ⟨35146050355188713604745477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187445601894339805891975877 35146050355188713604745477)
              ·
                refine ⟨6589884441597883800889777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35146050355188713604745477 6589884441597883800889777)
                ·
                  refine ⟨4942413331198412850667333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6589884441597883800889777 4942413331198412850667333)
                  ·
                    refine ⟨926702499599702409500125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4942413331198412850667333 926702499599702409500125)
                    ·
                      rfl

theorem cell22_2707120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_2707120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707120 prefixEnd_2707120 := by exact prefixLift 2707120
  have htrace : WordTrace (prefixWord ++ tailWord_2707120) baseStart_2707120 baseEnd_2707120 := by
    simpa [prefixWord, tailWord_2707120, baseEnd_2707120] using wordTrace_append hprefix tailTrace_2707120
  have hstable : (prefixWord ++ tailWord_2707120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707120).length < 2 ^ (prefixWord ++ tailWord_2707120).sum := by decide
  have hdescent : baseEnd_2707120 < baseStart_2707120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707150 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_2707150 : Nat := 118140960795 + 2707150 * 2 ^ 59
def prefixEnd_2707150 : Nat := 4983230072969 + 3 ^ 40 * 2707150 * 2
def baseEnd_2707150 : Nat := 926712769212792331250033

theorem tailTrace_2707150 : CollatzResearch.WordTrace tailWord_2707150 prefixEnd_2707150 926712769212792331250033 := by
  unfold tailWord_2707150
  simp only [CollatzResearch.WordTrace]
  refine ⟨12342234017808171156998863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65825248094976912837327269 12342234017808171156998863)
  ·
    refine ⟨18513351026712256735498295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12342234017808171156998863 18513351026712256735498295)
    ·
      refine ⟨27770026540068385103247443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18513351026712256735498295 27770026540068385103247443)
      ·
        refine ⟨41655039810102577654871165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27770026540068385103247443 41655039810102577654871165)
        ·
          refine ⟨15620639928788466620576687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41655039810102577654871165 15620639928788466620576687)
          ·
            refine ⟨23430959893182699930865031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15620639928788466620576687 23430959893182699930865031)
            ·
              refine ⟨35146439839774049896297547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23430959893182699930865031 35146439839774049896297547)
              ·
                refine ⟨52719659759661074844446321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35146439839774049896297547 52719659759661074844446321)
                ·
                  refine ⟨39539744819745806133334741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52719659759661074844446321 39539744819745806133334741)
                  ·
                    refine ⟨926712769212792331250033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39539744819745806133334741 926712769212792331250033)
                    ·
                      rfl

theorem cell22_2707150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_2707150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707150 prefixEnd_2707150 := by exact prefixLift 2707150
  have htrace : WordTrace (prefixWord ++ tailWord_2707150) baseStart_2707150 baseEnd_2707150 := by
    simpa [prefixWord, tailWord_2707150, baseEnd_2707150] using wordTrace_append hprefix tailTrace_2707150
  have hstable : (prefixWord ++ tailWord_2707150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707150).length < 2 ^ (prefixWord ++ tailWord_2707150).sum := by decide
  have hdescent : baseEnd_2707150 < baseStart_2707150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707180 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 7]
def baseStart_2707180 : Nat := 118140960795 + 2707180 * 2 ^ 59
def prefixEnd_2707180 : Nat := 4983230072969 + 3 ^ 40 * 2707180 * 2
def baseEnd_2707180 : Nat := 308907679608627417666647

theorem tailTrace_2707180 : CollatzResearch.WordTrace tailWord_2707180 prefixEnd_2707180 308907679608627417666647 := by
  unfold tailWord_2707180
  simp only [CollatzResearch.WordTrace]
  refine ⟨49369483166178342189791497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65825977554904456253055329 49369483166178342189791497)
  ·
    refine ⟨37027112374633756642343623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49369483166178342189791497 37027112374633756642343623)
    ·
      refine ⟨55540668561950634963515435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37027112374633756642343623 55540668561950634963515435)
      ·
        refine ⟨83311002842925952445273153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55540668561950634963515435 83311002842925952445273153)
        ·
          refine ⟨62483252132194464333954865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83311002842925952445273153 62483252132194464333954865)
          ·
            refine ⟨46862439099145848250466149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62483252132194464333954865 46862439099145848250466149)
            ·
              refine ⟨8786707331089846546962403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46862439099145848250466149 8786707331089846546962403)
              ·
                refine ⟨13180060996634769820443605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8786707331089846546962403 13180060996634769820443605)
                ·
                  refine ⟨308907679608627417666647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13180060996634769820443605 308907679608627417666647)
                  ·
                    rfl

theorem cell22_2707180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_2707180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707180 prefixEnd_2707180 := by exact prefixLift 2707180
  have htrace : WordTrace (prefixWord ++ tailWord_2707180) baseStart_2707180 baseEnd_2707180 := by
    simpa [prefixWord, tailWord_2707180, baseEnd_2707180] using wordTrace_append hprefix tailTrace_2707180
  have hstable : (prefixWord ++ tailWord_2707180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707180).length < 2 ^ (prefixWord ++ tailWord_2707180).sum := by decide
  have hdescent : baseEnd_2707180 < baseStart_2707180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707272 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 1, 6]
def baseStart_2707272 : Nat := 118140960795 + 2707272 * 2 ^ 59
def prefixEnd_2707272 : Nat := 4983230072969 + 3 ^ 40 * 2707272 * 2
def baseEnd_2707272 : Nat := 926754532306024679699659

theorem tailTrace_2707272 : CollatzResearch.WordTrace tailWord_2707272 prefixEnd_2707272 926754532306024679699659 := by
  unfold tailWord_2707272
  simp only [CollatzResearch.WordTrace]
  refine ⟨49371160924011692045966035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65828214565348922727954713 49371160924011692045966035)
  ·
    refine ⟨74056741386017538068949053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49371160924011692045966035 74056741386017538068949053)
    ·
      refine ⟨27771278019756576775855895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74056741386017538068949053 27771278019756576775855895)
      ·
        refine ⟨41656917029634865163783843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27771278019756576775855895 41656917029634865163783843)
        ·
          refine ⟨62485375544452297745675765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41656917029634865163783843 62485375544452297745675765)
          ·
            refine ⟨5858003957292402913657103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62485375544452297745675765 5858003957292402913657103)
            ·
              refine ⟨8787005935938604370485655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5858003957292402913657103 8787005935938604370485655)
              ·
                refine ⟨13180508903907906555728483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8787005935938604370485655 13180508903907906555728483)
                ·
                  refine ⟨19770763355861859833592725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13180508903907906555728483 19770763355861859833592725)
                  ·
                    refine ⟨926754532306024679699659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19770763355861859833592725 926754532306024679699659)
                    ·
                      rfl

theorem cell22_2707272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_2707272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707272 prefixEnd_2707272 := by exact prefixLift 2707272
  have htrace : WordTrace (prefixWord ++ tailWord_2707272) baseStart_2707272 baseEnd_2707272 := by
    simpa [prefixWord, tailWord_2707272, baseEnd_2707272] using wordTrace_append hprefix tailTrace_2707272
  have hstable : (prefixWord ++ tailWord_2707272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707272).length < 2 ^ (prefixWord ++ tailWord_2707272).sum := by decide
  have hdescent : baseEnd_2707272 < baseStart_2707272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707276 : List Nat := [2, 2, 1, 3, 4, 1, 2, 3, 4]
def baseStart_2707276 : Nat := 118140960795 + 2707276 * 2 ^ 59
def prefixEnd_2707276 : Nat := 4983230072969 + 3 ^ 40 * 2707276 * 2
def baseEnd_2707276 : Nat := 308918633862590000866549

theorem tailTrace_2707276 : CollatzResearch.WordTrace tailWord_2707276 prefixEnd_2707276 308918633862590000866549 := by
  unfold tailWord_2707276
  simp only [CollatzResearch.WordTrace]
  refine ⟨49371233870004446387538841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65828311826672595183385121 49371233870004446387538841)
  ·
    refine ⟨37028425402503334790654131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49371233870004446387538841 37028425402503334790654131)
    ·
      refine ⟨55542638103755002185981197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37028425402503334790654131 55542638103755002185981197)
      ·
        refine ⟨20828489288908125819742949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55542638103755002185981197 20828489288908125819742949)
        ·
          refine ⟨3905341741670273591201803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20828489288908125819742949 3905341741670273591201803)
          ·
            refine ⟨5858012612505410386802705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905341741670273591201803 5858012612505410386802705)
            ·
              refine ⟨4393509459379057790102029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5858012612505410386802705 4393509459379057790102029)
              ·
                refine ⟨1647566047267146671288261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4393509459379057790102029 1647566047267146671288261)
                ·
                  refine ⟨308918633862590000866549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647566047267146671288261 308918633862590000866549)
                  ·
                    rfl

theorem cell22_2707276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_2707276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707276 prefixEnd_2707276 := by exact prefixLift 2707276
  have htrace : WordTrace (prefixWord ++ tailWord_2707276) baseStart_2707276 baseEnd_2707276 := by
    simpa [prefixWord, tailWord_2707276, baseEnd_2707276] using wordTrace_append hprefix tailTrace_2707276
  have hstable : (prefixWord ++ tailWord_2707276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707276).length < 2 ^ (prefixWord ++ tailWord_2707276).sum := by decide
  have hdescent : baseEnd_2707276 < baseStart_2707276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707287 : List Nat := [1, 1, 3, 2, 5, 1, 9]
def baseStart_2707287 : Nat := 118140960795 + 2707287 * 2 ^ 59
def prefixEnd_2707287 : Nat := 4983230072969 + 3 ^ 40 * 2707287 * 2
def baseEnd_2707287 : Nat := 34324432115280357058319

theorem tailTrace_2707287 : CollatzResearch.WordTrace tailWord_2707287 prefixEnd_2707287 34324432115280357058319 := by
  unfold tailWord_2707287
  simp only [CollatzResearch.WordTrace]
  refine ⟨98742868942969041653728115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65828579295312694435818743 98742868942969041653728115)
  ·
    refine ⟨148114303414453562480592173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98742868942969041653728115 148114303414453562480592173)
    ·
      refine ⟨55542863780420085930222065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148114303414453562480592173 55542863780420085930222065)
      ·
        refine ⟨41657147835315064447666549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55542863780420085930222065 41657147835315064447666549)
        ·
          refine ⟨3905357609560787291968739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41657147835315064447666549 3905357609560787291968739)
          ·
            refine ⟨5858036414341180937953109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905357609560787291968739 5858036414341180937953109)
            ·
              refine ⟨34324432115280357058319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5858036414341180937953109 34324432115280357058319)
              ·
                rfl

theorem cell22_2707287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 9].length) (baseStart_2707287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707287 prefixEnd_2707287 := by exact prefixLift 2707287
  have htrace : WordTrace (prefixWord ++ tailWord_2707287) baseStart_2707287 baseEnd_2707287 := by
    simpa [prefixWord, tailWord_2707287, baseEnd_2707287] using wordTrace_append hprefix tailTrace_2707287
  have hstable : (prefixWord ++ tailWord_2707287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707287).length < 2 ^ (prefixWord ++ tailWord_2707287).sum := by decide
  have hdescent : baseEnd_2707287 < baseStart_2707287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707332 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 7]
def baseStart_2707332 : Nat := 118140960795 + 2707332 * 2 ^ 59
def prefixEnd_2707332 : Nat := 4983230072969 + 3 ^ 40 * 2707332 * 2
def baseEnd_2707332 : Nat := 308925023844068174399825

theorem tailTrace_2707332 : CollatzResearch.WordTrace tailWord_2707332 prefixEnd_2707332 308925023844068174399825 := by
  unfold tailWord_2707332
  simp only [CollatzResearch.WordTrace]
  refine ⟨49372255113903007169558125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65829673485204009559410833 49372255113903007169558125)
  ·
    refine ⟨18514595667713627688584297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49372255113903007169558125 18514595667713627688584297)
    ·
      refine ⟨13885946750785220766438223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18514595667713627688584297 13885946750785220766438223)
      ·
        refine ⟨20828920126177831149657335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13885946750785220766438223 20828920126177831149657335)
        ·
          refine ⟨31243380189266746724486003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20828920126177831149657335 31243380189266746724486003)
          ·
            refine ⟨46865070283900120086729005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31243380189266746724486003 46865070283900120086729005)
            ·
              refine ⟨17574401356462545032523377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46865070283900120086729005 17574401356462545032523377)
              ·
                refine ⟨13180801017346908774392533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17574401356462545032523377 13180801017346908774392533)
                ·
                  refine ⟨308925023844068174399825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13180801017346908774392533 308925023844068174399825)
                  ·
                    rfl

theorem cell22_2707332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_2707332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707332 prefixEnd_2707332 := by exact prefixLift 2707332
  have htrace : WordTrace (prefixWord ++ tailWord_2707332) baseStart_2707332 baseEnd_2707332 := by
    simpa [prefixWord, tailWord_2707332, baseEnd_2707332] using wordTrace_append hprefix tailTrace_2707332
  have hstable : (prefixWord ++ tailWord_2707332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707332).length < 2 ^ (prefixWord ++ tailWord_2707332).sum := by decide
  have hdescent : baseEnd_2707332 < baseStart_2707332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707439 : List Nat := [1, 1, 2, 1, 4, 2, 5, 6]
def baseStart_2707439 : Nat := 118140960795 + 2707439 * 2 ^ 59
def prefixEnd_2707439 : Nat := 4983230072969 + 3 ^ 40 * 2707439 * 2
def baseEnd_2707439 : Nat := 102979077757654656752683

theorem tailTrace_2707439 : CollatzResearch.WordTrace tailWord_2707439 prefixEnd_2707439 102979077757654656752683 := by
  unfold tailWord_2707439
  simp only [CollatzResearch.WordTrace]
  refine ⟨98748412838418371613261371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65832275225612247742174247 98748412838418371613261371)
  ·
    refine ⟨148122619257627557419892057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98748412838418371613261371 148122619257627557419892057)
    ·
      refine ⟨111091964443220668064919043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148122619257627557419892057 111091964443220668064919043)
      ·
        refine ⟨166637946664831002097378565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111091964443220668064919043 166637946664831002097378565)
        ·
          refine ⟨31244614999655812893258481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166637946664831002097378565 31244614999655812893258481)
          ·
            refine ⟨23433461249741859669943861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31244614999655812893258481 23433461249741859669943861)
            ·
              refine ⟨2196886992163299344057237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23433461249741859669943861 2196886992163299344057237)
              ·
                refine ⟨102979077757654656752683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2196886992163299344057237 102979077757654656752683)
                ·
                  rfl

theorem cell22_2707439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 6].length) (baseStart_2707439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707439 prefixEnd_2707439 := by exact prefixLift 2707439
  have htrace : WordTrace (prefixWord ++ tailWord_2707439) baseStart_2707439 baseEnd_2707439 := by
    simpa [prefixWord, tailWord_2707439, baseEnd_2707439] using wordTrace_append hprefix tailTrace_2707439
  have hstable : (prefixWord ++ tailWord_2707439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707439).length < 2 ^ (prefixWord ++ tailWord_2707439).sum := by decide
  have hdescent : baseEnd_2707439 < baseStart_2707439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707462 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2707462 : Nat := 118140960795 + 2707462 * 2 ^ 59
def prefixEnd_2707462 : Nat := 4983230072969 + 3 ^ 40 * 2707462 * 2
def baseEnd_2707462 : Nat := 308939857729642505816359

theorem tailTrace_2707462 : CollatzResearch.WordTrace tailWord_2707462 prefixEnd_2707462 308939857729642505816359 := by
  unfold tailWord_2707462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3085914116166720204417145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65832834478223364360899093 3085914116166720204417145)
  ·
    refine ⟨2314435587125040153312859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3085914116166720204417145 2314435587125040153312859)
    ·
      refine ⟨3471653380687560229969289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314435587125040153312859 3471653380687560229969289)
      ·
        refine ⟨2603740035515670172476967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3471653380687560229969289 2603740035515670172476967)
        ·
          refine ⟨3905610053273505258715451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603740035515670172476967 3905610053273505258715451)
          ·
            refine ⟨5858415079910257888073177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905610053273505258715451 5858415079910257888073177)
            ·
              refine ⟨4393811309932693416054883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5858415079910257888073177 4393811309932693416054883)
              ·
                refine ⟨6590716964899040124082325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4393811309932693416054883 6590716964899040124082325)
                ·
                  refine ⟨308939857729642505816359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6590716964899040124082325 308939857729642505816359)
                  ·
                    rfl

theorem cell22_2707462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2707462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707462 prefixEnd_2707462 := by exact prefixLift 2707462
  have htrace : WordTrace (prefixWord ++ tailWord_2707462) baseStart_2707462 baseEnd_2707462 := by
    simpa [prefixWord, tailWord_2707462, baseEnd_2707462] using wordTrace_append hprefix tailTrace_2707462
  have hstable : (prefixWord ++ tailWord_2707462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707462).length < 2 ^ (prefixWord ++ tailWord_2707462).sum := by decide
  have hdescent : baseEnd_2707462 < baseStart_2707462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707505 : List Nat := [1, 2, 2, 3, 1, 5, 1, 3, 1, 3]
def baseStart_2707505 : Nat := 118140960795 + 2707505 * 2 ^ 59
def prefixEnd_2707505 : Nat := 4983230072969 + 3 ^ 40 * 2707505 * 2
def baseEnd_2707505 : Nat := 926834292967689738623945

theorem tailTrace_2707505 : CollatzResearch.WordTrace tailWord_2707505 prefixEnd_2707505 926834292967689738623945 := by
  unfold tailWord_2707505
  simp only [CollatzResearch.WordTrace]
  refine ⟨98750820056179264885163969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65833880037452843256775979 98750820056179264885163969)
  ·
    refine ⟨74063115042134448663872977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98750820056179264885163969 74063115042134448663872977)
    ·
      refine ⟨55547336281600836497904733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74063115042134448663872977 55547336281600836497904733)
      ·
        refine ⟨20830251105600313686714275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55547336281600836497904733 20830251105600313686714275)
        ·
          refine ⟨31245376658400470530071413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20830251105600313686714275 31245376658400470530071413)
          ·
            refine ⟨2929254061725044112194195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31245376658400470530071413 2929254061725044112194195)
            ·
              refine ⟨4393881092587566168291293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929254061725044112194195 4393881092587566168291293)
              ·
                refine ⟨1647705409720337313109235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4393881092587566168291293 1647705409720337313109235)
                ·
                  refine ⟨2471558114580505969663853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647705409720337313109235 2471558114580505969663853)
                  ·
                    refine ⟨926834292967689738623945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2471558114580505969663853 926834292967689738623945)
                    ·
                      rfl

theorem cell22_2707505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_2707505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707505 prefixEnd_2707505 := by exact prefixLift 2707505
  have htrace : WordTrace (prefixWord ++ tailWord_2707505) baseStart_2707505 baseEnd_2707505 := by
    simpa [prefixWord, tailWord_2707505, baseEnd_2707505] using wordTrace_append hprefix tailTrace_2707505
  have hstable : (prefixWord ++ tailWord_2707505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707505).length < 2 ^ (prefixWord ++ tailWord_2707505).sum := by decide
  have hdescent : baseEnd_2707505 < baseStart_2707505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707514 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_2707514 : Nat := 118140960795 + 2707514 * 2 ^ 59
def prefixEnd_2707514 : Nat := 4983230072969 + 3 ^ 40 * 2707514 * 2
def baseEnd_2707514 : Nat := 926837373851616715148917

theorem tailTrace_2707514 : CollatzResearch.WordTrace tailWord_2707514 prefixEnd_2707514 926837373851616715148917 := by
  unfold tailWord_2707514
  simp only [CollatzResearch.WordTrace]
  refine ⟨24687787078286664855560399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65834098875431106281494397 24687787078286664855560399)
  ·
    refine ⟨37031680617429997283340599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24687787078286664855560399 37031680617429997283340599)
    ·
      refine ⟨55547520926144995925010899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37031680617429997283340599 55547520926144995925010899)
      ·
        refine ⟨83321281389217493887516349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55547520926144995925010899 83321281389217493887516349)
        ·
          refine ⟨31245480520956560207818631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83321281389217493887516349 31245480520956560207818631)
          ·
            refine ⟨46868220781434840311727947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31245480520956560207818631 46868220781434840311727947)
            ·
              refine ⟨70302331172152260467591921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46868220781434840311727947 70302331172152260467591921)
              ·
                refine ⟨52726748379114195350693941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70302331172152260467591921 52726748379114195350693941)
                ·
                  refine ⟨4943132660541955814127557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52726748379114195350693941 4943132660541955814127557)
                  ·
                    refine ⟨926837373851616715148917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943132660541955814127557 926837373851616715148917)
                    ·
                      rfl

theorem cell22_2707514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_2707514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707514 prefixEnd_2707514 := by exact prefixLift 2707514
  have htrace : WordTrace (prefixWord ++ tailWord_2707514) baseStart_2707514 baseEnd_2707514 := by
    simpa [prefixWord, tailWord_2707514, baseEnd_2707514] using wordTrace_append hprefix tailTrace_2707514
  have hstable : (prefixWord ++ tailWord_2707514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707514).length < 2 ^ (prefixWord ++ tailWord_2707514).sum := by decide
  have hdescent : baseEnd_2707514 < baseStart_2707514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707548 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_2707548 : Nat := 118140960795 + 2707548 * 2 ^ 59
def prefixEnd_2707548 : Nat := 4983230072969 + 3 ^ 40 * 2707548 * 2
def baseEnd_2707548 : Nat := 926849012746451959798813

theorem tailTrace_2707548 : CollatzResearch.WordTrace tailWord_2707548 prefixEnd_2707548 926849012746451959798813 := by
  unfold tailWord_2707548
  simp only [CollatzResearch.WordTrace]
  refine ⟨49376194197511741614489649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65834925596682322152652865 49376194197511741614489649)
  ·
    refine ⟨37032145648133806210867237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49376194197511741614489649 37032145648133806210867237)
    ·
      refine ⟨6943527309025088664537607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37032145648133806210867237 6943527309025088664537607)
      ·
        refine ⟨10415290963537632996806411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6943527309025088664537607 10415290963537632996806411)
        ·
          refine ⟨15622936445306449495209617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10415290963537632996806411 15622936445306449495209617)
          ·
            refine ⟨11717202333979837121407213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15622936445306449495209617 11717202333979837121407213)
            ·
              refine ⟨4393950875242438920527705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11717202333979837121407213 4393950875242438920527705)
              ·
                refine ⟨3295463156431829190395779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4393950875242438920527705 3295463156431829190395779)
                ·
                  refine ⟨4943194734647743785593669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295463156431829190395779 4943194734647743785593669)
                  ·
                    refine ⟨926849012746451959798813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943194734647743785593669 926849012746451959798813)
                    ·
                      rfl

theorem cell22_2707548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_2707548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707548 prefixEnd_2707548 := by exact prefixLift 2707548
  have htrace : WordTrace (prefixWord ++ tailWord_2707548) baseStart_2707548 baseEnd_2707548 := by
    simpa [prefixWord, tailWord_2707548, baseEnd_2707548] using wordTrace_append hprefix tailTrace_2707548
  have hstable : (prefixWord ++ tailWord_2707548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707548).length < 2 ^ (prefixWord ++ tailWord_2707548).sum := by decide
  have hdescent : baseEnd_2707548 < baseStart_2707548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707580 : List Nat := [2, 2, 2, 1, 1, 6, 2, 2, 4]
def baseStart_2707580 : Nat := 118140960795 + 2707580 * 2 ^ 59
def prefixEnd_2707580 : Nat := 4983230072969 + 3 ^ 40 * 2707580 * 2
def baseEnd_2707580 : Nat := 308953322333471514332905

theorem tailTrace_2707580 : CollatzResearch.WordTrace tailWord_2707580 prefixEnd_2707580 308953322333471514332905 := by
  unfold tailWord_2707580
  simp only [CollatzResearch.WordTrace]
  refine ⟨49376777765453776347072097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65835703687271701796096129 49376777765453776347072097)
  ·
    refine ⟨37032583324090332260304073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49376777765453776347072097 37032583324090332260304073)
    ·
      refine ⟨27774437493067749195228055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37032583324090332260304073 27774437493067749195228055)
      ·
        refine ⟨41661656239601623792842083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27774437493067749195228055 41661656239601623792842083)
        ·
          refine ⟨62492484359402435689263125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41661656239601623792842083 62492484359402435689263125)
          ·
            refine ⟨2929335204346989172934209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62492484359402435689263125 2929335204346989172934209)
            ·
              refine ⟨2197001403260241879700657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929335204346989172934209 2197001403260241879700657)
              ·
                refine ⟨1647751052445181409775493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197001403260241879700657 1647751052445181409775493)
                ·
                  refine ⟨308953322333471514332905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647751052445181409775493 308953322333471514332905)
                  ·
                    rfl

theorem cell22_2707580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_2707580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707580 prefixEnd_2707580 := by exact prefixLift 2707580
  have htrace : WordTrace (prefixWord ++ tailWord_2707580) baseStart_2707580 baseEnd_2707580 := by
    simpa [prefixWord, tailWord_2707580, baseEnd_2707580] using wordTrace_append hprefix tailTrace_2707580
  have hstable : (prefixWord ++ tailWord_2707580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707580).length < 2 ^ (prefixWord ++ tailWord_2707580).sum := by decide
  have hdescent : baseEnd_2707580 < baseStart_2707580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707608 : List Nat := [2, 1, 2, 4, 3, 1, 3, 6]
def baseStart_2707608 : Nat := 118140960795 + 2707608 * 2 ^ 59
def prefixEnd_2707608 : Nat := 4983230072969 + 3 ^ 40 * 2707608 * 2
def baseEnd_2707608 : Nat := 102985505774736867033181

theorem tailTrace_2707608 : CollatzResearch.WordTrace tailWord_2707608 prefixEnd_2707608 102985505774736867033181 := by
  unfold tailWord_2707608
  simp only [CollatzResearch.WordTrace]
  refine ⟨49377288387403056738081739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65836384516537408984108985 49377288387403056738081739)
  ·
    refine ⟨74065932581104585107122609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49377288387403056738081739 74065932581104585107122609)
    ·
      refine ⟨55549449435828438830341957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74065932581104585107122609 55549449435828438830341957)
      ·
        refine ⟨10415521769217832280689117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55549449435828438830341957 10415521769217832280689117)
        ·
          refine ⟨3905820663456687105258419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10415521769217832280689117 3905820663456687105258419)
          ·
            refine ⟨5858730995185030657887629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905820663456687105258419 5858730995185030657887629)
            ·
              refine ⟨2197024123194386496707861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5858730995185030657887629 2197024123194386496707861)
              ·
                refine ⟨102985505774736867033181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2197024123194386496707861 102985505774736867033181)
                ·
                  rfl

theorem cell22_2707608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 6].length) (baseStart_2707608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707608 prefixEnd_2707608 := by exact prefixLift 2707608
  have htrace : WordTrace (prefixWord ++ tailWord_2707608) baseStart_2707608 baseEnd_2707608 := by
    simpa [prefixWord, tailWord_2707608, baseEnd_2707608] using wordTrace_append hprefix tailTrace_2707608
  have hstable : (prefixWord ++ tailWord_2707608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707608).length < 2 ^ (prefixWord ++ tailWord_2707608).sum := by decide
  have hdescent : baseEnd_2707608 < baseStart_2707608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707610 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 2, 4]
def baseStart_2707610 : Nat := 118140960795 + 2707610 * 2 ^ 59
def prefixEnd_2707610 : Nat := 4983230072969 + 3 ^ 40 * 2707610 * 2
def baseEnd_2707610 : Nat := 926870236613504464748623

theorem tailTrace_2707610 : CollatzResearch.WordTrace tailWord_2707610 prefixEnd_2707610 926870236613504464748623 := by
  unfold tailWord_2707610
  simp only [CollatzResearch.WordTrace]
  refine ⟨24688662430199716954434071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65836433147199245211824189 24688662430199716954434071)
  ·
    refine ⟨37032993645299575431651107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24688662430199716954434071 37032993645299575431651107)
    ·
      refine ⟨55549490467949363147476661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37032993645299575431651107 55549490467949363147476661)
      ·
        refine ⟨5207764731370252795075937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55549490467949363147476661 5207764731370252795075937)
        ·
          refine ⟨3905823548527689596306953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5207764731370252795075937 3905823548527689596306953)
          ·
            refine ⟨2929367661395767197230215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3905823548527689596306953 2929367661395767197230215)
            ·
              refine ⟨4394051492093650795845323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929367661395767197230215 4394051492093650795845323)
              ·
                refine ⟨6591077238140476193767985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4394051492093650795845323 6591077238140476193767985)
                ·
                  refine ⟨4943307928605357145325989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6591077238140476193767985 4943307928605357145325989)
                  ·
                    refine ⟨926870236613504464748623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943307928605357145325989 926870236613504464748623)
                    ·
                      rfl

theorem cell22_2707610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_2707610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707610 prefixEnd_2707610 := by exact prefixLift 2707610
  have htrace : WordTrace (prefixWord ++ tailWord_2707610) baseStart_2707610 baseEnd_2707610 := by
    simpa [prefixWord, tailWord_2707610, baseEnd_2707610] using wordTrace_append hprefix tailTrace_2707610
  have hstable : (prefixWord ++ tailWord_2707610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707610).length < 2 ^ (prefixWord ++ tailWord_2707610).sum := by decide
  have hdescent : baseEnd_2707610 < baseStart_2707610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707698 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_2707698 : Nat := 118140960795 + 2707698 * 2 ^ 59
def prefixEnd_2707698 : Nat := 4983230072969 + 3 ^ 40 * 2707698 * 2
def baseEnd_2707698 : Nat := 308966786937300522849451

theorem tailTrace_2707698 : CollatzResearch.WordTrace tailWord_2707698 prefixEnd_2707698 308966786937300522849451 := by
  unfold tailWord_2707698
  simp only [CollatzResearch.WordTrace]
  refine ⟨24689464836120014711734937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65838572896320039231293165 24689464836120014711734937)
  ·
    refine ⟨18517098627090011033801203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24689464836120014711734937 18517098627090011033801203)
    ·
      refine ⟨27775647940635016550701805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18517098627090011033801203 27775647940635016550701805)
      ·
        refine ⟨10415867977738131206513177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27775647940635016550701805 10415867977738131206513177)
        ·
          refine ⟨7811900983303598404884883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10415867977738131206513177 7811900983303598404884883)
          ·
            refine ⟨11717851474955397607327325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7811900983303598404884883 11717851474955397607327325)
            ·
              refine ⟨4394194303108274102747747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11717851474955397607327325 4394194303108274102747747)
              ·
                refine ⟨6591291454662411154121621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4394194303108274102747747 6591291454662411154121621)
                ·
                  refine ⟨308966786937300522849451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6591291454662411154121621 308966786937300522849451)
                  ·
                    rfl

theorem cell22_2707698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_2707698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707698 prefixEnd_2707698 := by exact prefixLift 2707698
  have htrace : WordTrace (prefixWord ++ tailWord_2707698) baseStart_2707698 baseEnd_2707698 := by
    simpa [prefixWord, tailWord_2707698, baseEnd_2707698] using wordTrace_append hprefix tailTrace_2707698
  have hstable : (prefixWord ++ tailWord_2707698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707698).length < 2 ^ (prefixWord ++ tailWord_2707698).sum := by decide
  have hdescent : baseEnd_2707698 < baseStart_2707698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707711 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 4, 4]
def baseStart_2707711 : Nat := 118140960795 + 2707711 * 2 ^ 59
def prefixEnd_2707711 : Nat := 4983230072969 + 3 ^ 40 * 2707711 * 2
def baseEnd_2707711 : Nat := 926904810977573867973313

theorem tailTrace_2707711 : CollatzResearch.WordTrace tailWord_2707711 prefixEnd_2707711 926904810977573867973313 := by
  unfold tailWord_2707711
  simp only [CollatzResearch.WordTrace]
  refine ⟨98758333493432962067162987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65838888995621974711441991 98758333493432962067162987)
  ·
    refine ⟨148137500240149443100744481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98758333493432962067162987 148137500240149443100744481)
    ·
      refine ⟨111103125180112082325558361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148137500240149443100744481 111103125180112082325558361)
      ·
        refine ⟨83327343885084061744168771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111103125180112082325558361 83327343885084061744168771)
        ·
          refine ⟨124991015827626092616253157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83327343885084061744168771 124991015827626092616253157)
          ·
            refine ⟨23435815467679892365547467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124991015827626092616253157 23435815467679892365547467)
            ·
              refine ⟨35153723201519838548321201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23435815467679892365547467 35153723201519838548321201)
              ·
                refine ⟨26365292401139878911240901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35153723201519838548321201 26365292401139878911240901)
                ·
                  refine ⟨4943492325213727295857669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26365292401139878911240901 4943492325213727295857669)
                  ·
                    refine ⟨926904810977573867973313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943492325213727295857669 926904810977573867973313)
                    ·
                      rfl

theorem cell22_2707711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_2707711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707711 prefixEnd_2707711 := by exact prefixLift 2707711
  have htrace : WordTrace (prefixWord ++ tailWord_2707711) baseStart_2707711 baseEnd_2707711 := by
    simpa [prefixWord, tailWord_2707711, baseEnd_2707711] using wordTrace_append hprefix tailTrace_2707711
  have hstable : (prefixWord ++ tailWord_2707711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707711).length < 2 ^ (prefixWord ++ tailWord_2707711).sum := by decide
  have hdescent : baseEnd_2707711 < baseStart_2707711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707726 : List Nat := [4, 1, 1, 2, 1, 2, 1, 10]
def baseStart_2707726 : Nat := 118140960795 + 2707726 * 2 ^ 59
def prefixEnd_2707726 : Nat := 4983230072969 + 3 ^ 40 * 2707726 * 2
def baseEnd_2707726 : Nat := 102989993976013203205363

theorem tailTrace_2707726 : CollatzResearch.WordTrace tailWord_2707726 prefixEnd_2707726 102989993976013203205363 := by
  unfold tailWord_2707726
  simp only [CollatzResearch.WordTrace]
  refine ⟨12344860073547327453619879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65839253725585746419306021 12344860073547327453619879)
  ·
    refine ⟨18517290110320991180429819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12344860073547327453619879 18517290110320991180429819)
    ·
      refine ⟨27775935165481486770644729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18517290110320991180429819 27775935165481486770644729)
      ·
        refine ⟨20831951374111115077983547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27775935165481486770644729 20831951374111115077983547)
        ·
          refine ⟨31247927061166672616975321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20831951374111115077983547 31247927061166672616975321)
          ·
            refine ⟨23435945295875004462731491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31247927061166672616975321 23435945295875004462731491)
            ·
              refine ⟨35153917943812506694097237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23435945295875004462731491 35153917943812506694097237)
              ·
                refine ⟨102989993976013203205363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35153917943812506694097237 102989993976013203205363)
                ·
                  rfl

theorem cell22_2707726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_2707726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707726 prefixEnd_2707726 := by exact prefixLift 2707726
  have htrace : WordTrace (prefixWord ++ tailWord_2707726) baseStart_2707726 baseEnd_2707726 := by
    simpa [prefixWord, tailWord_2707726, baseEnd_2707726] using wordTrace_append hprefix tailTrace_2707726
  have hstable : (prefixWord ++ tailWord_2707726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707726).length < 2 ^ (prefixWord ++ tailWord_2707726).sum := by decide
  have hdescent : baseEnd_2707726 < baseStart_2707726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707749 : List Nat := [1, 3, 1, 2, 6, 1, 2, 2, 4]
def baseStart_2707749 : Nat := 118140960795 + 2707749 * 2 ^ 59
def prefixEnd_2707749 : Nat := 4983230072969 + 3 ^ 40 * 2707749 * 2
def baseEnd_2707749 : Nat := 308972606384718145174399

theorem tailTrace_2707749 : CollatzResearch.WordTrace tailWord_2707749 prefixEnd_2707749 308972606384718145174399 := by
  unfold tailWord_2707749
  simp only [CollatzResearch.WordTrace]
  refine ⟨98759719467295294557046301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65839812978196863038030867 98759719467295294557046301)
  ·
    refine ⟨37034894800235735458892363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98759719467295294557046301 37034894800235735458892363)
    ·
      refine ⟨55552342200353603188338545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37034894800235735458892363 55552342200353603188338545)
      ·
        refine ⟨41664256650265202391253909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55552342200353603188338545 41664256650265202391253909)
        ·
          refine ⟨1953012030481181362090027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41664256650265202391253909 1953012030481181362090027)
          ·
            refine ⟨2929518045721772043135041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1953012030481181362090027 2929518045721772043135041)
            ·
              refine ⟨2197138534291329032351281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929518045721772043135041 2197138534291329032351281)
              ·
                refine ⟨1647853900718496774263461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197138534291329032351281 1647853900718496774263461)
                ·
                  refine ⟨308972606384718145174399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647853900718496774263461 308972606384718145174399)
                  ·
                    rfl

theorem cell22_2707749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_2707749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707749 prefixEnd_2707749 := by exact prefixLift 2707749
  have htrace : WordTrace (prefixWord ++ tailWord_2707749) baseStart_2707749 baseEnd_2707749 := by
    simpa [prefixWord, tailWord_2707749, baseEnd_2707749] using wordTrace_append hprefix tailTrace_2707749
  have hstable : (prefixWord ++ tailWord_2707749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707749).length < 2 ^ (prefixWord ++ tailWord_2707749).sum := by decide
  have hdescent : baseEnd_2707749 < baseStart_2707749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707756 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_2707756 : Nat := 118140960795 + 2707756 * 2 ^ 59
def prefixEnd_2707756 : Nat := 4983230072969 + 3 ^ 40 * 2707756 * 2
def baseEnd_2707756 : Nat := 926920215397208750598175

theorem tailTrace_2707756 : CollatzResearch.WordTrace tailWord_2707756 prefixEnd_2707756 926920215397208750598175 := by
  unfold tailWord_2707756
  simp only [CollatzResearch.WordTrace]
  refine ⟨49379987389134967376275561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65839983185513289835034081 49379987389134967376275561)
  ·
    refine ⟨37034990541851225532206671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49379987389134967376275561 37034990541851225532206671)
    ·
      refine ⟨55552485812776838298310007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37034990541851225532206671 55552485812776838298310007)
      ·
        refine ⟨83328728719165257447465011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55552485812776838298310007 83328728719165257447465011)
        ·
          refine ⟨124993093078747886171197517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83328728719165257447465011 124993093078747886171197517)
          ·
            refine ⟨46872409904530457314199069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124993093078747886171197517 46872409904530457314199069)
            ·
              refine ⟨17577153714198921492824651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46872409904530457314199069 17577153714198921492824651)
              ·
                refine ⟨26365730571298382239236977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17577153714198921492824651 26365730571298382239236977)
                ·
                  refine ⟨19774297928473786679427733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26365730571298382239236977 19774297928473786679427733)
                  ·
                    refine ⟨926920215397208750598175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19774297928473786679427733 926920215397208750598175)
                    ·
                      rfl

theorem cell22_2707756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_2707756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707756 prefixEnd_2707756 := by exact prefixLift 2707756
  have htrace : WordTrace (prefixWord ++ tailWord_2707756) baseStart_2707756 baseEnd_2707756 := by
    simpa [prefixWord, tailWord_2707756, baseEnd_2707756] using wordTrace_append hprefix tailTrace_2707756
  have hstable : (prefixWord ++ tailWord_2707756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707756).length < 2 ^ (prefixWord ++ tailWord_2707756).sum := by decide
  have hdescent : baseEnd_2707756 < baseStart_2707756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707792 : List Nat := [2, 1, 1, 1, 1, 7, 2, 3, 1, 3]
def baseStart_2707792 : Nat := 118140960795 + 2707792 * 2 ^ 59
def prefixEnd_2707792 : Nat := 4983230072969 + 3 ^ 40 * 2707792 * 2
def baseEnd_2707792 : Nat := 926932538932916656698065

theorem tailTrace_2707792 : CollatzResearch.WordTrace tailWord_2707792 prefixEnd_2707792 926932538932916656698065 := by
  unfold tailWord_2707792
  simp only [CollatzResearch.WordTrace]
  refine ⟨49380643903069756450430815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65840858537426341933907753 49380643903069756450430815)
  ·
    refine ⟨74070965854604634675646223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49380643903069756450430815 74070965854604634675646223)
    ·
      refine ⟨111106448781906952013469335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74070965854604634675646223 111106448781906952013469335)
      ·
        refine ⟨166659673172860428020204003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111106448781906952013469335 166659673172860428020204003)
        ·
          refine ⟨249989509759290642030306005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166659673172860428020204003 249989509759290642030306005)
          ·
            refine ⟨5859129134983374422585297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 249989509759290642030306005 5859129134983374422585297)
            ·
              refine ⟨4394346851237530816938973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5859129134983374422585297 4394346851237530816938973)
              ·
                refine ⟨1647880069214074056352115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4394346851237530816938973 1647880069214074056352115)
                ·
                  refine ⟨2471820103821111084528173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647880069214074056352115 2471820103821111084528173)
                  ·
                    refine ⟨926932538932916656698065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2471820103821111084528173 926932538932916656698065)
                    ·
                      rfl

theorem cell22_2707792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 1, 3].length) (baseStart_2707792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707792 prefixEnd_2707792 := by exact prefixLift 2707792
  have htrace : WordTrace (prefixWord ++ tailWord_2707792) baseStart_2707792 baseEnd_2707792 := by
    simpa [prefixWord, tailWord_2707792, baseEnd_2707792] using wordTrace_append hprefix tailTrace_2707792
  have hstable : (prefixWord ++ tailWord_2707792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707792).length < 2 ^ (prefixWord ++ tailWord_2707792).sum := by decide
  have hdescent : baseEnd_2707792 < baseStart_2707792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707835 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 1, 4]
def baseStart_2707835 : Nat := 118140960795 + 2707835 * 2 ^ 59
def prefixEnd_2707835 : Nat := 4983230072969 + 3 ^ 40 * 2707835 * 2
def baseEnd_2707835 : Nat := 926947258711678877872933

theorem tailTrace_2707835 : CollatzResearch.WordTrace tailWord_2707835 prefixEnd_2707835 926947258711678877872933 := by
  unfold tailWord_2707835
  simp only [CollatzResearch.WordTrace]
  refine ⟨98762856144983731244676959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65841904096655820829784639 98762856144983731244676959)
  ·
    refine ⟨148144284217475596867015439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98762856144983731244676959 148144284217475596867015439)
    ·
      refine ⟨222216426326213395300523159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148144284217475596867015439 222216426326213395300523159)
      ·
        refine ⟨333324639489320092950784739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222216426326213395300523159 333324639489320092950784739)
        ·
          refine ⟨499986959233980139426177109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333324639489320092950784739 499986959233980139426177109)
          ·
            refine ⟨5859222178523204758900513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 499986959233980139426177109 5859222178523204758900513)
            ·
              refine ⟨4394416633892403569175385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5859222178523204758900513 4394416633892403569175385)
              ·
                refine ⟨3295812475419302676881539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4394416633892403569175385 3295812475419302676881539)
                ·
                  refine ⟨4943718713128954015322309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295812475419302676881539 4943718713128954015322309)
                  ·
                    refine ⟨926947258711678877872933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943718713128954015322309 926947258711678877872933)
                    ·
                      rfl

theorem cell22_2707835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 4].length) (baseStart_2707835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707835 prefixEnd_2707835 := by exact prefixLift 2707835
  have htrace : WordTrace (prefixWord ++ tailWord_2707835) baseStart_2707835 baseEnd_2707835 := by
    simpa [prefixWord, tailWord_2707835, baseEnd_2707835] using wordTrace_append hprefix tailTrace_2707835
  have hstable : (prefixWord ++ tailWord_2707835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707835).length < 2 ^ (prefixWord ++ tailWord_2707835).sum := by decide
  have hdescent : baseEnd_2707835 < baseStart_2707835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707848 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 3, 5]
def baseStart_2707848 : Nat := 118140960795 + 2707848 * 2 ^ 59
def prefixEnd_2707848 : Nat := 4983230072969 + 3 ^ 40 * 2707848 * 2
def baseEnd_2707848 : Nat := 926951708877351177297893

theorem tailTrace_2707848 : CollatzResearch.WordTrace tailWord_2707848 prefixEnd_2707848 926951708877351177297893 := by
  unfold tailWord_2707848
  simp only [CollatzResearch.WordTrace]
  refine ⟨49381665146968317232450099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65842220195957756309933465 49381665146968317232450099)
  ·
    refine ⟨74072497720452475848675149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49381665146968317232450099 74072497720452475848675149)
    ·
      refine ⟨27777186645169678443253181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74072497720452475848675149 27777186645169678443253181)
      ·
        refine ⟨10416444991938629416219943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27777186645169678443253181 10416444991938629416219943)
        ·
          refine ⟨15624667487907944124329915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10416444991938629416219943 15624667487907944124329915)
          ·
            refine ⟨23437001231861916186494873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15624667487907944124329915 23437001231861916186494873)
            ·
              refine ⟨17577750923896437139871155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23437001231861916186494873 17577750923896437139871155)
              ·
                refine ⟨26366626385844655709806733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17577750923896437139871155 26366626385844655709806733)
                ·
                  refine ⟨9887484894691745891177525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26366626385844655709806733 9887484894691745891177525)
                  ·
                    refine ⟨926951708877351177297893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9887484894691745891177525 926951708877351177297893)
                    ·
                      rfl

theorem cell22_2707848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_2707848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707848 prefixEnd_2707848 := by exact prefixLift 2707848
  have htrace : WordTrace (prefixWord ++ tailWord_2707848) baseStart_2707848 baseEnd_2707848 := by
    simpa [prefixWord, tailWord_2707848, baseEnd_2707848] using wordTrace_append hprefix tailTrace_2707848
  have hstable : (prefixWord ++ tailWord_2707848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707848).length < 2 ^ (prefixWord ++ tailWord_2707848).sum := by decide
  have hdescent : baseEnd_2707848 < baseStart_2707848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707863 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 4, 4]
def baseStart_2707863 : Nat := 118140960795 + 2707863 * 2 ^ 59
def prefixEnd_2707863 : Nat := 4983230072969 + 3 ^ 40 * 2707863 * 2
def baseEnd_2707863 : Nat := 926956843683896138172847

theorem tailTrace_2707863 : CollatzResearch.WordTrace tailWord_2707863 prefixEnd_2707863 926956843683896138172847 := by
  unfold tailWord_2707863
  simp only [CollatzResearch.WordTrace]
  refine ⟨98763877388882292026696243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65842584925921528017797495 98763877388882292026696243)
  ·
    refine ⟨148145816083323438040044365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98763877388882292026696243 148145816083323438040044365)
    ·
      refine ⟨55554681031246289265016637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148145816083323438040044365 55554681031246289265016637)
      ·
        refine ⟨20833005386717358474381239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55554681031246289265016637 20833005386717358474381239)
        ·
          refine ⟨31249508080076037711571859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20833005386717358474381239 31249508080076037711571859)
          ·
            refine ⟨46874262120114056567357789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31249508080076037711571859 46874262120114056567357789)
            ·
              refine ⟨17577848295042771212759171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46874262120114056567357789 17577848295042771212759171)
              ·
                refine ⟨26366772442564156819138757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17577848295042771212759171 26366772442564156819138757)
                ·
                  refine ⟨4943769832980779403588517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26366772442564156819138757 4943769832980779403588517)
                  ·
                    refine ⟨926956843683896138172847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943769832980779403588517 926956843683896138172847)
                    ·
                      rfl

theorem cell22_2707863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_2707863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707863 prefixEnd_2707863 := by exact prefixLift 2707863
  have htrace : WordTrace (prefixWord ++ tailWord_2707863) baseStart_2707863 baseEnd_2707863 := by
    simpa [prefixWord, tailWord_2707863, baseEnd_2707863] using wordTrace_append hprefix tailTrace_2707863
  have hstable : (prefixWord ++ tailWord_2707863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707863).length < 2 ^ (prefixWord ++ tailWord_2707863).sum := by decide
  have hdescent : baseEnd_2707863 < baseStart_2707863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707865 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 2, 3]
def baseStart_2707865 : Nat := 118140960795 + 2707865 * 2 ^ 59
def prefixEnd_2707865 : Nat := 4983230072969 + 3 ^ 40 * 2707865 * 2
def baseEnd_2707865 : Nat := 926957528324768799622841

theorem tailTrace_2707865 : CollatzResearch.WordTrace tailWord_2707865 prefixEnd_2707865 926957528324768799622841 := by
  unfold tailWord_2707865
  simp only [CollatzResearch.WordTrace]
  refine ⟨98763950334875046368269049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65842633556583364245512699 98763950334875046368269049)
  ·
    refine ⟨74072962751156284776201787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98763950334875046368269049 74072962751156284776201787)
    ·
      refine ⟨111109444126734427164302681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74072962751156284776201787 111109444126734427164302681)
      ·
        refine ⟨83332083095050820373227011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111109444126734427164302681 83332083095050820373227011)
        ·
          refine ⟨124998124642576230559840517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83332083095050820373227011 124998124642576230559840517)
          ·
            refine ⟨23437148370483043229970097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124998124642576230559840517 23437148370483043229970097)
            ·
              refine ⟨17577861277862282422477573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23437148370483043229970097 17577861277862282422477573)
              ·
                refine ⟨3295848989599177954214545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17577861277862282422477573 3295848989599177954214545)
                ·
                  refine ⟨2471886742199383465660909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3295848989599177954214545 2471886742199383465660909)
                  ·
                    refine ⟨926957528324768799622841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2471886742199383465660909 926957528324768799622841)
                    ·
                      rfl

theorem cell22_2707865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 3].length) (baseStart_2707865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707865 prefixEnd_2707865 := by exact prefixLift 2707865
  have htrace : WordTrace (prefixWord ++ tailWord_2707865) baseStart_2707865 baseEnd_2707865 := by
    simpa [prefixWord, tailWord_2707865, baseEnd_2707865] using wordTrace_append hprefix tailTrace_2707865
  have hstable : (prefixWord ++ tailWord_2707865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707865).length < 2 ^ (prefixWord ++ tailWord_2707865).sum := by decide
  have hdescent : baseEnd_2707865 < baseStart_2707865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707983 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 5, 5]
def baseStart_2707983 : Nat := 118140960795 + 2707983 * 2 ^ 59
def prefixEnd_2707983 : Nat := 4983230072969 + 3 ^ 40 * 2707983 * 2
def baseEnd_2707983 : Nat := 926997922136255825172479

theorem tailTrace_2707983 : CollatzResearch.WordTrace tailWord_2707983 prefixEnd_2707983 926997922136255825172479 := by
  unfold tailWord_2707983
  simp only [CollatzResearch.WordTrace]
  refine ⟨98768254148447552521064603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65845502765631701680709735 98768254148447552521064603)
  ·
    refine ⟨148152381222671328781596905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98768254148447552521064603 148152381222671328781596905)
    ·
      refine ⟨111114285917003496586197679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148152381222671328781596905 111114285917003496586197679)
      ·
        refine ⟨166671428875505244879296519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111114285917003496586197679 166671428875505244879296519)
        ·
          refine ⟨250007143313257867318944779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166671428875505244879296519 250007143313257867318944779)
          ·
            refine ⟨375010714969886800978417169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250007143313257867318944779 375010714969886800978417169)
            ·
              refine ⟨281258036227415100733812877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375010714969886800978417169 281258036227415100733812877)
              ·
                refine ⟨105471763585280662775179829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281258036227415100733812877 105471763585280662775179829)
                ·
                  refine ⟨9887977836120062135173109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105471763585280662775179829 9887977836120062135173109)
                  ·
                    refine ⟨926997922136255825172479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9887977836120062135173109 926997922136255825172479)
                    ·
                      rfl

theorem cell22_2707983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_2707983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2707983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2707983 prefixEnd_2707983 := by exact prefixLift 2707983
  have htrace : WordTrace (prefixWord ++ tailWord_2707983) baseStart_2707983 baseEnd_2707983 := by
    simpa [prefixWord, tailWord_2707983, baseEnd_2707983] using wordTrace_append hprefix tailTrace_2707983
  have hstable : (prefixWord ++ tailWord_2707983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707983).length < 2 ^ (prefixWord ++ tailWord_2707983).sum := by decide
  have hdescent : baseEnd_2707983 < baseStart_2707983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708066 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2708066 : Nat := 118140960795 + 2708066 * 2 ^ 59
def prefixEnd_2708066 : Nat := 4983230072969 + 3 ^ 40 * 2708066 * 2
def baseEnd_2708066 : Nat := 927026334732471275347225

theorem tailTrace_2708066 : CollatzResearch.WordTrace tailWord_2708066 prefixEnd_2708066 927026334732471275347225 := by
  unfold tailWord_2708066
  simp only [CollatzResearch.WordTrace]
  refine ⟨24692820351786714424084013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65847520938097905130890701 24692820351786714424084013)
  ·
    refine ⟨9259807631920017909031505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24692820351786714424084013 9259807631920017909031505)
    ·
      refine ⟨6944855723940013431773629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9259807631920017909031505 6944855723940013431773629)
      ·
        refine ⟨2604320896477505036915111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6944855723940013431773629 2604320896477505036915111)
        ·
          refine ⟨3906481344716257555372667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2604320896477505036915111 3906481344716257555372667)
          ·
            refine ⟨5859722017074386333059001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3906481344716257555372667 5859722017074386333059001)
            ·
              refine ⟨4394791512805789749794251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5859722017074386333059001 4394791512805789749794251)
              ·
                refine ⟨6592187269208684624691377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4394791512805789749794251 6592187269208684624691377)
                ·
                  refine ⟨4944140451906513468518533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6592187269208684624691377 4944140451906513468518533)
                  ·
                    refine ⟨927026334732471275347225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4944140451906513468518533 927026334732471275347225)
                    ·
                      rfl

theorem cell22_2708066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2708066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708066 prefixEnd_2708066 := by exact prefixLift 2708066
  have htrace : WordTrace (prefixWord ++ tailWord_2708066) baseStart_2708066 baseEnd_2708066 := by
    simpa [prefixWord, tailWord_2708066, baseEnd_2708066] using wordTrace_append hprefix tailTrace_2708066
  have hstable : (prefixWord ++ tailWord_2708066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708066).length < 2 ^ (prefixWord ++ tailWord_2708066).sum := by decide
  have hdescent : baseEnd_2708066 < baseStart_2708066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708096 : List Nat := [2, 1, 1, 2, 1, 5, 4, 2, 1, 3]
def baseStart_2708096 : Nat := 118140960795 + 2708096 * 2 ^ 59
def prefixEnd_2708096 : Nat := 4983230072969 + 3 ^ 40 * 2708096 * 2
def baseEnd_2708096 : Nat := 927036604345561197097133

theorem tailTrace_2708096 : CollatzResearch.WordTrace tailWord_2708096 prefixEnd_2708096 927036604345561197097133 := by
  unfold tailWord_2708096
  simp only [CollatzResearch.WordTrace]
  refine ⟨49386187798519086409964071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65848250398025448546618761 49386187798519086409964071)
  ·
    refine ⟨74079281697778629614946107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49386187798519086409964071 74079281697778629614946107)
    ·
      refine ⟨111118922546667944422419161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74079281697778629614946107 111118922546667944422419161)
      ·
        refine ⟨83339191910000958316814371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111118922546667944422419161 83339191910000958316814371)
        ·
          refine ⟨125008787865001437475221557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83339191910000958316814371 125008787865001437475221557)
          ·
            refine ⟨11719573862343884763302021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125008787865001437475221557 11719573862343884763302021)
            ·
              refine ⟨2197420099189478393119129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11719573862343884763302021 2197420099189478393119129)
              ·
                refine ⟨1648065074392108794839347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197420099189478393119129 1648065074392108794839347)
                ·
                  refine ⟨2472097611588163192259021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648065074392108794839347 2472097611588163192259021)
                  ·
                    refine ⟨927036604345561197097133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2472097611588163192259021 927036604345561197097133)
                    ·
                      rfl

theorem cell22_2708096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 1, 3].length) (baseStart_2708096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708096 prefixEnd_2708096 := by exact prefixLift 2708096
  have htrace : WordTrace (prefixWord ++ tailWord_2708096) baseStart_2708096 baseEnd_2708096 := by
    simpa [prefixWord, tailWord_2708096, baseEnd_2708096] using wordTrace_append hprefix tailTrace_2708096
  have hstable : (prefixWord ++ tailWord_2708096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708096).length < 2 ^ (prefixWord ++ tailWord_2708096).sum := by decide
  have hdescent : baseEnd_2708096 < baseStart_2708096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708098 : List Nat := [3, 4, 3, 1, 1, 2, 1, 7]
def baseStart_2708098 : Nat := 118140960795 + 2708098 * 2 ^ 59
def prefixEnd_2708098 : Nat := 4983230072969 + 3 ^ 40 * 2708098 * 2
def baseEnd_2708098 : Nat := 103004143220714873171903

theorem tailTrace_2708098 : CollatzResearch.WordTrace tailWord_2708098 prefixEnd_2708098 103004143220714873171903 := by
  unfold tailWord_2708098
  simp only [CollatzResearch.WordTrace]
  refine ⟨24693112135757731790375237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65848299028687284774333965 24693112135757731790375237)
  ·
    refine ⟨4629958525454574710695357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24693112135757731790375237 4629958525454574710695357)
    ·
      refine ⟨1736234447045465516510759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4629958525454574710695357 1736234447045465516510759)
      ·
        refine ⟨2604351670568198274766139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736234447045465516510759 2604351670568198274766139)
        ·
          refine ⟨3906527505852297412149209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2604351670568198274766139 3906527505852297412149209)
          ·
            refine ⟨2929895629389223059111907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3906527505852297412149209 2929895629389223059111907)
            ·
              refine ⟨4394843444083834588667861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929895629389223059111907 4394843444083834588667861)
              ·
                refine ⟨103004143220714873171903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4394843444083834588667861 103004143220714873171903)
                ·
                  rfl

theorem cell22_2708098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_2708098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708098 prefixEnd_2708098 := by exact prefixLift 2708098
  have htrace : WordTrace (prefixWord ++ tailWord_2708098) baseStart_2708098 baseEnd_2708098 := by
    simpa [prefixWord, tailWord_2708098, baseEnd_2708098] using wordTrace_append hprefix tailTrace_2708098
  have hstable : (prefixWord ++ tailWord_2708098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708098).length < 2 ^ (prefixWord ++ tailWord_2708098).sum := by decide
  have hdescent : baseEnd_2708098 < baseStart_2708098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708137 : List Nat := [1, 2, 1, 1, 1, 1, 2, 9, 4]
def baseStart_2708137 : Nat := 118140960795 + 2708137 * 2 ^ 59
def prefixEnd_2708137 : Nat := 4983230072969 + 3 ^ 40 * 2708137 * 2
def baseEnd_2708137 : Nat := 309016879827816918940669

theorem tailTrace_2708137 : CollatzResearch.WordTrace tailWord_2708137 prefixEnd_2708137 309016879827816918940669 := by
  unfold tailWord_2708137
  simp only [CollatzResearch.WordTrace]
  refine ⟨98773870989889636822170665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65849247326593091214780443 98773870989889636822170665)
  ·
    refine ⟨74080403242417227616627999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98773870989889636822170665 74080403242417227616627999)
    ·
      refine ⟨111120604863625841424941999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74080403242417227616627999 111120604863625841424941999)
      ·
        refine ⟨166680907295438762137412999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111120604863625841424941999 166680907295438762137412999)
        ·
          refine ⟨250021360943158143206119499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166680907295438762137412999 250021360943158143206119499)
          ·
            refine ⟨375032041414737214809179249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250021360943158143206119499 375032041414737214809179249)
            ·
              refine ⟨281274031061052911106884437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375032041414737214809179249 281274031061052911106884437)
              ·
                refine ⟨1648090025748356901016901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 281274031061052911106884437 1648090025748356901016901)
                ·
                  refine ⟨309016879827816918940669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648090025748356901016901 309016879827816918940669)
                  ·
                    rfl

theorem cell22_2708137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 4].length) (baseStart_2708137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708137 prefixEnd_2708137 := by exact prefixLift 2708137
  have htrace : WordTrace (prefixWord ++ tailWord_2708137) baseStart_2708137 baseEnd_2708137 := by
    simpa [prefixWord, tailWord_2708137, baseEnd_2708137] using wordTrace_append hprefix tailTrace_2708137
  have hstable : (prefixWord ++ tailWord_2708137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708137).length < 2 ^ (prefixWord ++ tailWord_2708137).sum := by decide
  have hdescent : baseEnd_2708137 < baseStart_2708137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708173 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2708173 : Nat := 118140960795 + 2708173 * 2 ^ 59
def prefixEnd_2708173 : Nat := 4983230072969 + 3 ^ 40 * 2708173 * 2
def baseEnd_2708173 : Nat := 927062963019158662921897

theorem tailTrace_2708173 : CollatzResearch.WordTrace tailWord_2708173 prefixEnd_2708173 927062963019158662921897 := by
  unfold tailWord_2708173
  simp only [CollatzResearch.WordTrace]
  refine ⟨98775184017759214970481173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65850122678506143313654115 98775184017759214970481173)
  ·
    refine ⟨4630086750832463201741305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98775184017759214970481173 4630086750832463201741305)
    ·
      refine ⟨3472565063124347401305979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4630086750832463201741305 3472565063124347401305979)
      ·
        refine ⟨5208847594686521101958969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472565063124347401305979 5208847594686521101958969)
        ·
          refine ⟨3906635696014890826469227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5208847594686521101958969 3906635696014890826469227)
          ·
            refine ⟨5859953544022336239703841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3906635696014890826469227 5859953544022336239703841)
            ·
              refine ⟨4394965158016752179777881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5859953544022336239703841 4394965158016752179777881)
              ·
                refine ⟨3296223868512564134833411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4394965158016752179777881 3296223868512564134833411)
                ·
                  refine ⟨4944335802768846202250117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296223868512564134833411 4944335802768846202250117)
                  ·
                    refine ⟨927062963019158662921897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4944335802768846202250117 927062963019158662921897)
                    ·
                      rfl

theorem cell22_2708173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2708173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708173 prefixEnd_2708173 := by exact prefixLift 2708173
  have htrace : WordTrace (prefixWord ++ tailWord_2708173) baseStart_2708173 baseEnd_2708173 := by
    simpa [prefixWord, tailWord_2708173, baseEnd_2708173] using wordTrace_append hprefix tailTrace_2708173
  have hstable : (prefixWord ++ tailWord_2708173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708173).length < 2 ^ (prefixWord ++ tailWord_2708173).sum := by decide
  have hdescent : baseEnd_2708173 < baseStart_2708173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708188 : List Nat := [2, 2, 5, 1, 1, 3, 1, 3, 4]
def baseStart_2708188 : Nat := 118140960795 + 2708188 * 2 ^ 59
def prefixEnd_2708188 : Nat := 4983230072969 + 3 ^ 40 * 2708188 * 2
def baseEnd_2708188 : Nat := 309022699275234541265617

theorem tailTrace_2708188 : CollatzResearch.WordTrace tailWord_2708188 prefixEnd_2708188 309022699275234541265617 := by
  unfold tailWord_2708188
  simp only [CollatzResearch.WordTrace]
  refine ⟨49387865556352436266138609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65850487408469915021518145 49387865556352436266138609)
  ·
    refine ⟨37040899167264327199603957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49387865556352436266138609 37040899167264327199603957)
    ·
      refine ⟨3472584296931030674962871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37040899167264327199603957 3472584296931030674962871)
      ·
        refine ⟨5208876445396546012444307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472584296931030674962871 5208876445396546012444307)
        ·
          refine ⟨7813314668094819018666461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208876445396546012444307 7813314668094819018666461)
          ·
            refine ⟨2929993000535557131999923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7813314668094819018666461 2929993000535557131999923)
            ·
              refine ⟨4394989500803335697999885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929993000535557131999923 4394989500803335697999885)
              ·
                refine ⟨1648121062801250886749957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4394989500803335697999885 1648121062801250886749957)
                ·
                  refine ⟨309022699275234541265617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648121062801250886749957 309022699275234541265617)
                  ·
                    rfl

theorem cell22_2708188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_2708188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708188 prefixEnd_2708188 := by exact prefixLift 2708188
  have htrace : WordTrace (prefixWord ++ tailWord_2708188) baseStart_2708188 baseEnd_2708188 := by
    simpa [prefixWord, tailWord_2708188, baseEnd_2708188] using wordTrace_append hprefix tailTrace_2708188
  have hstable : (prefixWord ++ tailWord_2708188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708188).length < 2 ^ (prefixWord ++ tailWord_2708188).sum := by decide
  have hdescent : baseEnd_2708188 < baseStart_2708188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708276 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_2708276 : Nat := 118140960795 + 2708276 * 2 ^ 59
def prefixEnd_2708276 : Nat := 4983230072969 + 3 ^ 40 * 2708276 * 2
def baseEnd_2708276 : Nat := 927098222024100727596581

theorem tailTrace_2708276 : CollatzResearch.WordTrace tailWord_2708276 prefixEnd_2708276 927098222024100727596581 := by
  unfold tailWord_2708276
  simp only [CollatzResearch.WordTrace]
  refine ⟨49389470368193031780740341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65852627157590709040987121 49389470368193031780740341)
  ·
    refine ⟨4630262847018096729444407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49389470368193031780740341 4630262847018096729444407)
    ·
      refine ⟨6945394270527145094166611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4630262847018096729444407 6945394270527145094166611)
      ·
        refine ⟨10418091405790717641249917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6945394270527145094166611 10418091405790717641249917)
        ·
          refine ⟨3906784277171519115468719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10418091405790717641249917 3906784277171519115468719)
          ·
            refine ⟨5860176415757278673203079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3906784277171519115468719 5860176415757278673203079)
            ·
              refine ⟨8790264623635918009804619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5860176415757278673203079 8790264623635918009804619)
              ·
                refine ⟨13185396935453877014706929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8790264623635918009804619 13185396935453877014706929)
                ·
                  refine ⟨9889047701590407761030197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13185396935453877014706929 9889047701590407761030197)
                  ·
                    refine ⟨927098222024100727596581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9889047701590407761030197 927098222024100727596581)
                    ·
                      rfl

theorem cell22_2708276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_2708276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708276 prefixEnd_2708276 := by exact prefixLift 2708276
  have htrace : WordTrace (prefixWord ++ tailWord_2708276) baseStart_2708276 baseEnd_2708276 := by
    simpa [prefixWord, tailWord_2708276, baseEnd_2708276] using wordTrace_append hprefix tailTrace_2708276
  have hstable : (prefixWord ++ tailWord_2708276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708276).length < 2 ^ (prefixWord ++ tailWord_2708276).sum := by decide
  have hdescent : baseEnd_2708276 < baseStart_2708276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708306 : List Nat := [3, 2, 2, 1, 1, 2, 4, 3, 4]
def baseStart_2708306 : Nat := 118140960795 + 2708306 * 2 ^ 59
def prefixEnd_2708306 : Nat := 4983230072969 + 3 ^ 40 * 2708306 * 2
def baseEnd_2708306 : Nat := 309036163879063549782163

theorem tailTrace_2708306 : CollatzResearch.WordTrace tailWord_2708306 prefixEnd_2708306 309036163879063549782163 := by
  unfold tailWord_2708306
  simp only [CollatzResearch.WordTrace]
  refine ⟨24695008731569344671268193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65853356617518252456715181 24695008731569344671268193)
  ·
    refine ⟨18521256548677008503451145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24695008731569344671268193 18521256548677008503451145)
    ·
      refine ⟨13890942411507756377588359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18521256548677008503451145 13890942411507756377588359)
      ·
        refine ⟨20836413617261634566382539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13890942411507756377588359 20836413617261634566382539)
        ·
          refine ⟨31254620425892451849573809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20836413617261634566382539 31254620425892451849573809)
          ·
            refine ⟨23440965319419338887180357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31254620425892451849573809 23440965319419338887180357)
            ·
              refine ⟨4395180997391126041346317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23440965319419338887180357 4395180997391126041346317)
              ·
                refine ⟨1648192874021672265504869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4395180997391126041346317 1648192874021672265504869)
                ·
                  refine ⟨309036163879063549782163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648192874021672265504869 309036163879063549782163)
                  ·
                    rfl

theorem cell22_2708306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_2708306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708306 prefixEnd_2708306 := by exact prefixLift 2708306
  have htrace : WordTrace (prefixWord ++ tailWord_2708306) baseStart_2708306 baseEnd_2708306 := by
    simpa [prefixWord, tailWord_2708306, baseEnd_2708306] using wordTrace_append hprefix tailTrace_2708306
  have hstable : (prefixWord ++ tailWord_2708306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708306).length < 2 ^ (prefixWord ++ tailWord_2708306).sum := by decide
  have hdescent : baseEnd_2708306 < baseStart_2708306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708347 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 2, 6]
def baseStart_2708347 : Nat := 118140960795 + 2708347 * 2 ^ 59
def prefixEnd_2708347 : Nat := 4983230072969 + 3 ^ 40 * 2708347 * 2
def baseEnd_2708347 : Nat := 927122526775080209071363

theorem tailTrace_2708347 : CollatzResearch.WordTrace tailWord_2708347 prefixEnd_2708347 927122526775080209071363 := by
  unfold tailWord_2708347
  simp only [CollatzResearch.WordTrace]
  refine ⟨98781530319128842687315295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65854353546085895124876863 98781530319128842687315295)
  ·
    refine ⟨148172295478693264030972943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98781530319128842687315295 148172295478693264030972943)
    ·
      refine ⟨222258443218039896046459415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148172295478693264030972943 222258443218039896046459415)
      ·
        refine ⟨333387664827059844069689123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222258443218039896046459415 333387664827059844069689123)
        ·
          refine ⟨500081497240589766104533685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333387664827059844069689123 500081497240589766104533685)
          ·
            refine ⟨46882640366305290572300033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 500081497240589766104533685 46882640366305290572300033)
            ·
              refine ⟨35161980274728967929225025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46882640366305290572300033 35161980274728967929225025)
              ·
                refine ⟨26371485206046725946918769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35161980274728967929225025 26371485206046725946918769)
                ·
                  refine ⟨19778613904535044460189077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26371485206046725946918769 19778613904535044460189077)
                  ·
                    refine ⟨927122526775080209071363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19778613904535044460189077 927122526775080209071363)
                    ·
                      rfl

theorem cell22_2708347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_2708347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708347 prefixEnd_2708347 := by exact prefixLift 2708347
  have htrace : WordTrace (prefixWord ++ tailWord_2708347) baseStart_2708347 baseEnd_2708347 := by
    simpa [prefixWord, tailWord_2708347, baseEnd_2708347] using wordTrace_append hprefix tailTrace_2708347
  have hstable : (prefixWord ++ tailWord_2708347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708347).length < 2 ^ (prefixWord ++ tailWord_2708347).sum := by decide
  have hdescent : baseEnd_2708347 < baseStart_2708347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708383 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 3, 3]
def baseStart_2708383 : Nat := 118140960795 + 2708383 * 2 ^ 59
def prefixEnd_2708383 : Nat := 4983230072969 + 3 ^ 40 * 2708383 * 2
def baseEnd_2708383 : Nat := 927134850310788115171253

theorem tailTrace_2708383 : CollatzResearch.WordTrace tailWord_2708383 prefixEnd_2708383 927134850310788115171253 := by
  unfold tailWord_2708383
  simp only [CollatzResearch.WordTrace]
  refine ⟨98782843346998420835625803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65855228897998947223750535 98782843346998420835625803)
  ·
    refine ⟨148174265020497631253438705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98782843346998420835625803 148174265020497631253438705)
    ·
      refine ⟨111130698765373223440079029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148174265020497631253438705 111130698765373223440079029)
      ·
        refine ⟨10418503009253739697507409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111130698765373223440079029 10418503009253739697507409)
        ·
          refine ⟨7813877256940304773130557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10418503009253739697507409 7813877256940304773130557)
          ·
            refine ⟨2930203971352614289923959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7813877256940304773130557 2930203971352614289923959)
            ·
              refine ⟨4395305957028921434885939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930203971352614289923959 4395305957028921434885939)
              ·
                refine ⟨6592958935543382152328909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4395305957028921434885939 6592958935543382152328909)
                ·
                  refine ⟨2472359600828768307123341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6592958935543382152328909 2472359600828768307123341)
                  ·
                    refine ⟨927134850310788115171253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2472359600828768307123341 927134850310788115171253)
                    ·
                      rfl

theorem cell22_2708383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 3].length) (baseStart_2708383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708383 prefixEnd_2708383 := by exact prefixLift 2708383
  have htrace : WordTrace (prefixWord ++ tailWord_2708383) baseStart_2708383 baseEnd_2708383 := by
    simpa [prefixWord, tailWord_2708383, baseEnd_2708383] using wordTrace_append hprefix tailTrace_2708383
  have hstable : (prefixWord ++ tailWord_2708383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708383).length < 2 ^ (prefixWord ++ tailWord_2708383).sum := by decide
  have hdescent : baseEnd_2708383 < baseStart_2708383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708490 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 2, 3]
def baseStart_2708490 : Nat := 118140960795 + 2708490 * 2 ^ 59
def prefixEnd_2708490 : Nat := 4983230072969 + 3 ^ 40 * 2708490 * 2
def baseEnd_2708490 : Nat := 927171478597475502745925

theorem tailTrace_2708490 : CollatzResearch.WordTrace tailWord_2708490 prefixEnd_2708490 927171478597475502745925 := by
  unfold tailWord_2708490
  simp only [CollatzResearch.WordTrace]
  refine ⟨24696686489402694527442731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65857830638407185406513949 24696686489402694527442731)
  ·
    refine ⟨37045029734104041791164097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24696686489402694527442731 37045029734104041791164097)
    ·
      refine ⟨27783772300578031343373073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37045029734104041791164097 27783772300578031343373073)
      ·
        refine ⟨20837829225433523507529805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27783772300578031343373073 20837829225433523507529805)
        ·
          refine ⟨7814185959537571315323677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20837829225433523507529805 7814185959537571315323677)
          ·
            refine ⟨2930319734826589243246379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7814185959537571315323677 2930319734826589243246379)
            ·
              refine ⟨4395479602239883864869569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930319734826589243246379 4395479602239883864869569)
              ·
                refine ⟨3296609701679912898652177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4395479602239883864869569 3296609701679912898652177)
                ·
                  refine ⟨2472457276259934673989133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3296609701679912898652177 2472457276259934673989133)
                  ·
                    refine ⟨927171478597475502745925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2472457276259934673989133 927171478597475502745925)
                    ·
                      rfl

theorem cell22_2708490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_2708490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708490 prefixEnd_2708490 := by exact prefixLift 2708490
  have htrace : WordTrace (prefixWord ++ tailWord_2708490) baseStart_2708490 baseEnd_2708490 := by
    simpa [prefixWord, tailWord_2708490, baseEnd_2708490] using wordTrace_append hprefix tailTrace_2708490
  have hstable : (prefixWord ++ tailWord_2708490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708490).length < 2 ^ (prefixWord ++ tailWord_2708490).sum := by decide
  have hdescent : baseEnd_2708490 < baseStart_2708490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708591 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 1, 5]
def baseStart_2708591 : Nat := 118140960795 + 2708591 * 2 ^ 59
def prefixEnd_2708591 : Nat := 4983230072969 + 3 ^ 40 * 2708591 * 2
def baseEnd_2708591 : Nat := 927206052961544905970615

theorem tailTrace_2708591 : CollatzResearch.WordTrace tailWord_2708591 prefixEnd_2708591 927206052961544905970615 := by
  unfold tailWord_2708591
  simp only [CollatzResearch.WordTrace]
  refine ⟨98790429730244872359197627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65860286486829914906131751 98790429730244872359197627)
  ·
    refine ⟨148185644595367308538796441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98790429730244872359197627 148185644595367308538796441)
    ·
      refine ⟨111139233446525481404097331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148185644595367308538796441 111139233446525481404097331)
      ·
        refine ⟨166708850169788222106145997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111139233446525481404097331 166708850169788222106145997)
        ·
          refine ⟨62515818813670583289804749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166708850169788222106145997 62515818813670583289804749)
          ·
            refine ⟨23443432055126468733676781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62515818813670583289804749 23443432055126468733676781)
            ·
              refine ⟨8791287020672425775128793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23443432055126468733676781 8791287020672425775128793)
              ·
                refine ⟨6593465265504319331346595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8791287020672425775128793 6593465265504319331346595)
                ·
                  refine ⟨9890197898256478997019893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6593465265504319331346595 9890197898256478997019893)
                  ·
                    refine ⟨927206052961544905970615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9890197898256478997019893 927206052961544905970615)
                    ·
                      rfl

theorem cell22_2708591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_2708591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708591 prefixEnd_2708591 := by exact prefixLift 2708591
  have htrace : WordTrace (prefixWord ++ tailWord_2708591) baseStart_2708591 baseEnd_2708591 := by
    simpa [prefixWord, tailWord_2708591, baseEnd_2708591] using wordTrace_append hprefix tailTrace_2708591
  have hstable : (prefixWord ++ tailWord_2708591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708591).length < 2 ^ (prefixWord ++ tailWord_2708591).sum := by decide
  have hdescent : baseEnd_2708591 < baseStart_2708591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708608 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 2, 3]
def baseStart_2708608 : Nat := 118140960795 + 2708608 * 2 ^ 59
def prefixEnd_2708608 : Nat := 4983230072969 + 3 ^ 40 * 2708608 * 2
def baseEnd_2708608 : Nat := 927211872408962528295563

theorem tailTrace_2708608 : CollatzResearch.WordTrace tailWord_2708608 prefixEnd_2708608 927211872408962528295563 := by
  unfold tailWord_2708608
  simp only [CollatzResearch.WordTrace]
  refine ⟨49395524885591642131283239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65860699847455522841710985 49395524885591642131283239)
  ·
    refine ⟨74093287328387463196924859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49395524885591642131283239 74093287328387463196924859)
    ·
      refine ⟨111139930992581194795387289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74093287328387463196924859 111139930992581194795387289)
      ·
        refine ⟨83354948244435896096540467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111139930992581194795387289 83354948244435896096540467)
        ·
          refine ⟨125032422366653844144810701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83354948244435896096540467 125032422366653844144810701)
          ·
            refine ⟨46887158387495191554304013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125032422366653844144810701 46887158387495191554304013)
            ·
              refine ⟨17582684395310696832864005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46887158387495191554304013 17582684395310696832864005)
              ·
                refine ⟨3296753324120755656162001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17582684395310696832864005 3296753324120755656162001)
                ·
                  refine ⟨2472564993090566742121501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3296753324120755656162001 2472564993090566742121501)
                  ·
                    refine ⟨927211872408962528295563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2472564993090566742121501 927211872408962528295563)
                    ·
                      rfl

theorem cell22_2708608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2, 3].length) (baseStart_2708608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708608 prefixEnd_2708608 := by exact prefixLift 2708608
  have htrace : WordTrace (prefixWord ++ tailWord_2708608) baseStart_2708608 baseEnd_2708608 := by
    simpa [prefixWord, tailWord_2708608, baseEnd_2708608] using wordTrace_append hprefix tailTrace_2708608
  have hstable : (prefixWord ++ tailWord_2708608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708608).length < 2 ^ (prefixWord ++ tailWord_2708608).sum := by decide
  have hdescent : baseEnd_2708608 < baseStart_2708608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708670 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 3, 3]
def baseStart_2708670 : Nat := 118140960795 + 2708670 * 2 ^ 59
def prefixEnd_2708670 : Nat := 4983230072969 + 3 ^ 40 * 2708670 * 2
def baseEnd_2708670 : Nat := 927233096276015033245373

theorem tailTrace_2708670 : CollatzResearch.WordTrace tailWord_2708670 prefixEnd_2708670 927233096276015033245373 := by
  unfold tailWord_2708670
  simp only [CollatzResearch.WordTrace]
  refine ⟨12349163887119833606415433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65862207397972445900882309 12349163887119833606415433)
  ·
    refine ⟨9261872915339875204811575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12349163887119833606415433 9261872915339875204811575)
    ·
      refine ⟨13892809373009812807217363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9261872915339875204811575 13892809373009812807217363)
      ·
        refine ⟨20839214059514719210826045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13892809373009812807217363 20839214059514719210826045)
        ·
          refine ⟨7814705272318019704059767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20839214059514719210826045 7814705272318019704059767)
          ·
            refine ⟨11722057908477029556089651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7814705272318019704059767 11722057908477029556089651)
            ·
              refine ⟨17583086862715544334134477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11722057908477029556089651 17583086862715544334134477)
              ·
                refine ⟨6593657573518329125300429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17583086862715544334134477 6593657573518329125300429)
                ·
                  refine ⟨2472621590069373421987661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6593657573518329125300429 2472621590069373421987661)
                  ·
                    refine ⟨927233096276015033245373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2472621590069373421987661 927233096276015033245373)
                    ·
                      rfl

theorem cell22_2708670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_2708670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708670 prefixEnd_2708670 := by exact prefixLift 2708670
  have htrace : WordTrace (prefixWord ++ tailWord_2708670) baseStart_2708670 baseEnd_2708670 := by
    simpa [prefixWord, tailWord_2708670, baseEnd_2708670] using wordTrace_append hprefix tailTrace_2708670
  have hstable : (prefixWord ++ tailWord_2708670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708670).length < 2 ^ (prefixWord ++ tailWord_2708670).sum := by decide
  have hdescent : baseEnd_2708670 < baseStart_2708670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708818 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_2708818 : Nat := 118140960795 + 2708818 * 2 ^ 59
def prefixEnd_2708818 : Nat := 4983230072969 + 3 ^ 40 * 2708818 * 2
def baseEnd_2708818 : Nat := 309094586566863993514973

theorem tailTrace_2708818 : CollatzResearch.WordTrace tailWord_2708818 prefixEnd_2708818 309094586566863993514973 := by
  unfold tailWord_2708818
  simp only [CollatzResearch.WordTrace]
  refine ⟨24699677275105622531927777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65865806066948326751807405 24699677275105622531927777)
  ·
    refine ⟨18524757956329216898945833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24699677275105622531927777 18524757956329216898945833)
    ·
      refine ⟨13893568467246912674209375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18524757956329216898945833 13893568467246912674209375)
      ·
        refine ⟨20840352700870369011314063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13893568467246912674209375 20840352700870369011314063)
        ·
          refine ⟨31260529051305553516971095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20840352700870369011314063 31260529051305553516971095)
          ·
            refine ⟨46890793576958330275456643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31260529051305553516971095 46890793576958330275456643)
            ·
              refine ⟨70336190365437495413184965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46890793576958330275456643 70336190365437495413184965)
              ·
                refine ⟨13188035693519530389972181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70336190365437495413184965 13188035693519530389972181)
                ·
                  refine ⟨309094586566863993514973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13188035693519530389972181 309094586566863993514973)
                  ·
                    rfl

theorem cell22_2708818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_2708818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708818 prefixEnd_2708818 := by exact prefixLift 2708818
  have htrace : WordTrace (prefixWord ++ tailWord_2708818) baseStart_2708818 baseEnd_2708818 := by
    simpa [prefixWord, tailWord_2708818, baseEnd_2708818] using wordTrace_append hprefix tailTrace_2708818
  have hstable : (prefixWord ++ tailWord_2708818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708818).length < 2 ^ (prefixWord ++ tailWord_2708818).sum := by decide
  have hdescent : baseEnd_2708818 < baseStart_2708818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708835 : List Nat := [1, 1, 1, 5, 2, 2, 3, 2, 5]
def baseStart_2708835 : Nat := 118140960795 + 2708835 * 2 ^ 59
def prefixEnd_2708835 : Nat := 4983230072969 + 3 ^ 40 * 2708835 * 2
def baseEnd_2708835 : Nat := 309096526382669867623289

theorem tailTrace_2708835 : CollatzResearch.WordTrace tailWord_2708835 prefixEnd_2708835 309096526382669867623289 := by
  unfold tailWord_2708835
  simp only [CollatzResearch.WordTrace]
  refine ⟨98799329141360902031079959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65866219427573934687386639 98799329141360902031079959)
  ·
    refine ⟨148198993712041353046619939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98799329141360902031079959 148198993712041353046619939)
    ·
      refine ⟨222298490568062029569929909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148198993712041353046619939 222298490568062029569929909)
      ·
        refine ⟨20840483490755815272180929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 222298490568062029569929909 20840483490755815272180929)
        ·
          refine ⟨15630362618066861454135697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20840483490755815272180929 15630362618066861454135697)
          ·
            refine ⟨11722771963550146090601773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15630362618066861454135697 11722771963550146090601773)
            ·
              refine ⟨4396039486331304783975665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11722771963550146090601773 4396039486331304783975665)
              ·
                refine ⟨3297029614748478587981749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4396039486331304783975665 3297029614748478587981749)
                ·
                  refine ⟨309096526382669867623289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3297029614748478587981749 309096526382669867623289)
                  ·
                    rfl

theorem cell22_2708835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 2, 5].length) (baseStart_2708835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708835 prefixEnd_2708835 := by exact prefixLift 2708835
  have htrace : WordTrace (prefixWord ++ tailWord_2708835) baseStart_2708835 baseEnd_2708835 := by
    simpa [prefixWord, tailWord_2708835, baseEnd_2708835] using wordTrace_append hprefix tailTrace_2708835
  have hstable : (prefixWord ++ tailWord_2708835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708835).length < 2 ^ (prefixWord ++ tailWord_2708835).sum := by decide
  have hdescent : baseEnd_2708835 < baseStart_2708835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708908 : List Nat := [2, 2, 1, 1, 1, 1, 5, 9]
def baseStart_2708908 : Nat := 118140960795 + 2708908 * 2 ^ 59
def prefixEnd_2708908 : Nat := 4983230072969 + 3 ^ 40 * 2708908 * 2
def baseEnd_2708908 : Nat := 103034952059984638421627

theorem tailTrace_2708908 : CollatzResearch.WordTrace tailWord_2708908 prefixEnd_2708908 103034952059984638421627 := by
  unfold tailWord_2708908
  simp only [CollatzResearch.WordTrace]
  refine ⟨49400995835048217749243689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65867994446730956998991585 49400995835048217749243689)
  ·
    refine ⟨37050746876286163311932767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49400995835048217749243689 37050746876286163311932767)
    ·
      refine ⟨55576120314429244967899151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37050746876286163311932767 55576120314429244967899151)
      ·
        refine ⟨83364180471643867451848727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55576120314429244967899151 83364180471643867451848727)
        ·
          refine ⟨125046270707465801177773091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83364180471643867451848727 125046270707465801177773091)
          ·
            refine ⟨187569406061198701766659637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125046270707465801177773091 187569406061198701766659637)
            ·
              refine ⟨17584631818237378290624341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187569406061198701766659637 17584631818237378290624341)
              ·
                refine ⟨103034952059984638421627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17584631818237378290624341 103034952059984638421627)
                ·
                  rfl

theorem cell22_2708908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 9].length) (baseStart_2708908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708908 prefixEnd_2708908 := by exact prefixLift 2708908
  have htrace : WordTrace (prefixWord ++ tailWord_2708908) baseStart_2708908 baseEnd_2708908 := by
    simpa [prefixWord, tailWord_2708908, baseEnd_2708908] using wordTrace_append hprefix tailTrace_2708908
  have hstable : (prefixWord ++ tailWord_2708908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708908).length < 2 ^ (prefixWord ++ tailWord_2708908).sum := by decide
  have hdescent : baseEnd_2708908 < baseStart_2708908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708948 : List Nat := [2, 4, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2708948 : Nat := 118140960795 + 2708948 * 2 ^ 59
def prefixEnd_2708948 : Nat := 4983230072969 + 3 ^ 40 * 2708948 * 2
def baseEnd_2708948 : Nat := 309109420452438324931507

theorem tailTrace_2708948 : CollatzResearch.WordTrace tailWord_2708948 prefixEnd_2708948 309109420452438324931507 := by
  unfold tailWord_2708948
  simp only [CollatzResearch.WordTrace]
  refine ⟨49401725294975761164971749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65868967059967681553295665 49401725294975761164971749)
  ·
    refine ⟨9262823492807955218432203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49401725294975761164971749 9262823492807955218432203)
    ·
      refine ⟨13894235239211932827648305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9262823492807955218432203 13894235239211932827648305)
      ·
        refine ⟨10420676429408949620736229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13894235239211932827648305 10420676429408949620736229)
        ·
          refine ⟨1953876830514178053888043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10420676429408949620736229 1953876830514178053888043)
          ·
            refine ⟨2930815245771267080832065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1953876830514178053888043 2930815245771267080832065)
            ·
              refine ⟨2198111434328450310624049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2930815245771267080832065 2198111434328450310624049)
              ·
                refine ⟨1648583575746337732968037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2198111434328450310624049 1648583575746337732968037)
                ·
                  refine ⟨309109420452438324931507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648583575746337732968037 309109420452438324931507)
                  ·
                    rfl

theorem cell22_2708948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2708948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2708948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2708948 prefixEnd_2708948 := by exact prefixLift 2708948
  have htrace : WordTrace (prefixWord ++ tailWord_2708948) baseStart_2708948 baseEnd_2708948 := by
    simpa [prefixWord, tailWord_2708948, baseEnd_2708948] using wordTrace_append hprefix tailTrace_2708948
  have hstable : (prefixWord ++ tailWord_2708948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708948).length < 2 ^ (prefixWord ++ tailWord_2708948).sum := by decide
  have hdescent : baseEnd_2708948 < baseStart_2708948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709004 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 5]
def baseStart_2709004 : Nat := 118140960795 + 2709004 * 2 ^ 59
def prefixEnd_2709004 : Nat := 4983230072969 + 3 ^ 40 * 2709004 * 2
def baseEnd_2709004 : Nat := 309115810433916498464783

theorem tailTrace_2709004 : CollatzResearch.WordTrace tailWord_2709004 prefixEnd_2709004 309115810433916498464783 := by
  unfold tailWord_2709004
  simp only [CollatzResearch.WordTrace]
  refine ⟨49402746538874321946991033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65870328718499095929321377 49402746538874321946991033)
  ·
    refine ⟨37052059904155741460243275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49402746538874321946991033 37052059904155741460243275)
    ·
      refine ⟨55578089856233612190364913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37052059904155741460243275 55578089856233612190364913)
      ·
        refine ⟨41683567392175209142773685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55578089856233612190364913 41683567392175209142773685)
        ·
          refine ⟨3907834443016425857135033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41683567392175209142773685 3907834443016425857135033)
          ·
            refine ⟨2930875832262319392851275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3907834443016425857135033 2930875832262319392851275)
            ·
              refine ⟨4396313748393479089276913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930875832262319392851275 4396313748393479089276913)
              ·
                refine ⟨3297235311295109316957685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4396313748393479089276913 3297235311295109316957685)
                ·
                  refine ⟨309115810433916498464783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3297235311295109316957685 309115810433916498464783)
                  ·
                    rfl

theorem cell22_2709004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_2709004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709004 prefixEnd_2709004 := by exact prefixLift 2709004
  have htrace : WordTrace (prefixWord ++ tailWord_2709004) baseStart_2709004 baseEnd_2709004 := by
    simpa [prefixWord, tailWord_2709004, baseEnd_2709004] using wordTrace_append hprefix tailTrace_2709004
  have hstable : (prefixWord ++ tailWord_2709004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709004).length < 2 ^ (prefixWord ++ tailWord_2709004).sum := by decide
  have hdescent : baseEnd_2709004 < baseStart_2709004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709034 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2709034 : Nat := 118140960795 + 2709034 * 2 ^ 59
def prefixEnd_2709034 : Nat := 4983230072969 + 3 ^ 40 * 2709034 * 2
def baseEnd_2709034 : Nat := 927357700914839417144257

theorem tailTrace_2709034 : CollatzResearch.WordTrace tailWord_2709034 prefixEnd_2709034 927357700914839417144257 := by
  unfold tailWord_2709034
  simp only [CollatzResearch.WordTrace]
  refine ⟨24701646816909989754393539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65871058178426639345049437 24701646816909989754393539)
  ·
    refine ⟨37052470225364984631590309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24701646816909989754393539 37052470225364984631590309)
    ·
      refine ⟨6947338167255934618423183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37052470225364984631590309 6947338167255934618423183)
      ·
        refine ⟨10421007250883901927634775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6947338167255934618423183 10421007250883901927634775)
        ·
          refine ⟨15631510876325852891452163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10421007250883901927634775 15631510876325852891452163)
          ·
            refine ⟨23447266314488779337178245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15631510876325852891452163 23447266314488779337178245)
            ·
              refine ⟨4396362433966646125720921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23447266314488779337178245 4396362433966646125720921)
              ·
                refine ⟨3297271825474984594290691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4396362433966646125720921 3297271825474984594290691)
                ·
                  refine ⟨4945907738212476891436037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297271825474984594290691 4945907738212476891436037)
                  ·
                    refine ⟨927357700914839417144257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4945907738212476891436037 927357700914839417144257)
                    ·
                      rfl

theorem cell22_2709034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2709034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709034 prefixEnd_2709034 := by exact prefixLift 2709034
  have htrace : WordTrace (prefixWord ++ tailWord_2709034) baseStart_2709034 baseEnd_2709034 := by
    simpa [prefixWord, tailWord_2709034, baseEnd_2709034] using wordTrace_append hprefix tailTrace_2709034
  have hstable : (prefixWord ++ tailWord_2709034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709034).length < 2 ^ (prefixWord ++ tailWord_2709034).sum := by decide
  have hdescent : baseEnd_2709034 < baseStart_2709034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709047 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 4, 3]
def baseStart_2709047 : Nat := 118140960795 + 2709047 * 2 ^ 59
def prefixEnd_2709047 : Nat := 4983230072969 + 3 ^ 40 * 2709047 * 2
def baseEnd_2709047 : Nat := 927362151080511716569217

theorem tailTrace_2709047 : CollatzResearch.WordTrace tailWord_2709047 prefixEnd_2709047 927362151080511716569217 := by
  unfold tailWord_2709047
  simp only [CollatzResearch.WordTrace]
  refine ⟨98807061416592862237797395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65871374277728574825198263 98807061416592862237797395)
  ·
    refine ⟨148210592124889293356696093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98807061416592862237797395 148210592124889293356696093)
    ·
      refine ⟨55578972046833485008761035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148210592124889293356696093 55578972046833485008761035)
      ·
        refine ⟨83368458070250227513141553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55578972046833485008761035 83368458070250227513141553)
        ·
          refine ⟨62526343552687670634856165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83368458070250227513141553 62526343552687670634856165)
          ·
            refine ⟨11723689416128938244035531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62526343552687670634856165 11723689416128938244035531)
            ·
              refine ⟨17585534124193407366053297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11723689416128938244035531 17585534124193407366053297)
              ·
                refine ⟨13189150593145055524539973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17585534124193407366053297 13189150593145055524539973)
                ·
                  refine ⟨2472965736214697910851245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13189150593145055524539973 2472965736214697910851245)
                  ·
                    refine ⟨927362151080511716569217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2472965736214697910851245 927362151080511716569217)
                    ·
                      rfl

theorem cell22_2709047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_2709047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709047 prefixEnd_2709047 := by exact prefixLift 2709047
  have htrace : WordTrace (prefixWord ++ tailWord_2709047) baseStart_2709047 baseEnd_2709047 := by
    simpa [prefixWord, tailWord_2709047, baseEnd_2709047] using wordTrace_append hprefix tailTrace_2709047
  have hstable : (prefixWord ++ tailWord_2709047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709047).length < 2 ^ (prefixWord ++ tailWord_2709047).sum := by decide
  have hdescent : baseEnd_2709047 < baseStart_2709047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709049 : List Nat := [1, 2, 1, 5, 1, 2, 3, 3, 4]
def baseStart_2709049 : Nat := 118140960795 + 2709049 * 2 ^ 59
def prefixEnd_2709049 : Nat := 4983230072969 + 3 ^ 40 * 2709049 * 2
def baseEnd_2709049 : Nat := 309120945240461459339737

theorem tailTrace_2709049 : CollatzResearch.WordTrace tailWord_2709049 prefixEnd_2709049 309120945240461459339737 := by
  unfold tailWord_2709049
  simp only [CollatzResearch.WordTrace]
  refine ⟨98807134362585616579370201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65871422908390411052913467 98807134362585616579370201)
  ·
    refine ⟨74105350771939212434527651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98807134362585616579370201 74105350771939212434527651)
    ·
      refine ⟨111158026157908818651791477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74105350771939212434527651 111158026157908818651791477)
      ·
        refine ⟨10421064952303951748605451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111158026157908818651791477 10421064952303951748605451)
        ·
          refine ⟨15631597428455927622908177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10421064952303951748605451 15631597428455927622908177)
          ·
            refine ⟨11723698071341945717181133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15631597428455927622908177 11723698071341945717181133)
            ·
              refine ⟨4396386776753229643942925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11723698071341945717181133 4396386776753229643942925)
              ·
                refine ⟨1648645041282461116478597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4396386776753229643942925 1648645041282461116478597)
                ·
                  refine ⟨309120945240461459339737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648645041282461116478597 309120945240461459339737)
                  ·
                    rfl

theorem cell22_2709049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 4].length) (baseStart_2709049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709049 prefixEnd_2709049 := by exact prefixLift 2709049
  have htrace : WordTrace (prefixWord ++ tailWord_2709049) baseStart_2709049 baseEnd_2709049 := by
    simpa [prefixWord, tailWord_2709049, baseEnd_2709049] using wordTrace_append hprefix tailTrace_2709049
  have hstable : (prefixWord ++ tailWord_2709049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709049).length < 2 ^ (prefixWord ++ tailWord_2709049).sum := by decide
  have hdescent : baseEnd_2709049 < baseStart_2709049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709085 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2709085 : Nat := 118140960795 + 2709085 * 2 ^ 59
def prefixEnd_2709085 : Nat := 4983230072969 + 3 ^ 40 * 2709085 * 2
def baseEnd_2709085 : Nat := 927375159257092284119101

theorem tailTrace_2709085 : CollatzResearch.WordTrace tailWord_2709085 prefixEnd_2709085 927375159257092284119101 := by
  unfold tailWord_2709085
  simp only [CollatzResearch.WordTrace]
  refine ⟨98808447390455194727680709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65872298260303463151787139 98808447390455194727680709)
  ·
    refine ⟨18526583885710349011440133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98808447390455194727680709 18526583885710349011440133)
    ·
      refine ⟨3473734478570690439645025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18526583885710349011440133 3473734478570690439645025)
      ·
        refine ⟨2605300858928017829733769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3473734478570690439645025 2605300858928017829733769)
        ·
          refine ⟨1953975644196013372300327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2605300858928017829733769 1953975644196013372300327)
          ·
            refine ⟨2930963466294020058450491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1953975644196013372300327 2930963466294020058450491)
            ·
              refine ⟨4396445199441030087675737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930963466294020058450491 4396445199441030087675737)
              ·
                refine ⟨3297333899580772565756803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4396445199441030087675737 3297333899580772565756803)
                ·
                  refine ⟨4946000849371158848635205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297333899580772565756803 4946000849371158848635205)
                  ·
                    refine ⟨927375159257092284119101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4946000849371158848635205 927375159257092284119101)
                    ·
                      rfl

theorem cell22_2709085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2709085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709085 prefixEnd_2709085 := by exact prefixLift 2709085
  have htrace : WordTrace (prefixWord ++ tailWord_2709085) baseStart_2709085 baseEnd_2709085 := by
    simpa [prefixWord, tailWord_2709085, baseEnd_2709085] using wordTrace_append hprefix tailTrace_2709085
  have hstable : (prefixWord ++ tailWord_2709085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709085).length < 2 ^ (prefixWord ++ tailWord_2709085).sum := by decide
  have hdescent : baseEnd_2709085 < baseStart_2709085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709105 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 9]
def baseStart_2709105 : Nat := 118140960795 + 2709105 * 2 ^ 59
def prefixEnd_2709105 : Nat := 4983230072969 + 3 ^ 40 * 2709105 * 2
def baseEnd_2709105 : Nat := 309127335221939632873013

theorem tailTrace_2709105 : CollatzResearch.WordTrace tailWord_2709105 prefixEnd_2709105 309127335221939632873013 := by
  unfold tailWord_2709105
  simp only [CollatzResearch.WordTrace]
  refine ⟨98809176850382738143408769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65872784566921825428939179 98809176850382738143408769)
  ·
    refine ⟨74106882637787053607556577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98809176850382738143408769 74106882637787053607556577)
    ·
      refine ⟨55580161978340290205667433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74106882637787053607556577 55580161978340290205667433)
      ·
        refine ⟨41685121483755217654250575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55580161978340290205667433 41685121483755217654250575)
        ·
          refine ⟨62527682225632826481375863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41685121483755217654250575 62527682225632826481375863)
          ·
            refine ⟨93791523338449239722063795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62527682225632826481375863 93791523338449239722063795)
            ·
              refine ⟨140687285007673859583095693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93791523338449239722063795 140687285007673859583095693)
              ·
                refine ⟨52757731877877697343660885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140687285007673859583095693 52757731877877697343660885)
                ·
                  refine ⟨309127335221939632873013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52757731877877697343660885 309127335221939632873013)
                  ·
                    rfl

theorem cell22_2709105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_2709105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709105 prefixEnd_2709105 := by exact prefixLift 2709105
  have htrace : WordTrace (prefixWord ++ tailWord_2709105) baseStart_2709105 baseEnd_2709105 := by
    simpa [prefixWord, tailWord_2709105, baseEnd_2709105] using wordTrace_append hprefix tailTrace_2709105
  have hstable : (prefixWord ++ tailWord_2709105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709105).length < 2 ^ (prefixWord ++ tailWord_2709105).sum := by decide
  have hdescent : baseEnd_2709105 < baseStart_2709105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709135 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 1, 10]
def baseStart_2709135 : Nat := 118140960795 + 2709135 * 2 ^ 59
def prefixEnd_2709135 : Nat := 4983230072969 + 3 ^ 40 * 2709135 * 2
def baseEnd_2709135 : Nat := 927392275278908820368947

theorem tailTrace_2709135 : CollatzResearch.WordTrace tailWord_2709135 prefixEnd_2709135 927392275278908820368947 := by
  unfold tailWord_2709135
  simp only [CollatzResearch.WordTrace]
  refine ⟨98810271040274053267000859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65873514026849368844667239 98810271040274053267000859)
  ·
    refine ⟨148215406560411079900501289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98810271040274053267000859 148215406560411079900501289)
    ·
      refine ⟨111161554920308309925375967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148215406560411079900501289 111161554920308309925375967)
      ·
        refine ⟨166742332380462464888063951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111161554920308309925375967 166742332380462464888063951)
        ·
          refine ⟨250113498570693697332095927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166742332380462464888063951 250113498570693697332095927)
          ·
            refine ⟨375170247856040545998143891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250113498570693697332095927 375170247856040545998143891)
            ·
              refine ⟨562755371784060818997215837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375170247856040545998143891 562755371784060818997215837)
              ·
                refine ⟨211033264419022807123955939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 562755371784060818997215837 211033264419022807123955939)
                ·
                  refine ⟨316549896628534210685933909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211033264419022807123955939 316549896628534210685933909)
                  ·
                    refine ⟨927392275278908820368947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 316549896628534210685933909 927392275278908820368947)
                    ·
                      rfl

theorem cell22_2709135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_2709135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709135 prefixEnd_2709135 := by exact prefixLift 2709135
  have htrace : WordTrace (prefixWord ++ tailWord_2709135) baseStart_2709135 baseEnd_2709135 := by
    simpa [prefixWord, tailWord_2709135, baseEnd_2709135] using wordTrace_append hprefix tailTrace_2709135
  have hstable : (prefixWord ++ tailWord_2709135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709135).length < 2 ^ (prefixWord ++ tailWord_2709135).sum := by decide
  have hdescent : baseEnd_2709135 < baseStart_2709135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709173 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 5]
def baseStart_2709173 : Nat := 118140960795 + 2709173 * 2 ^ 59
def prefixEnd_2709173 : Nat := 4983230072969 + 3 ^ 40 * 2709173 * 2
def baseEnd_2709173 : Nat := 309135094485163129306277

theorem tailTrace_2709173 : CollatzResearch.WordTrace tailWord_2709173 prefixEnd_2709173 309135094485163129306277 := by
  unfold tailWord_2709173
  simp only [CollatzResearch.WordTrace]
  refine ⟨98811657014136385756884173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65874438009424257171256115 98811657014136385756884173)
  ·
    refine ⟨37054371380301144658831565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98811657014136385756884173 37054371380301144658831565)
    ·
      refine ⟨13895389267612929247061837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37054371380301144658831565 13895389267612929247061837)
      ·
        refine ⟨5210770975354848467648189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13895389267612929247061837 5210770975354848467648189)
        ·
          refine ⟨1954039115758068175368071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5210770975354848467648189 1954039115758068175368071)
          ·
            refine ⟨2931058673637102263052107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954039115758068175368071 2931058673637102263052107)
            ·
              refine ⟨4396588010455653394578161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931058673637102263052107 4396588010455653394578161)
              ·
                refine ⟨3297441007841740045933621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4396588010455653394578161 3297441007841740045933621)
                ·
                  refine ⟨309135094485163129306277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3297441007841740045933621 309135094485163129306277)
                  ·
                    rfl

theorem cell22_2709173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_2709173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709173 prefixEnd_2709173 := by exact prefixLift 2709173
  have htrace : WordTrace (prefixWord ++ tailWord_2709173) baseStart_2709173 baseEnd_2709173 := by
    simpa [prefixWord, tailWord_2709173, baseEnd_2709173] using wordTrace_append hprefix tailTrace_2709173
  have hstable : (prefixWord ++ tailWord_2709173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709173).length < 2 ^ (prefixWord ++ tailWord_2709173).sum := by decide
  have hdescent : baseEnd_2709173 < baseStart_2709173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709184 : List Nat := [2, 1, 1, 2, 4, 1, 1, 6, 4]
def baseStart_2709184 : Nat := 118140960795 + 2709184 * 2 ^ 59
def prefixEnd_2709184 : Nat := 4983230072969 + 3 ^ 40 * 2709184 * 2
def baseEnd_2709184 : Nat := 309136349660096341964599

theorem tailTrace_2709184 : CollatzResearch.WordTrace tailWord_2709184 prefixEnd_2709184 309136349660096341964599 := by
  unfold tailWord_2709184
  simp only [CollatzResearch.WordTrace]
  refine ⟨49406029108548267317767303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65874705478064356423689737 49406029108548267317767303)
  ·
    refine ⟨74109043662822400976650955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49406029108548267317767303 74109043662822400976650955)
    ·
      refine ⟨111163565494233601464976433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74109043662822400976650955 111163565494233601464976433)
      ·
        refine ⟨83372674120675201098732325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111163565494233601464976433 83372674120675201098732325)
        ·
          refine ⟨15632376397626600206012311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83372674120675201098732325 15632376397626600206012311)
          ·
            refine ⟨23448564596439900309018467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15632376397626600206012311 23448564596439900309018467)
            ·
              refine ⟨35172846894659850463527701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23448564596439900309018467 35172846894659850463527701)
              ·
                refine ⟨1648727198187180490477861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35172846894659850463527701 1648727198187180490477861)
                ·
                  refine ⟨309136349660096341964599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648727198187180490477861 309136349660096341964599)
                  ·
                    rfl

theorem cell22_2709184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 4].length) (baseStart_2709184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709184 prefixEnd_2709184 := by exact prefixLift 2709184
  have htrace : WordTrace (prefixWord ++ tailWord_2709184) baseStart_2709184 baseEnd_2709184 := by
    simpa [prefixWord, tailWord_2709184, baseEnd_2709184] using wordTrace_append hprefix tailTrace_2709184
  have hstable : (prefixWord ++ tailWord_2709184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709184).length < 2 ^ (prefixWord ++ tailWord_2709184).sum := by decide
  have hdescent : baseEnd_2709184 < baseStart_2709184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709190 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_2709190 : Nat := 118140960795 + 2709190 * 2 ^ 59
def prefixEnd_2709190 : Nat := 4983230072969 + 3 ^ 40 * 2709190 * 2
def baseEnd_2709190 : Nat := 309137034300969003414593

theorem tailTrace_2709190 : CollatzResearch.WordTrace tailWord_2709190 prefixEnd_2709190 309137034300969003414593 := by
  unfold tailWord_2709190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3087883657971087426882907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65874851370049865106835349 3087883657971087426882907)
  ·
    refine ⟨4631825486956631140324361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3087883657971087426882907 4631825486956631140324361)
    ·
      refine ⟨3473869115217473355243271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4631825486956631140324361 3473869115217473355243271)
      ·
        refine ⟨5210803672826210032864907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3473869115217473355243271 5210803672826210032864907)
        ·
          refine ⟨7816205509239315049297361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5210803672826210032864907 7816205509239315049297361)
          ·
            refine ⟨5862154131929486286973021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7816205509239315049297361 5862154131929486286973021)
            ·
              refine ⟨2198307799473557357614883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5862154131929486286973021 2198307799473557357614883)
              ·
                refine ⟨3297461699210336036422325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198307799473557357614883 3297461699210336036422325)
                ·
                  refine ⟨309137034300969003414593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3297461699210336036422325 309137034300969003414593)
                  ·
                    rfl

theorem cell22_2709190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_2709190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709190 prefixEnd_2709190 := by exact prefixLift 2709190
  have htrace : WordTrace (prefixWord ++ tailWord_2709190) baseStart_2709190 baseEnd_2709190 := by
    simpa [prefixWord, tailWord_2709190, baseEnd_2709190] using wordTrace_append hprefix tailTrace_2709190
  have hstable : (prefixWord ++ tailWord_2709190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709190).length < 2 ^ (prefixWord ++ tailWord_2709190).sum := by decide
  have hdescent : baseEnd_2709190 < baseStart_2709190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709199 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 2, 3]
def baseStart_2709199 : Nat := 118140960795 + 2709199 * 2 ^ 59
def prefixEnd_2709199 : Nat := 4983230072969 + 3 ^ 40 * 2709199 * 2
def baseEnd_2709199 : Nat := 927414183786833986768751

theorem tailTrace_2709199 : CollatzResearch.WordTrace tailWord_2709199 prefixEnd_2709199 927414183786833986768751 := by
  unfold tailWord_2709199
  simp only [CollatzResearch.WordTrace]
  refine ⟨98812605312042192197330651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65875070208028128131553767 98812605312042192197330651)
  ·
    refine ⟨148218907968063288295995977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98812605312042192197330651 148218907968063288295995977)
    ·
      refine ⟨111164180976047466221996983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148218907968063288295995977 111164180976047466221996983)
      ·
        refine ⟨166746271464071199332995475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111164180976047466221996983 166746271464071199332995475)
        ·
          refine ⟨250119407196106798999493213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166746271464071199332995475 250119407196106798999493213)
          ·
            refine ⟨93794777698540049624809955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250119407196106798999493213 93794777698540049624809955)
            ·
              refine ⟨140692166547810074437214933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93794777698540049624809955 140692166547810074437214933)
              ·
                refine ⟨3297472653464298619622225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 140692166547810074437214933 3297472653464298619622225)
                ·
                  refine ⟨2473104490098223964716669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3297472653464298619622225 2473104490098223964716669)
                  ·
                    refine ⟨927414183786833986768751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2473104490098223964716669 927414183786833986768751)
                    ·
                      rfl

theorem cell22_2709199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 3].length) (baseStart_2709199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709199 prefixEnd_2709199 := by exact prefixLift 2709199
  have htrace : WordTrace (prefixWord ++ tailWord_2709199) baseStart_2709199 baseEnd_2709199 := by
    simpa [prefixWord, tailWord_2709199, baseEnd_2709199] using wordTrace_append hprefix tailTrace_2709199
  have hstable : (prefixWord ++ tailWord_2709199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709199).length < 2 ^ (prefixWord ++ tailWord_2709199).sum := by decide
  have hdescent : baseEnd_2709199 < baseStart_2709199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709229 : List Nat := [1, 5, 1, 2, 1, 4, 8]
def baseStart_2709229 : Nat := 118140960795 + 2709229 * 2 ^ 59
def prefixEnd_2709229 : Nat := 4983230072969 + 3 ^ 40 * 2709229 * 2
def baseEnd_2709229 : Nat := 34349053829626811426617

theorem tailTrace_2709229 : CollatzResearch.WordTrace tailWord_2709229 prefixEnd_2709229 34349053829626811426617 := by
  unfold tailWord_2709229
  simp only [CollatzResearch.WordTrace]
  refine ⟨98813699501933507320922741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65875799667955671547281827 98813699501933507320922741)
  ·
    refine ⟨9263784328306266311336507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98813699501933507320922741 9263784328306266311336507)
    ·
      refine ⟨13895676492459399467004761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9263784328306266311336507 13895676492459399467004761)
      ·
        refine ⟨10421757369344549600253571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13895676492459399467004761 10421757369344549600253571)
        ·
          refine ⟨15632636054016824400380357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10421757369344549600253571 15632636054016824400380357)
          ·
            refine ⟨2931119260128154575071317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15632636054016824400380357 2931119260128154575071317)
            ·
              refine ⟨34349053829626811426617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2931119260128154575071317 34349053829626811426617)
              ·
                rfl

theorem cell22_2709229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 8].length) (baseStart_2709229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709229 prefixEnd_2709229 := by exact prefixLift 2709229
  have htrace : WordTrace (prefixWord ++ tailWord_2709229) baseStart_2709229 baseEnd_2709229 := by
    simpa [prefixWord, tailWord_2709229, baseEnd_2709229] using wordTrace_append hprefix tailTrace_2709229
  have hstable : (prefixWord ++ tailWord_2709229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709229).length < 2 ^ (prefixWord ++ tailWord_2709229).sum := by decide
  have hdescent : baseEnd_2709229 < baseStart_2709229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709242 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_2709242 : Nat := 118140960795 + 2709242 * 2 ^ 59
def prefixEnd_2709242 : Nat := 4983230072969 + 3 ^ 40 * 2709242 * 2
def baseEnd_2709242 : Nat := 927428903565596207943619

theorem tailTrace_2709242 : CollatzResearch.WordTrace tailWord_2709242 prefixEnd_2709242 927428903565596207943619 := by
  unfold tailWord_2709242
  simp only [CollatzResearch.WordTrace]
  refine ⟨24703543412721602635286495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65876115767257607027430653 24703543412721602635286495)
  ·
    refine ⟨37055315119082403952929743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24703543412721602635286495 37055315119082403952929743)
    ·
      refine ⟨55582972678623605929394615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37055315119082403952929743 55582972678623605929394615)
      ·
        refine ⟨83374459017935408894091923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55582972678623605929394615 83374459017935408894091923)
        ·
          refine ⟨125061688526903113341137885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83374459017935408894091923 125061688526903113341137885)
          ·
            refine ⟨46898133197588667502926707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125061688526903113341137885 46898133197588667502926707)
            ·
              refine ⟨70347199796383001254390061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46898133197588667502926707 70347199796383001254390061)
              ·
                refine ⟨26380199923643625470396273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70347199796383001254390061 26380199923643625470396273)
                ·
                  refine ⟨19785149942732719102797205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26380199923643625470396273 19785149942732719102797205)
                  ·
                    refine ⟨927428903565596207943619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19785149942732719102797205 927428903565596207943619)
                    ·
                      rfl

theorem cell22_2709242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_2709242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709242 prefixEnd_2709242 := by exact prefixLift 2709242
  have htrace : WordTrace (prefixWord ++ tailWord_2709242) baseStart_2709242 baseEnd_2709242 := by
    simpa [prefixWord, tailWord_2709242, baseEnd_2709242] using wordTrace_append hprefix tailTrace_2709242
  have hstable : (prefixWord ++ tailWord_2709242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709242).length < 2 ^ (prefixWord ++ tailWord_2709242).sum := by decide
  have hdescent : baseEnd_2709242 < baseStart_2709242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709246 : List Nat := [4, 2, 2, 1, 3, 1, 2, 7]
def baseStart_2709246 : Nat := 118140960795 + 2709246 * 2 ^ 59
def prefixEnd_2709246 : Nat := 4983230072969 + 3 ^ 40 * 2709246 * 2
def baseEnd_2709246 : Nat := 103047808094149058982623

theorem tailTrace_2709246 : CollatzResearch.WordTrace tailWord_2709246 prefixEnd_2709246 103047808094149058982623 := by
  unfold tailWord_2709246
  simp only [CollatzResearch.WordTrace]
  refine ⟨12351789942858989903036449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65876213028581279482861061 12351789942858989903036449)
  ·
    refine ⟨9263842457144242427277337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12351789942858989903036449 9263842457144242427277337)
    ·
      refine ⟨6947881842858181820458003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9263842457144242427277337 6947881842858181820458003)
      ·
        refine ⟨10421822764287272730687005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6947881842858181820458003 10421822764287272730687005)
        ·
          refine ⟨3908183536607727274007627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10421822764287272730687005 3908183536607727274007627)
          ·
            refine ⟨5862275304911590911011441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908183536607727274007627 5862275304911590911011441)
            ·
              refine ⟨4396706478683693183258581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5862275304911590911011441 4396706478683693183258581)
              ·
                refine ⟨103047808094149058982623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4396706478683693183258581 103047808094149058982623)
                ·
                  rfl

theorem cell22_2709246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_2709246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709246 prefixEnd_2709246 := by exact prefixLift 2709246
  have htrace : WordTrace (prefixWord ++ tailWord_2709246) baseStart_2709246 baseEnd_2709246 := by
    simpa [prefixWord, tailWord_2709246, baseEnd_2709246] using wordTrace_append hprefix tailTrace_2709246
  have hstable : (prefixWord ++ tailWord_2709246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709246).length < 2 ^ (prefixWord ++ tailWord_2709246).sum := by decide
  have hdescent : baseEnd_2709246 < baseStart_2709246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709304 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 3, 4]
def baseStart_2709304 : Nat := 118140960795 + 2709304 * 2 ^ 59
def prefixEnd_2709304 : Nat := 4983230072969 + 3 ^ 40 * 2709304 * 2
def baseEnd_2709304 : Nat := 927450127432648712893429

theorem tailTrace_2709304 : CollatzResearch.WordTrace tailWord_2709304 prefixEnd_2709304 927450127432648712893429 := by
  unfold tailWord_2709304
  simp only [CollatzResearch.WordTrace]
  refine ⟨49408217488330897564951483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65877623317774530086601977 49408217488330897564951483)
  ·
    refine ⟨74112326232496346347427225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49408217488330897564951483 74112326232496346347427225)
    ·
      refine ⟨55584244674372259760570419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74112326232496346347427225 55584244674372259760570419)
      ·
        refine ⟨83376367011558389640855629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55584244674372259760570419 83376367011558389640855629)
        ·
          refine ⟨31266137629334396115320861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83376367011558389640855629 31266137629334396115320861)
          ·
            refine ⟨11724801611000398543245323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31266137629334396115320861 11724801611000398543245323)
            ·
              refine ⟨17587202416500597814867985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11724801611000398543245323 17587202416500597814867985)
              ·
                refine ⟨13190401812375448361150989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17587202416500597814867985 13190401812375448361150989)
                ·
                  refine ⟨4946400679640793135431621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13190401812375448361150989 4946400679640793135431621)
                  ·
                    refine ⟨927450127432648712893429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4946400679640793135431621 927450127432648712893429)
                    ·
                      rfl

theorem cell22_2709304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_2709304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709304 prefixEnd_2709304 := by exact prefixLift 2709304
  have htrace : WordTrace (prefixWord ++ tailWord_2709304) baseStart_2709304 baseEnd_2709304 := by
    simpa [prefixWord, tailWord_2709304, baseEnd_2709304] using wordTrace_append hprefix tailTrace_2709304
  have hstable : (prefixWord ++ tailWord_2709304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709304).length < 2 ^ (prefixWord ++ tailWord_2709304).sum := by decide
  have hdescent : baseEnd_2709304 < baseStart_2709304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709349 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_2709349 : Nat := 118140960795 + 2709349 * 2 ^ 59
def prefixEnd_2709349 : Nat := 4983230072969 + 3 ^ 40 * 2709349 * 2
def baseEnd_2709349 : Nat := 927465531852283595518291

theorem tailTrace_2709349 : CollatzResearch.WordTrace tailWord_2709349 prefixEnd_2709349 927465531852283595518291 := by
  unfold tailWord_2709349
  simp only [CollatzResearch.WordTrace]
  refine ⟨98818076261498767815291101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65878717507665845210194067 98818076261498767815291101)
  ·
    refine ⟨37056778598062037930734163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98818076261498767815291101 37056778598062037930734163)
    ·
      refine ⟨55585167897093056896101245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37056778598062037930734163 55585167897093056896101245)
      ·
        refine ⟨20844437961409896336037967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55585167897093056896101245 20844437961409896336037967)
        ·
          refine ⟨31266656942114844504056951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20844437961409896336037967 31266656942114844504056951)
          ·
            refine ⟨46899985413172266756085427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31266656942114844504056951 46899985413172266756085427)
            ·
              refine ⟨70349978119758400134128141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46899985413172266756085427 70349978119758400134128141)
              ·
                refine ⟨26381241794909400050298053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70349978119758400134128141 26381241794909400050298053)
                ·
                  refine ⟨4946482836545512509430885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26381241794909400050298053 4946482836545512509430885)
                  ·
                    refine ⟨927465531852283595518291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4946482836545512509430885 927465531852283595518291)
                    ·
                      rfl

theorem cell22_2709349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_2709349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709349 prefixEnd_2709349 := by exact prefixLift 2709349
  have htrace : WordTrace (prefixWord ++ tailWord_2709349) baseStart_2709349 baseEnd_2709349 := by
    simpa [prefixWord, tailWord_2709349, baseEnd_2709349] using wordTrace_append hprefix tailTrace_2709349
  have hstable : (prefixWord ++ tailWord_2709349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709349).length < 2 ^ (prefixWord ++ tailWord_2709349).sum := by decide
  have hdescent : baseEnd_2709349 < baseStart_2709349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709351 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 4, 3]
def baseStart_2709351 : Nat := 118140960795 + 2709351 * 2 ^ 59
def prefixEnd_2709351 : Nat := 4983230072969 + 3 ^ 40 * 2709351 * 2
def baseEnd_2709351 : Nat := 927466216493156256968285

theorem tailTrace_2709351 : CollatzResearch.WordTrace tailWord_2709351 prefixEnd_2709351 927466216493156256968285 := by
  unfold tailWord_2709351
  simp only [CollatzResearch.WordTrace]
  refine ⟨98818149207491522156863907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65878766138327681437909271 98818149207491522156863907)
  ·
    refine ⟨148227223811237283235295861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98818149207491522156863907 148227223811237283235295861)
    ·
      refine ⟨13896302232303495303308987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148227223811237283235295861 13896302232303495303308987)
      ·
        refine ⟨20844453348455242954963481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13896302232303495303308987 20844453348455242954963481)
        ·
          refine ⟨15633340011341432216222611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20844453348455242954963481 15633340011341432216222611)
          ·
            refine ⟨23450010017012148324333917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15633340011341432216222611 23450010017012148324333917)
            ·
              refine ⟨8793753756379555621625219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23450010017012148324333917 8793753756379555621625219)
              ·
                refine ⟨13190630634569333432437829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8793753756379555621625219 13190630634569333432437829)
                ·
                  refine ⟨2473243243981750018582093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13190630634569333432437829 2473243243981750018582093)
                  ·
                    refine ⟨927466216493156256968285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2473243243981750018582093 927466216493156256968285)
                    ·
                      rfl

theorem cell22_2709351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_2709351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709351 prefixEnd_2709351 := by exact prefixLift 2709351
  have htrace : WordTrace (prefixWord ++ tailWord_2709351) baseStart_2709351 baseEnd_2709351 := by
    simpa [prefixWord, tailWord_2709351, baseEnd_2709351] using wordTrace_append hprefix tailTrace_2709351
  have hstable : (prefixWord ++ tailWord_2709351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709351).length < 2 ^ (prefixWord ++ tailWord_2709351).sum := by decide
  have hdescent : baseEnd_2709351 < baseStart_2709351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709413 : List Nat := [1, 3, 1, 2, 1, 1, 1, 8, 1, 3]
def baseStart_2709413 : Nat := 118140960795 + 2709413 * 2 ^ 59
def prefixEnd_2709413 : Nat := 4983230072969 + 3 ^ 40 * 2709413 * 2
def baseEnd_2709413 : Nat := 927487440360208761918095

theorem tailTrace_2709413 : CollatzResearch.WordTrace tailWord_2709413 prefixEnd_2709413 927487440360208761918095 := by
  unfold tailWord_2709413
  simp only [CollatzResearch.WordTrace]
  refine ⟨98820410533266906745620893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65880273688844604497080595 98820410533266906745620893)
  ·
    refine ⟨37057653949975090029607835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98820410533266906745620893 37057653949975090029607835)
    ·
      refine ⟨55586480924962635044411753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37057653949975090029607835 55586480924962635044411753)
      ·
        refine ⟨41689860693721976283308815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55586480924962635044411753 41689860693721976283308815)
        ·
          refine ⟨62534791040582964424963223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41689860693721976283308815 62534791040582964424963223)
          ·
            refine ⟨93802186560874446637444835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62534791040582964424963223 93802186560874446637444835)
            ·
              refine ⟨140703279841311669956167253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93802186560874446637444835 140703279841311669956167253)
              ·
                refine ⟨1648866560640371132298835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 140703279841311669956167253 1648866560640371132298835)
                ·
                  refine ⟨2473299840960556698448253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648866560640371132298835 2473299840960556698448253)
                  ·
                    refine ⟨927487440360208761918095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2473299840960556698448253 927487440360208761918095)
                    ·
                      rfl

theorem cell22_2709413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_2709413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709413 prefixEnd_2709413 := by exact prefixLift 2709413
  have htrace : WordTrace (prefixWord ++ tailWord_2709413) baseStart_2709413 baseEnd_2709413 := by
    simpa [prefixWord, tailWord_2709413, baseEnd_2709413] using wordTrace_append hprefix tailTrace_2709413
  have hstable : (prefixWord ++ tailWord_2709413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709413).length < 2 ^ (prefixWord ++ tailWord_2709413).sum := by decide
  have hdescent : baseEnd_2709413 < baseStart_2709413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709456 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 1, 4]
def baseStart_2709456 : Nat := 118140960795 + 2709456 * 2 ^ 59
def prefixEnd_2709456 : Nat := 4983230072969 + 3 ^ 40 * 2709456 * 2
def baseEnd_2709456 : Nat := 927502160138970983092963

theorem tailTrace_2709456 : CollatzResearch.WordTrace tailWord_2709456 prefixEnd_2709456 927502160138970983092963 := by
  unfold tailWord_2709456
  simp only [CollatzResearch.WordTrace]
  refine ⟨49410989436055562544718111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65881319248074083392957481 49410989436055562544718111)
  ·
    refine ⟨74116484154083343817077167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49410989436055562544718111 74116484154083343817077167)
    ·
      refine ⟨111174726231125015725615751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74116484154083343817077167 111174726231125015725615751)
      ·
        refine ⟨166762089346687523588423627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111174726231125015725615751 166762089346687523588423627)
        ·
          refine ⟨250143134020031285382635441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166762089346687523588423627 250143134020031285382635441)
          ·
            refine ⟨187607350515023464036976581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250143134020031285382635441 187607350515023464036976581)
            ·
              refine ⟨35176378221566899506933109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187607350515023464036976581 35176378221566899506933109)
              ·
                refine ⟨3297785458271896828774979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35176378221566899506933109 3297785458271896828774979)
                ·
                  refine ⟨4946678187407845243162469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297785458271896828774979 4946678187407845243162469)
                  ·
                    refine ⟨927502160138970983092963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4946678187407845243162469 927502160138970983092963)
                    ·
                      rfl

theorem cell22_2709456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_2709456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709456 prefixEnd_2709456 := by exact prefixLift 2709456
  have htrace : WordTrace (prefixWord ++ tailWord_2709456) baseStart_2709456 baseEnd_2709456 := by
    simpa [prefixWord, tailWord_2709456, baseEnd_2709456] using wordTrace_append hprefix tailTrace_2709456
  have hstable : (prefixWord ++ tailWord_2709456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709456).length < 2 ^ (prefixWord ++ tailWord_2709456).sum := by decide
  have hdescent : baseEnd_2709456 < baseStart_2709456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709499 : List Nat := [1, 1, 1, 1, 1, 3, 4, 10]
def baseStart_2709499 : Nat := 118140960795 + 2709499 * 2 ^ 59
def prefixEnd_2709499 : Nat := 4983230072969 + 3 ^ 40 * 2709499 * 2
def baseEnd_2709499 : Nat := 103057431101970356029759

theorem tailTrace_2709499 : CollatzResearch.WordTrace tailWord_2709499 prefixEnd_2709499 103057431101970356029759 := by
  unfold tailWord_2709499
  simp only [CollatzResearch.WordTrace]
  refine ⟨98823547210955343433251551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65882364807303562288834367 98823547210955343433251551)
  ·
    refine ⟨148235320816433015149877327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98823547210955343433251551 148235320816433015149877327)
    ·
      refine ⟨222352981224649522724815991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148235320816433015149877327 222352981224649522724815991)
      ·
        refine ⟨333529471836974284087223987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222352981224649522724815991 333529471836974284087223987)
        ·
          refine ⟨500294207755461426130835981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333529471836974284087223987 500294207755461426130835981)
          ·
            refine ⟨187610327908298034799063493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 500294207755461426130835981 187610327908298034799063493)
            ·
              refine ⟨35176936482805881524824405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187610327908298034799063493 35176936482805881524824405)
              ·
                refine ⟨103057431101970356029759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35176936482805881524824405 103057431101970356029759)
                ·
                  rfl

theorem cell22_2709499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 10].length) (baseStart_2709499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709499 prefixEnd_2709499 := by exact prefixLift 2709499
  have htrace : WordTrace (prefixWord ++ tailWord_2709499) baseStart_2709499 baseEnd_2709499 := by
    simpa [prefixWord, tailWord_2709499, baseEnd_2709499] using wordTrace_append hprefix tailTrace_2709499
  have hstable : (prefixWord ++ tailWord_2709499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709499).length < 2 ^ (prefixWord ++ tailWord_2709499).sum := by decide
  have hdescent : baseEnd_2709499 < baseStart_2709499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709537 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 2, 3]
def baseStart_2709537 : Nat := 118140960795 + 2709537 * 2 ^ 59
def prefixEnd_2709537 : Nat := 4983230072969 + 3 ^ 40 * 2709537 * 2
def baseEnd_2709537 : Nat := 927529888094313771817715

theorem tailTrace_2709537 : CollatzResearch.WordTrace tailWord_2709537 prefixEnd_2709537 927529888094313771817715 := by
  unfold tailWord_2709537
  simp only [CollatzResearch.WordTrace]
  refine ⟨98824933184817675923134865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65883288789878450615423243 98824933184817675923134865)
  ·
    refine ⟨74118699888613256942351149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98824933184817675923134865 74118699888613256942351149)
    ·
      refine ⟨27794512458229971353381681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74118699888613256942351149 27794512458229971353381681)
      ·
        refine ⟨20845884343672478515036261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27794512458229971353381681 20845884343672478515036261)
        ·
          refine ⟨3908603314438589721569299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20845884343672478515036261 3908603314438589721569299)
          ·
            refine ⟨5862904971657884582353949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908603314438589721569299 5862904971657884582353949)
            ·
              refine ⟨2198589364371706718382731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5862904971657884582353949 2198589364371706718382731)
              ·
                refine ⟨3297884046557560077574097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198589364371706718382731 3297884046557560077574097)
                ·
                  refine ⟨2473413034918170058180573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3297884046557560077574097 2473413034918170058180573)
                  ·
                    refine ⟨927529888094313771817715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2473413034918170058180573 927529888094313771817715)
                    ·
                      rfl

theorem cell22_2709537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_2709537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709537 prefixEnd_2709537 := by exact prefixLift 2709537
  have htrace : WordTrace (prefixWord ++ tailWord_2709537) baseStart_2709537 baseEnd_2709537 := by
    simpa [prefixWord, tailWord_2709537, baseEnd_2709537] using wordTrace_append hprefix tailTrace_2709537
  have hstable : (prefixWord ++ tailWord_2709537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709537).length < 2 ^ (prefixWord ++ tailWord_2709537).sum := by decide
  have hdescent : baseEnd_2709537 < baseStart_2709537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709550 : List Nat := [4, 1, 3, 1, 1, 4, 2, 6]
def baseStart_2709550 : Nat := 118140960795 + 2709550 * 2 ^ 59
def prefixEnd_2709550 : Nat := 4983230072969 + 3 ^ 40 * 2709550 * 2
def baseEnd_2709550 : Nat := 103059370917776230138075

theorem tailTrace_2709550 : CollatzResearch.WordTrace tailWord_2709550 prefixEnd_2709550 103059370917776230138075 := by
  unfold tailWord_2709550
  simp only [CollatzResearch.WordTrace]
  refine ⟨12353175916721322392919763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65883604889180386095572069 12353175916721322392919763)
  ·
    refine ⟨18529763875081983589379645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12353175916721322392919763 18529763875081983589379645)
    ·
      refine ⟨6948661453155743846017367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18529763875081983589379645 6948661453155743846017367)
      ·
        refine ⟨10422992179733615769026051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6948661453155743846017367 10422992179733615769026051)
        ·
          refine ⟨15634488269600423653539077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10422992179733615769026051 15634488269600423653539077)
          ·
            refine ⟨2931466550550079435038577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15634488269600423653539077 2931466550550079435038577)
            ·
              refine ⟨2198599912912559576278933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2931466550550079435038577 2198599912912559576278933)
              ·
                refine ⟨103059370917776230138075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2198599912912559576278933 103059370917776230138075)
                ·
                  rfl

theorem cell22_2709550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_2709550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709550 prefixEnd_2709550 := by exact prefixLift 2709550
  have htrace : WordTrace (prefixWord ++ tailWord_2709550) baseStart_2709550 baseEnd_2709550 := by
    simpa [prefixWord, tailWord_2709550, baseEnd_2709550] using wordTrace_append hprefix tailTrace_2709550
  have hstable : (prefixWord ++ tailWord_2709550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709550).length < 2 ^ (prefixWord ++ tailWord_2709550).sum := by decide
  have hdescent : baseEnd_2709550 < baseStart_2709550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709576 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 2, 5]
def baseStart_2709576 : Nat := 118140960795 + 2709576 * 2 ^ 59
def prefixEnd_2709576 : Nat := 4983230072969 + 3 ^ 40 * 2709576 * 2
def baseEnd_2709576 : Nat := 927543238591330670092595

theorem tailTrace_2709576 : CollatzResearch.WordTrace tailWord_2709576 prefixEnd_2709576 927543238591330670092595 := by
  unfold tailWord_2709576
  simp only [CollatzResearch.WordTrace]
  refine ⟨49413177815838192791902291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65884237087784257055869721 49413177815838192791902291)
  ·
    refine ⟨74119766723757289187853437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49413177815838192791902291 74119766723757289187853437)
    ·
      refine ⟨27794912521408983445445039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74119766723757289187853437 27794912521408983445445039)
      ·
        refine ⟨41692368782113475168167559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27794912521408983445445039 41692368782113475168167559)
        ·
          refine ⟨62538553173170212752251339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41692368782113475168167559 62538553173170212752251339)
          ·
            refine ⟨93807829759755319128377009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62538553173170212752251339 93807829759755319128377009)
            ·
              refine ⟨70355872319816489346282757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93807829759755319128377009 70355872319816489346282757)
              ·
                refine ⟨13191726059965591752428017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70355872319816489346282757 13191726059965591752428017)
                ·
                  refine ⟨9893794544974193814321013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13191726059965591752428017 9893794544974193814321013)
                  ·
                    refine ⟨927543238591330670092595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9893794544974193814321013 927543238591330670092595)
                    ·
                      rfl

theorem cell22_2709576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_2709576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709576 prefixEnd_2709576 := by exact prefixLift 2709576
  have htrace : WordTrace (prefixWord ++ tailWord_2709576) baseStart_2709576 baseEnd_2709576 := by
    simpa [prefixWord, tailWord_2709576, baseEnd_2709576] using wordTrace_append hprefix tailTrace_2709576
  have hstable : (prefixWord ++ tailWord_2709576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709576).length < 2 ^ (prefixWord ++ tailWord_2709576).sum := by decide
  have hdescent : baseEnd_2709576 < baseStart_2709576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709655 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 1, 5]
def baseStart_2709655 : Nat := 118140960795 + 2709655 * 2 ^ 59
def prefixEnd_2709655 : Nat := 4983230072969 + 3 ^ 40 * 2709655 * 2
def baseEnd_2709655 : Nat := 927570281905800797367353

theorem tailTrace_2709655 : CollatzResearch.WordTrace tailWord_2709655 prefixEnd_2709655 927570281905800797367353 := by
  unfold tailWord_2709655
  simp only [CollatzResearch.WordTrace]
  refine ⟨98829236998390182075930419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65886157998926788050620279 98829236998390182075930419)
  ·
    refine ⟨148243855497585273113895629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98829236998390182075930419 148243855497585273113895629)
    ·
      refine ⟨55591445811594477417710861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148243855497585273113895629 55591445811594477417710861)
      ·
        refine ⟨20846792179347929031641573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55591445811594477417710861 20846792179347929031641573)
        ·
          refine ⟨3908773533627736693432795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20846792179347929031641573 3908773533627736693432795)
          ·
            refine ⟨5863160300441605040149193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908773533627736693432795 5863160300441605040149193)
            ·
              refine ⟨4397370225331203780111895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5863160300441605040149193 4397370225331203780111895)
              ·
                refine ⟨6596055337996805670167843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4397370225331203780111895 6596055337996805670167843)
                ·
                  refine ⟨9894083006995208505251765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6596055337996805670167843 9894083006995208505251765)
                  ·
                    refine ⟨927570281905800797367353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9894083006995208505251765 927570281905800797367353)
                    ·
                      rfl

theorem cell22_2709655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_2709655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709655 prefixEnd_2709655 := by exact prefixLift 2709655
  have htrace : WordTrace (prefixWord ++ tailWord_2709655) baseStart_2709655 baseEnd_2709655 := by
    simpa [prefixWord, tailWord_2709655, baseEnd_2709655] using wordTrace_append hprefix tailTrace_2709655
  have hstable : (prefixWord ++ tailWord_2709655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709655).length < 2 ^ (prefixWord ++ tailWord_2709655).sum := by decide
  have hdescent : baseEnd_2709655 < baseStart_2709655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709674 : List Nat := [3, 1, 5, 1, 2, 1, 2, 3, 4]
def baseStart_2709674 : Nat := 118140960795 + 2709674 * 2 ^ 59
def prefixEnd_2709674 : Nat := 4983230072969 + 3 ^ 40 * 2709674 * 2
def baseEnd_2709674 : Nat := 309192261998030360380765

theorem tailTrace_2709674 : CollatzResearch.WordTrace tailWord_2709674 prefixEnd_2709674 309192261998030360380765 := by
  unfold tailWord_2709674
  simp only [CollatzResearch.WordTrace]
  refine ⟨24707482496330337080218019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65886619990214232213914717 24707482496330337080218019)
  ·
    refine ⟨37061223744495505620327029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24707482496330337080218019 37061223744495505620327029)
    ·
      refine ⟨3474489726046453651905659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37061223744495505620327029 3474489726046453651905659)
      ·
        refine ⟨5211734589069680477858489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3474489726046453651905659 5211734589069680477858489)
        ·
          refine ⟨3908800941802260358393867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5211734589069680477858489 3908800941802260358393867)
          ·
            refine ⟨5863201412703390537590801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908800941802260358393867 5863201412703390537590801)
            ·
              refine ⟨4397401059527542903193101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5863201412703390537590801 4397401059527542903193101)
              ·
                refine ⟨1649025397322828588697413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4397401059527542903193101 1649025397322828588697413)
                ·
                  refine ⟨309192261998030360380765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1649025397322828588697413 309192261998030360380765)
                  ·
                    rfl

theorem cell22_2709674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_2709674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709674 prefixEnd_2709674 := by exact prefixLift 2709674
  have htrace : WordTrace (prefixWord ++ tailWord_2709674) baseStart_2709674 baseEnd_2709674 := by
    simpa [prefixWord, tailWord_2709674, baseEnd_2709674] using wordTrace_append hprefix tailTrace_2709674
  have hstable : (prefixWord ++ tailWord_2709674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709674).length < 2 ^ (prefixWord ++ tailWord_2709674).sum := by decide
  have hdescent : baseEnd_2709674 < baseStart_2709674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709683 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 7, 3]
def baseStart_2709683 : Nat := 118140960795 + 2709683 * 2 ^ 59
def prefixEnd_2709683 : Nat := 4983230072969 + 3 ^ 40 * 2709683 * 2
def baseEnd_2709683 : Nat := 927579866878018057667267

theorem tailTrace_2709683 : CollatzResearch.WordTrace tailWord_2709683 prefixEnd_2709683 927579866878018057667267 := by
  unfold tailWord_2709683
  simp only [CollatzResearch.WordTrace]
  refine ⟨98830258242288742857949703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65886838828192495238633135 98830258242288742857949703)
  ·
    refine ⟨148245387363433114286924555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98830258242288742857949703 148245387363433114286924555)
    ·
      refine ⟨222368081045149671430386833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148245387363433114286924555 222368081045149671430386833)
      ·
        refine ⟨166776060783862253572790125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222368081045149671430386833 166776060783862253572790125)
        ·
          refine ⟨62541022793948345089796297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166776060783862253572790125 62541022793948345089796297)
          ·
            refine ⟨46905767095461258817347223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62541022793948345089796297 46905767095461258817347223)
            ·
              refine ⟨70358650643191888226020835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46905767095461258817347223 70358650643191888226020835)
              ·
                refine ⟨105537975964787832339031253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70358650643191888226020835 105537975964787832339031253)
                ·
                  refine ⟨2473546311674714820446045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 105537975964787832339031253 2473546311674714820446045)
                  ·
                    refine ⟨927579866878018057667267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2473546311674714820446045 927579866878018057667267)
                    ·
                      rfl

theorem cell22_2709683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 3].length) (baseStart_2709683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709683 prefixEnd_2709683 := by exact prefixLift 2709683
  have htrace : WordTrace (prefixWord ++ tailWord_2709683) baseStart_2709683 baseEnd_2709683 := by
    simpa [prefixWord, tailWord_2709683, baseEnd_2709683] using wordTrace_append hprefix tailTrace_2709683
  have hstable : (prefixWord ++ tailWord_2709683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709683).length < 2 ^ (prefixWord ++ tailWord_2709683).sum := by decide
  have hdescent : baseEnd_2709683 < baseStart_2709683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709685 : List Nat := [1, 3, 3, 4, 1, 1, 9]
def baseStart_2709685 : Nat := 118140960795 + 2709685 * 2 ^ 59
def prefixEnd_2709685 : Nat := 4983230072969 + 3 ^ 40 * 2709685 * 2
def baseEnd_2709685 : Nat := 34354835241440397004343

theorem tailTrace_2709685 : CollatzResearch.WordTrace tailWord_2709685 prefixEnd_2709685 34354835241440397004343 := by
  unfold tailWord_2709685
  simp only [CollatzResearch.WordTrace]
  refine ⟨98830331188281497199522509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65886887458854331466348339 98830331188281497199522509)
  ·
    refine ⟨37061374195605561449820941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98830331188281497199522509 37061374195605561449820941)
    ·
      refine ⟨13898015323352085543682853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37061374195605561449820941 13898015323352085543682853)
      ·
        refine ⟨2605877873128516039440535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13898015323352085543682853 2605877873128516039440535)
        ·
          refine ⟨3908816809692774059160803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2605877873128516039440535 3908816809692774059160803)
          ·
            refine ⟨5863225214539161088741205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908816809692774059160803 5863225214539161088741205)
            ·
              refine ⟨34354835241440397004343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5863225214539161088741205 34354835241440397004343)
              ·
                rfl

theorem cell22_2709685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 9].length) (baseStart_2709685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709685 prefixEnd_2709685 := by exact prefixLift 2709685
  have htrace : WordTrace (prefixWord ++ tailWord_2709685) baseStart_2709685 baseEnd_2709685 := by
    simpa [prefixWord, tailWord_2709685, baseEnd_2709685] using wordTrace_append hprefix tailTrace_2709685
  have hstable : (prefixWord ++ tailWord_2709685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709685).length < 2 ^ (prefixWord ++ tailWord_2709685).sum := by decide
  have hdescent : baseEnd_2709685 < baseStart_2709685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709713 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 5]
def baseStart_2709713 : Nat := 118140960795 + 2709713 * 2 ^ 59
def prefixEnd_2709713 : Nat := 4983230072969 + 3 ^ 40 * 2709713 * 2
def baseEnd_2709713 : Nat := 309196712163702659805725

theorem tailTrace_2709713 : CollatzResearch.WordTrace tailWord_2709713 prefixEnd_2709713 309196712163702659805725 := by
  unfold tailWord_2709713
  simp only [CollatzResearch.WordTrace]
  refine ⟨98831352432180057981541793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65887568288120038654361195 98831352432180057981541793)
  ·
    refine ⟨74123514324135043486156345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98831352432180057981541793 74123514324135043486156345)
    ·
      refine ⟨55592635743101282614617259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74123514324135043486156345 55592635743101282614617259)
      ·
        refine ⟨83388953614651923921925889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55592635743101282614617259 83388953614651923921925889)
        ·
          refine ⟨62541715210988942941444417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83388953614651923921925889 62541715210988942941444417)
          ·
            refine ⟨46906286408241707206083313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62541715210988942941444417 46906286408241707206083313)
            ·
              refine ⟨35179714806181280404562485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46906286408241707206083313 35179714806181280404562485)
              ·
                refine ⟨3298098263079495037927733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35179714806181280404562485 3298098263079495037927733)
                ·
                  refine ⟨309196712163702659805725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3298098263079495037927733 309196712163702659805725)
                  ·
                    rfl

theorem cell22_2709713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_2709713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709713 prefixEnd_2709713 := by exact prefixLift 2709713
  have htrace : WordTrace (prefixWord ++ tailWord_2709713) baseStart_2709713 baseEnd_2709713 := by
    simpa [prefixWord, tailWord_2709713, baseEnd_2709713] using wordTrace_append hprefix tailTrace_2709713
  have hstable : (prefixWord ++ tailWord_2709713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709713).length < 2 ^ (prefixWord ++ tailWord_2709713).sum := by decide
  have hdescent : baseEnd_2709713 < baseStart_2709713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709764 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 5]
def baseStart_2709764 : Nat := 118140960795 + 2709764 * 2 ^ 59
def prefixEnd_2709764 : Nat := 4983230072969 + 3 ^ 40 * 2709764 * 2
def baseEnd_2709764 : Nat := 309202531611120282130673

theorem tailTrace_2709764 : CollatzResearch.WordTrace tailWord_2709764 prefixEnd_2709764 309202531611120282130673 := by
  unfold tailWord_2709764
  simp only [CollatzResearch.WordTrace]
  refine ⟨49416606277497646845824173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65888808369996862461098897 49416606277497646845824173)
  ·
    refine ⟨18531227354061617567184065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49416606277497646845824173 18531227354061617567184065)
    ·
      refine ⟨13898420515546213175388049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18531227354061617567184065 13898420515546213175388049)
      ·
        refine ⟨10423815386659659881541037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13898420515546213175388049 10423815386659659881541037)
        ·
          refine ⟨3908930769997372455577889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10423815386659659881541037 3908930769997372455577889)
          ·
            refine ⟨2931698077498029341683417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3908930769997372455577889 2931698077498029341683417)
            ·
              refine ⟨2198773558123522006262563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2931698077498029341683417 2198773558123522006262563)
              ·
                refine ⟨3298160337185283009393845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198773558123522006262563 3298160337185283009393845)
                ·
                  refine ⟨309202531611120282130673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3298160337185283009393845 309202531611120282130673)
                  ·
                    rfl

theorem cell22_2709764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_2709764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709764 prefixEnd_2709764 := by exact prefixLift 2709764
  have htrace : WordTrace (prefixWord ++ tailWord_2709764) baseStart_2709764 baseEnd_2709764 := by
    simpa [prefixWord, tailWord_2709764, baseEnd_2709764] using wordTrace_append hprefix tailTrace_2709764
  have hstable : (prefixWord ++ tailWord_2709764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709764).length < 2 ^ (prefixWord ++ tailWord_2709764).sum := by decide
  have hdescent : baseEnd_2709764 < baseStart_2709764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709777 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 1, 4]
def baseStart_2709777 : Nat := 118140960795 + 2709777 * 2 ^ 59
def prefixEnd_2709777 : Nat := 4983230072969 + 3 ^ 40 * 2709777 * 2
def baseEnd_2709777 : Nat := 927612044999033145816979

theorem tailTrace_2709777 : CollatzResearch.WordTrace tailWord_2709777 prefixEnd_2709777 927612044999033145816979 := by
  unfold tailWord_2709777
  simp only [CollatzResearch.WordTrace]
  refine ⟨98833686703948196911871585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65889124469298797941247723 98833686703948196911871585)
  ·
    refine ⟨74125265027961147683903689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98833686703948196911871585 74125265027961147683903689)
    ·
      refine ⟨55593948770970860762927767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74125265027961147683903689 55593948770970860762927767)
      ·
        refine ⟨83390923156456291144391651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55593948770970860762927767 83390923156456291144391651)
        ·
          refine ⟨125086384734684436716587477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83390923156456291144391651 125086384734684436716587477)
          ·
            refine ⟨2931712142219166485545019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 125086384734684436716587477 2931712142219166485545019)
            ·
              refine ⟨4397568213328749728317529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931712142219166485545019 4397568213328749728317529)
              ·
                refine ⟨3298176159996562296238147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4397568213328749728317529 3298176159996562296238147)
                ·
                  refine ⟨4947264239994843444357221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3298176159996562296238147 4947264239994843444357221)
                  ·
                    refine ⟨927612044999033145816979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4947264239994843444357221 927612044999033145816979)
                    ·
                      rfl

theorem cell22_2709777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_2709777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709777 prefixEnd_2709777 := by exact prefixLift 2709777
  have htrace : WordTrace (prefixWord ++ tailWord_2709777) baseStart_2709777 baseEnd_2709777 := by
    simpa [prefixWord, tailWord_2709777, baseEnd_2709777] using wordTrace_append hprefix tailTrace_2709777
  have hstable : (prefixWord ++ tailWord_2709777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709777).length < 2 ^ (prefixWord ++ tailWord_2709777).sum := by decide
  have hdescent : baseEnd_2709777 < baseStart_2709777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709794 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_2709794 : Nat := 118140960795 + 2709794 * 2 ^ 59
def prefixEnd_2709794 : Nat := 4983230072969 + 3 ^ 40 * 2709794 * 2
def baseEnd_2709794 : Nat := 927617864446450768141927

theorem tailTrace_2709794 : CollatzResearch.WordTrace tailWord_2709794 prefixEnd_2709794 927617864446450768141927 := by
  unfold tailWord_2709794
  simp only [CollatzResearch.WordTrace]
  refine ⟨24708576686221652203810109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65889537829924405876826957 24708576686221652203810109)
  ·
    refine ⟨9265716257333119576428791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24708576686221652203810109 9265716257333119576428791)
    ·
      refine ⟨13898574385999679364643187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9265716257333119576428791 13898574385999679364643187)
      ·
        refine ⟨20847861578999519046964781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13898574385999679364643187 20847861578999519046964781)
        ·
          refine ⟨7817948092124819642611793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20847861578999519046964781 7817948092124819642611793)
          ·
            refine ⟨5863461069093614731958845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7817948092124819642611793 5863461069093614731958845)
            ·
              refine ⟨2198797900910105524484567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5863461069093614731958845 2198797900910105524484567)
              ·
                refine ⟨3298196851365158286726851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198797900910105524484567 3298196851365158286726851)
                ·
                  refine ⟨4947295277047737430090277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3298196851365158286726851 4947295277047737430090277)
                  ·
                    refine ⟨927617864446450768141927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4947295277047737430090277 927617864446450768141927)
                    ·
                      rfl

theorem cell22_2709794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_2709794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709794 prefixEnd_2709794 := by exact prefixLift 2709794
  have htrace : WordTrace (prefixWord ++ tailWord_2709794) baseStart_2709794 baseEnd_2709794 := by
    simpa [prefixWord, tailWord_2709794, baseEnd_2709794] using wordTrace_append hprefix tailTrace_2709794
  have hstable : (prefixWord ++ tailWord_2709794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709794).length < 2 ^ (prefixWord ++ tailWord_2709794).sum := by decide
  have hdescent : baseEnd_2709794 < baseStart_2709794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709833 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_2709833 : Nat := 118140960795 + 2709833 * 2 ^ 59
def prefixEnd_2709833 : Nat := 4983230072969 + 3 ^ 40 * 2709833 * 2
def baseEnd_2709833 : Nat := 927631214943467666416807

theorem tailTrace_2709833 : CollatzResearch.WordTrace tailWord_2709833 prefixEnd_2709833 927631214943467666416807 := by
  unfold tailWord_2709833
  simp only [CollatzResearch.WordTrace]
  refine ⟨98835729191745318475910153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65890486127830212317273435 98835729191745318475910153)
  ·
    refine ⟨74126796893808988856932615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98835729191745318475910153 74126796893808988856932615)
    ·
      refine ⟨111190195340713483285398923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74126796893808988856932615 111190195340713483285398923)
      ·
        refine ⟨166785293011070224928098385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111190195340713483285398923 166785293011070224928098385)
        ·
          refine ⟨125088969758302668696073789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166785293011070224928098385 125088969758302668696073789)
          ·
            refine ⟨46908363659363500761027671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125088969758302668696073789 46908363659363500761027671)
            ·
              refine ⟨70362545489045251141541507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46908363659363500761027671 70362545489045251141541507)
              ·
                refine ⟨105543818233567876712312261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70362545489045251141541507 105543818233567876712312261)
                ·
                  refine ⟨19789465918793976883558549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105543818233567876712312261 19789465918793976883558549)
                  ·
                    refine ⟨927631214943467666416807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19789465918793976883558549 927631214943467666416807)
                    ·
                      rfl

theorem cell22_2709833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_2709833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709833 prefixEnd_2709833 := by exact prefixLift 2709833
  have htrace : WordTrace (prefixWord ++ tailWord_2709833) baseStart_2709833 baseEnd_2709833 := by
    simpa [prefixWord, tailWord_2709833, baseEnd_2709833] using wordTrace_append hprefix tailTrace_2709833
  have hstable : (prefixWord ++ tailWord_2709833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709833).length < 2 ^ (prefixWord ++ tailWord_2709833).sum := by decide
  have hdescent : baseEnd_2709833 < baseStart_2709833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709869 : List Nat := [1, 5, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_2709869 : Nat := 118140960795 + 2709869 * 2 ^ 59
def prefixEnd_2709869 : Nat := 4983230072969 + 3 ^ 40 * 2709869 * 2
def baseEnd_2709869 : Nat := 927643538479175572516697

theorem tailTrace_2709869 : CollatzResearch.WordTrace tailWord_2709869 prefixEnd_2709869 927643538479175572516697 := by
  unfold tailWord_2709869
  simp only [CollatzResearch.WordTrace]
  refine ⟨98837042219614896624220661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65891361479743264416147107 98837042219614896624220661)
  ·
    refine ⟨9265972708088896558520687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98837042219614896624220661 9265972708088896558520687)
    ·
      refine ⟨13898959062133344837781031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9265972708088896558520687 13898959062133344837781031)
      ·
        refine ⟨20848438593200017256671547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13898959062133344837781031 20848438593200017256671547)
        ·
          refine ⟨31272657889800025885007321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20848438593200017256671547 31272657889800025885007321)
          ·
            refine ⟨23454493417350019413755491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31272657889800025885007321 23454493417350019413755491)
            ·
              refine ⟨35181740126025029120633237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23454493417350019413755491 35181740126025029120633237)
              ·
                refine ⟨1649144068407423240029683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35181740126025029120633237 1649144068407423240029683)
                ·
                  refine ⟨2473716102611134860044525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649144068407423240029683 2473716102611134860044525)
                  ·
                    refine ⟨927643538479175572516697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2473716102611134860044525 927643538479175572516697)
                    ·
                      rfl

theorem cell22_2709869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_2709869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709869 prefixEnd_2709869 := by exact prefixLift 2709869
  have htrace : WordTrace (prefixWord ++ tailWord_2709869) baseStart_2709869 baseEnd_2709869 := by
    simpa [prefixWord, tailWord_2709869, baseEnd_2709869] using wordTrace_append hprefix tailTrace_2709869
  have hstable : (prefixWord ++ tailWord_2709869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709869).length < 2 ^ (prefixWord ++ tailWord_2709869).sum := by decide
  have hdescent : baseEnd_2709869 < baseStart_2709869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709927 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 6]
def baseStart_2709927 : Nat := 118140960795 + 2709927 * 2 ^ 59
def prefixEnd_2709927 : Nat := 4983230072969 + 3 ^ 40 * 2709927 * 2
def baseEnd_2709927 : Nat := 309221131021494251522173

theorem tailTrace_2709927 : CollatzResearch.WordTrace tailWord_2709927 prefixEnd_2709927 309221131021494251522173 := by
  unfold tailWord_2709927
  simp only [CollatzResearch.WordTrace]
  refine ⟨98839157653404772529832035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65892771768936515019888023 98839157653404772529832035)
  ·
    refine ⟨148258736480107158794748053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98839157653404772529832035 148258736480107158794748053)
    ·
      refine ⟨6949628272505023068503815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 148258736480107158794748053 6949628272505023068503815)
      ·
        refine ⟨10424442408757534602755723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6949628272505023068503815 10424442408757534602755723)
        ·
          refine ⟨15636663613136301904133585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10424442408757534602755723 15636663613136301904133585)
          ·
            refine ⟨11727497709852226428100189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15636663613136301904133585 11727497709852226428100189)
            ·
              refine ⟨4397811641194584910537571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11727497709852226428100189 4397811641194584910537571)
              ·
                refine ⟨6596717461791877365806357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4397811641194584910537571 6596717461791877365806357)
                ·
                  refine ⟨309221131021494251522173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6596717461791877365806357 309221131021494251522173)
                  ·
                    rfl

theorem cell22_2709927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 6].length) (baseStart_2709927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709927 prefixEnd_2709927 := by exact prefixLift 2709927
  have htrace : WordTrace (prefixWord ++ tailWord_2709927) baseStart_2709927 baseEnd_2709927 := by
    simpa [prefixWord, tailWord_2709927, baseEnd_2709927] using wordTrace_append hprefix tailTrace_2709927
  have hstable : (prefixWord ++ tailWord_2709927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709927).length < 2 ^ (prefixWord ++ tailWord_2709927).sum := by decide
  have hdescent : baseEnd_2709927 < baseStart_2709927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709933 : List Nat := [1, 5, 2, 2, 3, 1, 2, 1, 5]
def baseStart_2709933 : Nat := 118140960795 + 2709933 * 2 ^ 59
def prefixEnd_2709933 : Nat := 4983230072969 + 3 ^ 40 * 2709933 * 2
def baseEnd_2709933 : Nat := 309221815662366912972167

theorem tailTrace_2709933 : CollatzResearch.WordTrace tailWord_2709933 prefixEnd_2709933 309221815662366912972167 := by
  unfold tailWord_2709933
  simp only [CollatzResearch.WordTrace]
  refine ⟨98839376491383035554550453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65892917660922023703033635 98839376491383035554550453)
  ·
    refine ⟨9266191546067159583239105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98839376491383035554550453 9266191546067159583239105)
    ·
      refine ⟨6949643659550369687429329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9266191546067159583239105 6949643659550369687429329)
      ·
        refine ⟨5212232744662777265571997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6949643659550369687429329 5212232744662777265571997)
        ·
          refine ⟨1954587279248541474589499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5212232744662777265571997 1954587279248541474589499)
          ·
            refine ⟨2931880918872812211884249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954587279248541474589499 2931880918872812211884249)
            ·
              refine ⟨2198910689154609158913187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2931880918872812211884249 2198910689154609158913187)
              ·
                refine ⟨3298366033731913738369781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2198910689154609158913187 3298366033731913738369781)
                ·
                  refine ⟨309221815662366912972167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3298366033731913738369781 309221815662366912972167)
                  ·
                    rfl

theorem cell22_2709933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_2709933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709933 prefixEnd_2709933 := by exact prefixLift 2709933
  have htrace : WordTrace (prefixWord ++ tailWord_2709933) baseStart_2709933 baseEnd_2709933 := by
    simpa [prefixWord, tailWord_2709933, baseEnd_2709933] using wordTrace_append hprefix tailTrace_2709933
  have hstable : (prefixWord ++ tailWord_2709933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709933).length < 2 ^ (prefixWord ++ tailWord_2709933).sum := by decide
  have hdescent : baseEnd_2709933 < baseStart_2709933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709974 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2709974 : Nat := 118140960795 + 2709974 * 2 ^ 59
def prefixEnd_2709974 : Nat := 4983230072969 + 3 ^ 40 * 2709974 * 2
def baseEnd_2709974 : Nat := 927679482124990298641375

theorem tailTrace_2709974 : CollatzResearch.WordTrace tailWord_2709974 prefixEnd_2709974 927679482124990298641375 := by
  unfold tailWord_2709974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6177554492764656222299561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65893914589489666371195317 6177554492764656222299561)
  ·
    refine ⟨4633165869573492166724671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6177554492764656222299561 4633165869573492166724671)
    ·
      refine ⟨6949748804360238250087007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633165869573492166724671 6949748804360238250087007)
      ·
        refine ⟨10424623206540357375130511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6949748804360238250087007 10424623206540357375130511)
        ·
          refine ⟨15636934809810536062695767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10424623206540357375130511 15636934809810536062695767)
          ·
            refine ⟨23455402214715804094043651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15636934809810536062695767 23455402214715804094043651)
            ·
              refine ⟨35183103322073706141065477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23455402214715804094043651 35183103322073706141065477)
              ·
                refine ⟨6596831872888819901449777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35183103322073706141065477 6596831872888819901449777)
                ·
                  refine ⟨4947623904666614926087333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6596831872888819901449777 4947623904666614926087333)
                  ·
                    refine ⟨927679482124990298641375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4947623904666614926087333 927679482124990298641375)
                    ·
                      rfl

theorem cell22_2709974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2709974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709974 prefixEnd_2709974 := by exact prefixLift 2709974
  have htrace : WordTrace (prefixWord ++ tailWord_2709974) baseStart_2709974 baseEnd_2709974 := by
    simpa [prefixWord, tailWord_2709974, baseEnd_2709974] using wordTrace_append hprefix tailTrace_2709974
  have hstable : (prefixWord ++ tailWord_2709974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709974).length < 2 ^ (prefixWord ++ tailWord_2709974).sum := by decide
  have hdescent : baseEnd_2709974 < baseStart_2709974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709985 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_2709985 : Nat := 118140960795 + 2709985 * 2 ^ 59
def prefixEnd_2709985 : Nat := 4983230072969 + 3 ^ 40 * 2709985 * 2
def baseEnd_2709985 : Nat := 927683247649789936616341

theorem tailTrace_2709985 : CollatzResearch.WordTrace tailWord_2709985 prefixEnd_2709985 927683247649789936616341 := by
  unfold tailWord_2709985
  simp only [CollatzResearch.WordTrace]
  refine ⟨98841273087194648435443409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65894182058129765623628939 98841273087194648435443409)
  ·
    refine ⟨74130954815395986326582557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98841273087194648435443409 74130954815395986326582557)
    ·
      refine ⟨27799108055773494872468459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74130954815395986326582557 27799108055773494872468459)
      ·
        refine ⟨41698662083660242308702689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27799108055773494872468459 41698662083660242308702689)
        ·
          refine ⟨31273996562745181731527017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41698662083660242308702689 31273996562745181731527017)
          ·
            refine ⟨23455497422058886298645263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31273996562745181731527017 23455497422058886298645263)
            ·
              refine ⟨35183246133088329447967895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23455497422058886298645263 35183246133088329447967895)
              ·
                refine ⟨52774869199632494171951843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35183246133088329447967895 52774869199632494171951843)
                ·
                  refine ⟨79162303799448741257927765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52774869199632494171951843 79162303799448741257927765)
                  ·
                    refine ⟨927683247649789936616341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79162303799448741257927765 927683247649789936616341)
                    ·
                      rfl

theorem cell22_2709985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_2709985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709985 prefixEnd_2709985 := by exact prefixLift 2709985
  have htrace : WordTrace (prefixWord ++ tailWord_2709985) baseStart_2709985 baseEnd_2709985 := by
    simpa [prefixWord, tailWord_2709985, baseEnd_2709985] using wordTrace_append hprefix tailTrace_2709985
  have hstable : (prefixWord ++ tailWord_2709985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709985).length < 2 ^ (prefixWord ++ tailWord_2709985).sum := by decide
  have hdescent : baseEnd_2709985 < baseStart_2709985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709989 : List Nat := [1, 3, 1, 5, 2, 2, 1, 7]
def baseStart_2709989 : Nat := 118140960795 + 2709989 * 2 ^ 59
def prefixEnd_2709989 : Nat := 4983230072969 + 3 ^ 40 * 2709989 * 2
def baseEnd_2709989 : Nat := 103076068547948362168481

theorem tailTrace_2709989 : CollatzResearch.WordTrace tailWord_2709989 prefixEnd_2709989 103076068547948362168481 := by
  unfold tailWord_2709989
  simp only [CollatzResearch.WordTrace]
  refine ⟨98841418979180157118589021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65894279319453438079059347 98841418979180157118589021)
  ·
    refine ⟨37065532117192558919470883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98841418979180157118589021 37065532117192558919470883)
    ·
      refine ⟨55598298175788838379206325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37065532117192558919470883 55598298175788838379206325)
      ·
        refine ⟨5212340453980203598050593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55598298175788838379206325 5212340453980203598050593)
        ·
          refine ⟨3909255340485152698537945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5212340453980203598050593 3909255340485152698537945)
          ·
            refine ⟨2931941505363864523903459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3909255340485152698537945 2931941505363864523903459)
            ·
              refine ⟨4397912258045796785855189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931941505363864523903459 4397912258045796785855189)
              ·
                refine ⟨103076068547948362168481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4397912258045796785855189 103076068547948362168481)
                ·
                  rfl

theorem cell22_2709989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 7].length) (baseStart_2709989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2709989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2709989 prefixEnd_2709989 := by exact prefixLift 2709989
  have htrace : WordTrace (prefixWord ++ tailWord_2709989) baseStart_2709989 baseEnd_2709989 := by
    simpa [prefixWord, tailWord_2709989, baseEnd_2709989] using wordTrace_append hprefix tailTrace_2709989
  have hstable : (prefixWord ++ tailWord_2709989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709989).length < 2 ^ (prefixWord ++ tailWord_2709989).sum := by decide
  have hdescent : baseEnd_2709989 < baseStart_2709989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710015 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 1, 7]
def baseStart_2710015 : Nat := 118140960795 + 2710015 * 2 ^ 59
def prefixEnd_2710015 : Nat := 4983230072969 + 3 ^ 40 * 2710015 * 2
def baseEnd_2710015 : Nat := 927693517262879858366249

theorem tailTrace_2710015 : CollatzResearch.WordTrace tailWord_2710015 prefixEnd_2710015 927693517262879858366249 := by
  unfold tailWord_2710015
  simp only [CollatzResearch.WordTrace]
  refine ⟨98842367277085963559035499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65894911518057309039356999 98842367277085963559035499)
  ·
    refine ⟨148263550915628945338553249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98842367277085963559035499 148263550915628945338553249)
    ·
      refine ⟨111197663186721709003914937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148263550915628945338553249 111197663186721709003914937)
      ·
        refine ⟨83398247390041281752936203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111197663186721709003914937 83398247390041281752936203)
        ·
          refine ⟨125097371085061922629404305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83398247390041281752936203 125097371085061922629404305)
          ·
            refine ⟨93823028313796441972053229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125097371085061922629404305 93823028313796441972053229)
            ·
              refine ⟨35183635617673665739519961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93823028313796441972053229 35183635617673665739519961)
              ·
                refine ⟨26387726713255249304639971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35183635617673665739519961 26387726713255249304639971)
                ·
                  refine ⟨39581590069882873956959957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26387726713255249304639971 39581590069882873956959957)
                  ·
                    refine ⟨927693517262879858366249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39581590069882873956959957 927693517262879858366249)
                    ·
                      rfl

theorem cell22_2710015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_2710015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710015 prefixEnd_2710015 := by exact prefixLift 2710015
  have htrace : WordTrace (prefixWord ++ tailWord_2710015) baseStart_2710015 baseEnd_2710015 := by
    simpa [prefixWord, tailWord_2710015, baseEnd_2710015] using wordTrace_append hprefix tailTrace_2710015
  have hstable : (prefixWord ++ tailWord_2710015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710015).length < 2 ^ (prefixWord ++ tailWord_2710015).sum := by decide
  have hdescent : baseEnd_2710015 < baseStart_2710015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710094 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_2710094 : Nat := 118140960795 + 2710094 * 2 ^ 59
def prefixEnd_2710094 : Nat := 4983230072969 + 3 ^ 40 * 2710094 * 2
def baseEnd_2710094 : Nat := 927720560577349985641007

theorem tailTrace_2710094 : CollatzResearch.WordTrace tailWord_2710094 prefixEnd_2710094 927720560577349985641007 := by
  unfold tailWord_2710094
  simp only [CollatzResearch.WordTrace]
  refine ⟨12355656080474970006395167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65896832429199840034107557 12355656080474970006395167)
  ·
    refine ⟨18533484120712455009592751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12355656080474970006395167 18533484120712455009592751)
    ·
      refine ⟨27800226181068682514389127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18533484120712455009592751 27800226181068682514389127)
      ·
        refine ⟨41700339271603023771583691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27800226181068682514389127 41700339271603023771583691)
        ·
          refine ⟨62550508907404535657375537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41700339271603023771583691 62550508907404535657375537)
          ·
            refine ⟨46912881680553401743031653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62550508907404535657375537 46912881680553401743031653)
            ·
              refine ⟨8796165315103762826818435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46912881680553401743031653 8796165315103762826818435)
              ·
                refine ⟨13194247972655644240227653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8796165315103762826818435 13194247972655644240227653)
                ·
                  refine ⟨2473921494872933295042685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13194247972655644240227653 2473921494872933295042685)
                  ·
                    refine ⟨927720560577349985641007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2473921494872933295042685 927720560577349985641007)
                    ·
                      rfl

theorem cell22_2710094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_2710094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710094 prefixEnd_2710094 := by exact prefixLift 2710094
  have htrace : WordTrace (prefixWord ++ tailWord_2710094) baseStart_2710094 baseEnd_2710094 := by
    simpa [prefixWord, tailWord_2710094, baseEnd_2710094] using wordTrace_append hprefix tailTrace_2710094
  have hstable : (prefixWord ++ tailWord_2710094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710094).length < 2 ^ (prefixWord ++ tailWord_2710094).sum := by decide
  have hdescent : baseEnd_2710094 < baseStart_2710094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710126 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_2710126 : Nat := 118140960795 + 2710126 * 2 ^ 59
def prefixEnd_2710126 : Nat := 4983230072969 + 3 ^ 40 * 2710126 * 2
def baseEnd_2710126 : Nat := 927731514831312568840909

theorem tailTrace_2710126 : CollatzResearch.WordTrace tailWord_2710126 prefixEnd_2710126 927731514831312568840909 := by
  unfold tailWord_2710126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12355801972460478689540779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65897610519789219677550821 12355801972460478689540779)
  ·
    refine ⟨18533702958690718034311169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12355801972460478689540779 18533702958690718034311169)
    ·
      refine ⟨13900277219018038525733377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18533702958690718034311169 13900277219018038525733377)
      ·
        refine ⟨10425207914263528894300033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13900277219018038525733377 10425207914263528894300033)
        ·
          refine ⟨7818905935697646670725025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10425207914263528894300033 7818905935697646670725025)
          ·
            refine ⟨5864179451773235003043769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7818905935697646670725025 5864179451773235003043769)
            ·
              refine ⟨4398134588829926252282827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5864179451773235003043769 4398134588829926252282827)
              ·
                refine ⟨6597201883244889378424241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398134588829926252282827 6597201883244889378424241)
                ·
                  refine ⟨4947901412433667033818181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6597201883244889378424241 4947901412433667033818181)
                  ·
                    refine ⟨927731514831312568840909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4947901412433667033818181 927731514831312568840909)
                    ·
                      rfl

theorem cell22_2710126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_2710126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710126 prefixEnd_2710126 := by exact prefixLift 2710126
  have htrace : WordTrace (prefixWord ++ tailWord_2710126) baseStart_2710126 baseEnd_2710126 := by
    simpa [prefixWord, tailWord_2710126, baseEnd_2710126] using wordTrace_append hprefix tailTrace_2710126
  have hstable : (prefixWord ++ tailWord_2710126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710126).length < 2 ^ (prefixWord ++ tailWord_2710126).sum := by decide
  have hdescent : baseEnd_2710126 < baseStart_2710126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710190 : List Nat := [4, 1, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2710190 : Nat := 118140960795 + 2710190 * 2 ^ 59
def prefixEnd_2710190 : Nat := 4983230072969 + 3 ^ 40 * 2710190 * 2
def baseEnd_2710190 : Nat := 927753423339237735240713

theorem tailTrace_2710190 : CollatzResearch.WordTrace tailWord_2710190 prefixEnd_2710190 927753423339237735240713 := by
  unfold tailWord_2710190
  simp only [CollatzResearch.WordTrace]
  refine ⟨12356093756431496055832003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65899166700967978964437349 12356093756431496055832003)
  ·
    refine ⟨18534140634647244083748005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12356093756431496055832003 18534140634647244083748005)
    ·
      refine ⟨3475151368996358265702751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18534140634647244083748005 3475151368996358265702751)
      ·
        refine ⟨5212727053494537398554127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475151368996358265702751 5212727053494537398554127)
        ·
          refine ⟨7819090580241806097831191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5212727053494537398554127 7819090580241806097831191)
          ·
            refine ⟨11728635870362709146746787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7819090580241806097831191 11728635870362709146746787)
            ·
              refine ⟨17592953805544063720120181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11728635870362709146746787 17592953805544063720120181)
              ·
                refine ⟨1649339419269755973761267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17592953805544063720120181 1649339419269755973761267)
                ·
                  refine ⟨2474009128904633960641901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649339419269755973761267 2474009128904633960641901)
                  ·
                    refine ⟨927753423339237735240713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2474009128904633960641901 927753423339237735240713)
                    ·
                      rfl

theorem cell22_2710190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2710190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710190 prefixEnd_2710190 := by exact prefixLift 2710190
  have htrace : WordTrace (prefixWord ++ tailWord_2710190) baseStart_2710190 baseEnd_2710190 := by
    simpa [prefixWord, tailWord_2710190, baseEnd_2710190] using wordTrace_append hprefix tailTrace_2710190
  have hstable : (prefixWord ++ tailWord_2710190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710190).length < 2 ^ (prefixWord ++ tailWord_2710190).sum := by decide
  have hdescent : baseEnd_2710190 < baseStart_2710190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710244 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_2710244 : Nat := 118140960795 + 2710244 * 2 ^ 59
def prefixEnd_2710244 : Nat := 4983230072969 + 3 ^ 40 * 2710244 * 2
def baseEnd_2710244 : Nat := 927771908642799594390547

theorem tailTrace_2710244 : CollatzResearch.WordTrace tailWord_2710244 prefixEnd_2710244 927771908642799594390547 := by
  unfold tailWord_2710244
  simp only [CollatzResearch.WordTrace]
  refine ⟨49425359796628167834560893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65900479728837557112747857 49425359796628167834560893)
  ·
    refine ⟨18534509923735562937960335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49425359796628167834560893 18534509923735562937960335)
    ·
      refine ⟨27801764885603344406940503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18534509923735562937960335 27801764885603344406940503)
      ·
        refine ⟨41702647328405016610410755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27801764885603344406940503 41702647328405016610410755)
        ·
          refine ⟨62553970992607524915616133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41702647328405016610410755 62553970992607524915616133)
          ·
            refine ⟨11728869561113910921678025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62553970992607524915616133 11728869561113910921678025)
            ·
              refine ⟨8796652170835433191258519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11728869561113910921678025 8796652170835433191258519)
              ·
                refine ⟨13194978256253149786887779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8796652170835433191258519 13194978256253149786887779)
                ·
                  refine ⟨19792467384379724680331669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13194978256253149786887779 19792467384379724680331669)
                  ·
                    refine ⟨927771908642799594390547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19792467384379724680331669 927771908642799594390547)
                    ·
                      rfl

theorem cell22_2710244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_2710244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710244 prefixEnd_2710244 := by exact prefixLift 2710244
  have htrace : WordTrace (prefixWord ++ tailWord_2710244) baseStart_2710244 baseEnd_2710244 := by
    simpa [prefixWord, tailWord_2710244, baseEnd_2710244] using wordTrace_append hprefix tailTrace_2710244
  have hstable : (prefixWord ++ tailWord_2710244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710244).length < 2 ^ (prefixWord ++ tailWord_2710244).sum := by decide
  have hdescent : baseEnd_2710244 < baseStart_2710244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710280 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 2, 3]
def baseStart_2710280 : Nat := 118140960795 + 2710280 * 2 ^ 59
def prefixEnd_2710280 : Nat := 4983230072969 + 3 ^ 40 * 2710280 * 2
def baseEnd_2710280 : Nat := 927784232178507500490437

theorem tailTrace_2710280 : CollatzResearch.WordTrace tailWord_2710280 prefixEnd_2710280 927784232178507500490437 := by
  unfold tailWord_2710280
  simp only [CollatzResearch.WordTrace]
  refine ⟨49426016310562956908716147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65901355080750609211621529 49426016310562956908716147)
  ·
    refine ⟨74139024465844435363074221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49426016310562956908716147 74139024465844435363074221)
    ·
      refine ⟨27802134174691663261152833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74139024465844435363074221 27802134174691663261152833)
      ·
        refine ⟨20851600631018747445864625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27802134174691663261152833 20851600631018747445864625)
        ·
          refine ⟨15638700473264060584398469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20851600631018747445864625 15638700473264060584398469)
          ·
            refine ⟨2932256338737011359574713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15638700473264060584398469 2932256338737011359574713)
            ·
              refine ⟨2199192254052758519681035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932256338737011359574713 2199192254052758519681035)
              ·
                refine ⟨3298788381079137779521553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2199192254052758519681035 3298788381079137779521553)
                ·
                  refine ⟨2474091285809353334641165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3298788381079137779521553 2474091285809353334641165)
                  ·
                    refine ⟨927784232178507500490437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2474091285809353334641165 927784232178507500490437)
                    ·
                      rfl

theorem cell22_2710280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_2710280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710280 prefixEnd_2710280 := by exact prefixLift 2710280
  have htrace : WordTrace (prefixWord ++ tailWord_2710280) baseStart_2710280 baseEnd_2710280 := by
    simpa [prefixWord, tailWord_2710280, baseEnd_2710280] using wordTrace_append hprefix tailTrace_2710280
  have hstable : (prefixWord ++ tailWord_2710280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710280).length < 2 ^ (prefixWord ++ tailWord_2710280).sum := by decide
  have hdescent : baseEnd_2710280 < baseStart_2710280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710321 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 5]
def baseStart_2710321 : Nat := 118140960795 + 2710321 * 2 ^ 59
def prefixEnd_2710321 : Nat := 4983230072969 + 3 ^ 40 * 2710321 * 2
def baseEnd_2710321 : Nat := 309266089105465686738437

theorem tailTrace_2710321 : CollatzResearch.WordTrace tailWord_2710321 prefixEnd_2710321 309266089105465686738437 := by
  unfold tailWord_2710321
  simp only [CollatzResearch.WordTrace]
  refine ⟨98853528013977377819674817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65902352009318251879783211 98853528013977377819674817)
  ·
    refine ⟨74140146010483033364756113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98853528013977377819674817 74140146010483033364756113)
    ·
      refine ⟨55605109507862275023567085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74140146010483033364756113 55605109507862275023567085)
      ·
        refine ⟨20851916065448353133837657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55605109507862275023567085 20851916065448353133837657)
        ·
          refine ⟨15638937049086264850378243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20851916065448353133837657 15638937049086264850378243)
          ·
            refine ⟨23458405573629397275567365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15638937049086264850378243 23458405573629397275567365)
            ·
              refine ⟨4398451045055511989168881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23458405573629397275567365 4398451045055511989168881)
              ·
                refine ⟨3298838283791633991876661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4398451045055511989168881 3298838283791633991876661)
                ·
                  refine ⟨309266089105465686738437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3298838283791633991876661 309266089105465686738437)
                  ·
                    rfl

theorem cell22_2710321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_2710321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710321 prefixEnd_2710321 := by exact prefixLift 2710321
  have htrace : WordTrace (prefixWord ++ tailWord_2710321) baseStart_2710321 baseEnd_2710321 := by
    simpa [prefixWord, tailWord_2710321, baseEnd_2710321] using wordTrace_append hprefix tailTrace_2710321
  have hstable : (prefixWord ++ tailWord_2710321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710321).length < 2 ^ (prefixWord ++ tailWord_2710321).sum := by decide
  have hdescent : baseEnd_2710321 < baseStart_2710321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710325 : List Nat := [1, 3, 3, 1, 3, 2, 1, 4, 1, 3]
def baseStart_2710325 : Nat := 118140960795 + 2710325 * 2 ^ 59
def prefixEnd_2710325 : Nat := 4983230072969 + 3 ^ 40 * 2710325 * 2
def baseEnd_2710325 : Nat := 927799636598142383115299

theorem tailTrace_2710325 : CollatzResearch.WordTrace tailWord_2710325 prefixEnd_2710325 927799636598142383115299 := by
  unfold tailWord_2710325
  simp only [CollatzResearch.WordTrace]
  refine ⟨98853673905962886502820429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65902449270641924335213619 98853673905962886502820429)
  ·
    refine ⟨37070127714736082438557661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98853673905962886502820429 37070127714736082438557661)
    ·
      refine ⟨13901297893026030914459123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37070127714736082438557661 13901297893026030914459123)
      ·
        refine ⟨20851946839539046371688685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13901297893026030914459123 20851946839539046371688685)
        ·
          refine ⟨7819480064827142389383257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20851946839539046371688685 7819480064827142389383257)
          ·
            refine ⟨5864610048620356792037443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7819480064827142389383257 5864610048620356792037443)
            ·
              refine ⟨8796915072930535188056165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5864610048620356792037443 8796915072930535188056165)
              ·
                refine ⟨1649421576174475347760531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8796915072930535188056165 1649421576174475347760531)
                ·
                  refine ⟨2474132364261713021640797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649421576174475347760531 2474132364261713021640797)
                  ·
                    refine ⟨927799636598142383115299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2474132364261713021640797 927799636598142383115299)
                    ·
                      rfl

theorem cell22_2710325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_2710325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710325 prefixEnd_2710325 := by exact prefixLift 2710325
  have htrace : WordTrace (prefixWord ++ tailWord_2710325) baseStart_2710325 baseEnd_2710325 := by
    simpa [prefixWord, tailWord_2710325, baseEnd_2710325] using wordTrace_append hprefix tailTrace_2710325
  have hstable : (prefixWord ++ tailWord_2710325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710325).length < 2 ^ (prefixWord ++ tailWord_2710325).sum := by decide
  have hdescent : baseEnd_2710325 < baseStart_2710325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710342 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_2710342 : Nat := 118140960795 + 2710342 * 2 ^ 59
def prefixEnd_2710342 : Nat := 4983230072969 + 3 ^ 40 * 2710342 * 2
def baseEnd_2710342 : Nat := 927805456045560005440247

theorem tailTrace_2710342 : CollatzResearch.WordTrace tailWord_2710342 prefixEnd_2710342 927805456045560005440247 := by
  unfold tailWord_2710342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089196685840665575193415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65902862631267532270792853 3089196685840665575193415)
  ·
    refine ⟨4633795028760998362790123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3089196685840665575193415 4633795028760998362790123)
    ·
      refine ⟨6950692543141497544185185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4633795028760998362790123 6950692543141497544185185)
      ·
        refine ⟨5213019407356123158138889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6950692543141497544185185 5213019407356123158138889)
        ·
          refine ⟨3909764555517092368604167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5213019407356123158138889 3909764555517092368604167)
          ·
            refine ⟨5864646833275638552906251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3909764555517092368604167 5864646833275638552906251)
            ·
              refine ⟨8796970249913457829359377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5864646833275638552906251 8796970249913457829359377)
              ·
                refine ⟨6597727687435093372019533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8796970249913457829359377 6597727687435093372019533)
                ·
                  refine ⟨2474147882788160014507325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6597727687435093372019533 2474147882788160014507325)
                  ·
                    refine ⟨927805456045560005440247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2474147882788160014507325 927805456045560005440247)
                    ·
                      rfl

theorem cell22_2710342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_2710342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710342 prefixEnd_2710342 := by exact prefixLift 2710342
  have htrace : WordTrace (prefixWord ++ tailWord_2710342) baseStart_2710342 baseEnd_2710342 := by
    simpa [prefixWord, tailWord_2710342, baseEnd_2710342] using wordTrace_append hprefix tailTrace_2710342
  have hstable : (prefixWord ++ tailWord_2710342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710342).length < 2 ^ (prefixWord ++ tailWord_2710342).sum := by decide
  have hdescent : baseEnd_2710342 < baseStart_2710342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710394 : List Nat := [3, 1, 1, 1, 1, 1, 3, 11]
def baseStart_2710394 : Nat := 118140960795 + 2710394 * 2 ^ 59
def prefixEnd_2710394 : Nat := 4983230072969 + 3 ^ 40 * 2710394 * 2
def baseEnd_2710394 : Nat := 103091472967583244793343

theorem tailTrace_2710394 : CollatzResearch.WordTrace tailWord_2710394 prefixEnd_2710394 103091472967583244793343 := by
  unfold tailWord_2710394
  simp only [CollatzResearch.WordTrace]
  refine ⟨24714047635678227821770559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65904127028475274191388157 24714047635678227821770559)
  ·
    refine ⟨37071071453517341732655839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24714047635678227821770559 37071071453517341732655839)
    ·
      refine ⟨55606607180276012598983759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37071071453517341732655839 55606607180276012598983759)
      ·
        refine ⟨83409910770414018898475639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55606607180276012598983759 83409910770414018898475639)
        ·
          refine ⟨125114866155621028347713459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83409910770414018898475639 125114866155621028347713459)
          ·
            refine ⟨187672299233431542521570189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125114866155621028347713459 187672299233431542521570189)
            ·
              refine ⟨70377112212536828445588821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187672299233431542521570189 70377112212536828445588821)
              ·
                refine ⟨103091472967583244793343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 70377112212536828445588821 103091472967583244793343)
                ·
                  rfl

theorem cell22_2710394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_2710394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710394 prefixEnd_2710394 := by exact prefixLift 2710394
  have htrace : WordTrace (prefixWord ++ tailWord_2710394) baseStart_2710394 baseEnd_2710394 := by
    simpa [prefixWord, tailWord_2710394, baseEnd_2710394] using wordTrace_append hprefix tailTrace_2710394
  have hstable : (prefixWord ++ tailWord_2710394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710394).length < 2 ^ (prefixWord ++ tailWord_2710394).sum := by decide
  have hdescent : baseEnd_2710394 < baseStart_2710394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710411 : List Nat := [1, 1, 1, 1, 4, 2, 6, 6]
def baseStart_2710411 : Nat := 118140960795 + 2710411 * 2 ^ 59
def prefixEnd_2710411 : Nat := 4983230072969 + 3 ^ 40 * 2710411 * 2
def baseEnd_2710411 : Nat := 103092119572851869496115

theorem tailTrace_2710411 : CollatzResearch.WordTrace tailWord_2710411 prefixEnd_2710411 103092119572851869496115 := by
  unfold tailWord_2710411
  simp only [CollatzResearch.WordTrace]
  refine ⟨98856810583651323190451087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65904540389100882126967391 98856810583651323190451087)
  ·
    refine ⟨148285215875476984785676631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98856810583651323190451087 148285215875476984785676631)
    ·
      refine ⟨222427823813215477178514947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148285215875476984785676631 222427823813215477178514947)
      ·
        refine ⟨333641735719823215767772421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222427823813215477178514947 333641735719823215767772421)
        ·
          refine ⟨62557825447466852956457329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333641735719823215767772421 62557825447466852956457329)
          ·
            refine ⟨46918369085600139717342997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62557825447466852956457329 46918369085600139717342997)
            ·
              refine ⟨2199298550887506549250453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46918369085600139717342997 2199298550887506549250453)
              ·
                refine ⟨103092119572851869496115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2199298550887506549250453 103092119572851869496115)
                ·
                  rfl

theorem cell22_2710411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 6].length) (baseStart_2710411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710411 prefixEnd_2710411 := by exact prefixLift 2710411
  have htrace : WordTrace (prefixWord ++ tailWord_2710411) baseStart_2710411 baseEnd_2710411 := by
    simpa [prefixWord, tailWord_2710411, baseEnd_2710411] using wordTrace_append hprefix tailTrace_2710411
  have hstable : (prefixWord ++ tailWord_2710411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710411).length < 2 ^ (prefixWord ++ tailWord_2710411).sum := by decide
  have hdescent : baseEnd_2710411 < baseStart_2710411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710428 : List Nat := [2, 2, 3, 3, 2, 2, 8]
def baseStart_2710428 : Nat := 118140960795 + 2710428 * 2 ^ 59
def prefixEnd_2710428 : Nat := 4983230072969 + 3 ^ 40 * 2710428 * 2
def baseEnd_2710428 : Nat := 34364255392706831399629

theorem tailTrace_2710428 : CollatzResearch.WordTrace tailWord_2710428 prefixEnd_2710428 34364255392706831399629 := by
  unfold tailWord_2710428
  simp only [CollatzResearch.WordTrace]
  refine ⟨49428715312294867546909969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65904953749726490062546625 49428715312294867546909969)
  ·
    refine ⟨37071536484221150660182477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49428715312294867546909969 37071536484221150660182477)
    ·
      refine ⟨13901826181582931497568429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37071536484221150660182477 13901826181582931497568429)
      ·
        refine ⟨5213184818093599311588161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13901826181582931497568429 5213184818093599311588161)
        ·
          refine ⟨3909888613570199483691121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5213184818093599311588161 3909888613570199483691121)
          ·
            refine ⟨2932416460177649612768341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3909888613570199483691121 2932416460177649612768341)
            ·
              refine ⟨34364255392706831399629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2932416460177649612768341 34364255392706831399629)
              ·
                rfl

theorem cell22_2710428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 8].length) (baseStart_2710428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710428 prefixEnd_2710428 := by exact prefixLift 2710428
  have htrace : WordTrace (prefixWord ++ tailWord_2710428) baseStart_2710428 baseEnd_2710428 := by
    simpa [prefixWord, tailWord_2710428, baseEnd_2710428] using wordTrace_append hprefix tailTrace_2710428
  have hstable : (prefixWord ++ tailWord_2710428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710428).length < 2 ^ (prefixWord ++ tailWord_2710428).sum := by decide
  have hdescent : baseEnd_2710428 < baseStart_2710428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710445 : List Nat := [1, 5, 2, 3, 1, 1, 2, 7]
def baseStart_2710445 : Nat := 118140960795 + 2710445 * 2 ^ 59
def prefixEnd_2710445 : Nat := 4983230072969 + 3 ^ 40 * 2710445 * 2
def baseEnd_2710445 : Nat := 103093412783389118901659

theorem tailTrace_2710445 : CollatzResearch.WordTrace tailWord_2710445 prefixEnd_2710445 103093412783389118901659 := by
  unfold tailWord_2710445
  simp only [CollatzResearch.WordTrace]
  refine ⟨98858050665528146997188789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65905367110352097998125859 98858050665528146997188789)
  ·
    refine ⟨9267942249893263780986449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98858050665528146997188789 9267942249893263780986449)
    ·
      refine ⟨6950956687419947835739837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9267942249893263780986449 6950956687419947835739837)
      ·
        refine ⟨2606608757782480438402439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6950956687419947835739837 2606608757782480438402439)
        ·
          refine ⟨3909913136673720657603659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2606608757782480438402439 3909913136673720657603659)
          ·
            refine ⟨5864869705010580986405489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3909913136673720657603659 5864869705010580986405489)
            ·
              refine ⟨4398652278757935739804117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5864869705010580986405489 4398652278757935739804117)
              ·
                refine ⟨103093412783389118901659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4398652278757935739804117 103093412783389118901659)
                ·
                  rfl

theorem cell22_2710445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 7].length) (baseStart_2710445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710445 prefixEnd_2710445 := by exact prefixLift 2710445
  have htrace : WordTrace (prefixWord ++ tailWord_2710445) baseStart_2710445 baseEnd_2710445 := by
    simpa [prefixWord, tailWord_2710445, baseEnd_2710445] using wordTrace_append hprefix tailTrace_2710445
  have hstable : (prefixWord ++ tailWord_2710445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710445).length < 2 ^ (prefixWord ++ tailWord_2710445).sum := by decide
  have hdescent : baseEnd_2710445 < baseStart_2710445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710449 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 2, 3]
def baseStart_2710449 : Nat := 118140960795 + 2710449 * 2 ^ 59
def prefixEnd_2710449 : Nat := 4983230072969 + 3 ^ 40 * 2710449 * 2
def baseEnd_2710449 : Nat := 927842084332247393014919

theorem tailTrace_2710449 : CollatzResearch.WordTrace tailWord_2710449 prefixEnd_2710449 927842084332247393014919 := by
  unfold tailWord_2710449
  simp only [CollatzResearch.WordTrace]
  refine ⟨98858196557513655680334401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65905464371675770453556267 98858196557513655680334401)
  ·
    refine ⟨74143647418135241760250801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98858196557513655680334401 74143647418135241760250801)
    ·
      refine ⟨55607735563601431320188101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74143647418135241760250801 55607735563601431320188101)
      ·
        refine ⟨10426450418175268372535269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55607735563601431320188101 10426450418175268372535269)
        ·
          refine ⟨1954959453407862819850363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10426450418175268372535269 1954959453407862819850363)
          ·
            refine ⟨2932439180111794229775545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954959453407862819850363 2932439180111794229775545)
            ·
              refine ⟨2199329385083845672331659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932439180111794229775545 2199329385083845672331659)
              ·
                refine ⟨3298994077625768508497489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2199329385083845672331659 3298994077625768508497489)
                ·
                  refine ⟨2474245558219326381373117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3298994077625768508497489 2474245558219326381373117)
                  ·
                    refine ⟨927842084332247393014919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2474245558219326381373117 927842084332247393014919)
                    ·
                      rfl

theorem cell22_2710449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_2710449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710449 prefixEnd_2710449 := by exact prefixLift 2710449
  have htrace : WordTrace (prefixWord ++ tailWord_2710449) baseStart_2710449 baseEnd_2710449 := by
    simpa [prefixWord, tailWord_2710449, baseEnd_2710449] using wordTrace_append hprefix tailTrace_2710449
  have hstable : (prefixWord ++ tailWord_2710449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710449).length < 2 ^ (prefixWord ++ tailWord_2710449).sum := by decide
  have hdescent : baseEnd_2710449 < baseStart_2710449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
