import V185TrunkScan23Chunk0406

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2406765 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2406765 : Nat := 118140960795 + 2406765 * 2 ^ 59
def prefixEnd_2406765 : Nat := 4983230072969 + 3 ^ 40 * 2406765 * 2
def baseEnd_2406765 : Nat := 1235827267418381254568995

theorem tailTrace_2406765 : CollatzResearch.WordTrace tailWord_2406765 prefixEnd_2406765 1235827267418381254568995 := by
  unfold tailWord_2406765
  simp only [CollatzResearch.WordTrace]
  refine ⟨87781931125708922582325749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58521287417139281721550499 87781931125708922582325749)
  ·
    refine ⟨8229556043035211492093039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87781931125708922582325749 8229556043035211492093039)
    ·
      refine ⟨12344334064552817238139559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8229556043035211492093039 12344334064552817238139559)
      ·
        refine ⟨18516501096829225857209339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12344334064552817238139559 18516501096829225857209339)
        ·
          refine ⟨27774751645243838785814009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18516501096829225857209339 27774751645243838785814009)
          ·
            refine ⟨20831063733932879089360507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27774751645243838785814009 20831063733932879089360507)
            ·
              refine ⟨31246595600899318634040761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20831063733932879089360507 31246595600899318634040761)
              ·
                refine ⟨23434946700674488975530571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31246595600899318634040761 23434946700674488975530571)
                ·
                  refine ⟨35152420051011733463295857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23434946700674488975530571 35152420051011733463295857)
                  ·
                    refine ⟨26364315038258800097471893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35152420051011733463295857 26364315038258800097471893)
                    ·
                      refine ⟨1235827267418381254568995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26364315038258800097471893 1235827267418381254568995)
                      ·
                        rfl

theorem cell23_2406765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2406765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406765 prefixEnd_2406765 := by exact prefixLift 2406765
  have htrace : WordTrace (prefixWord ++ tailWord_2406765) baseStart_2406765 baseEnd_2406765 := by
    simpa [prefixWord, tailWord_2406765, baseEnd_2406765] using wordTrace_append hprefix tailTrace_2406765
  have hstable : (prefixWord ++ tailWord_2406765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406765).length < 2 ^ (prefixWord ++ tailWord_2406765).sum := by decide
  have hdescent : baseEnd_2406765 < baseStart_2406765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406792 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 1, 5]
def baseStart_2406792 : Nat := 118140960795 + 2406792 * 2 ^ 59
def prefixEnd_2406792 : Nat := 4983230072969 + 3 ^ 40 * 2406792 * 2
def baseEnd_2406792 : Nat := 411947043798684216310457

theorem tailTrace_2406792 : CollatzResearch.WordTrace tailWord_2406792 prefixEnd_2406792 411947043798684216310457 := by
  unfold tailWord_2406792
  simp only [CollatzResearch.WordTrace]
  refine ⟨43891457948305553096779315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58521943931074070795705753 43891457948305553096779315)
  ·
    refine ⟨65837186922458329645168973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43891457948305553096779315 65837186922458329645168973)
    ·
      refine ⟨24688945095921873616938365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65837186922458329645168973 24688945095921873616938365)
      ·
        refine ⟨9258354410970702606351887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24688945095921873616938365 9258354410970702606351887)
        ·
          refine ⟨13887531616456053909527831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9258354410970702606351887 13887531616456053909527831)
          ·
            refine ⟨20831297424684080864291747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13887531616456053909527831 20831297424684080864291747)
            ·
              refine ⟨31246946137026121296437621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20831297424684080864291747 31246946137026121296437621)
              ·
                refine ⟨2929401200346198871541027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31246946137026121296437621 2929401200346198871541027)
                ·
                  refine ⟨4394101800519298307311541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2929401200346198871541027 4394101800519298307311541)
                  ·
                    refine ⟨411947043798684216310457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4394101800519298307311541 411947043798684216310457)
                    ·
                      rfl

theorem cell23_2406792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_2406792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406792 prefixEnd_2406792 := by exact prefixLift 2406792
  have htrace : WordTrace (prefixWord ++ tailWord_2406792) baseStart_2406792 baseEnd_2406792 := by
    simpa [prefixWord, tailWord_2406792, baseEnd_2406792] using wordTrace_append hprefix tailTrace_2406792
  have hstable : (prefixWord ++ tailWord_2406792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406792).length < 2 ^ (prefixWord ++ tailWord_2406792).sum := by decide
  have hdescent : baseEnd_2406792 < baseStart_2406792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406825 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 4]
def baseStart_2406825 : Nat := 118140960795 + 2406825 * 2 ^ 59
def prefixEnd_2406825 : Nat := 4983230072969 + 3 ^ 40 * 2406825 * 2
def baseEnd_2406825 : Nat := 1235858076257651019818719

theorem tailTrace_2406825 : CollatzResearch.WordTrace tailWord_2406825 prefixEnd_2406825 1235858076257651019818719 := by
  unfold tailWord_2406825
  simp only [CollatzResearch.WordTrace]
  refine ⟨87784119505491552829509929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58522746336994368553006619 87784119505491552829509929)
  ·
    refine ⟨65838089629118664622132447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87784119505491552829509929 65838089629118664622132447)
    ·
      refine ⟨98757134443677996933198671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65838089629118664622132447 98757134443677996933198671)
      ·
        refine ⟨148135701665516995399798007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98757134443677996933198671 148135701665516995399798007)
        ·
          refine ⟨222203552498275493099697011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148135701665516995399798007 222203552498275493099697011)
          ·
            refine ⟨333305328747413239649545517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222203552498275493099697011 333305328747413239649545517)
            ·
              refine ⟨124989498280279964868579569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 333305328747413239649545517 124989498280279964868579569)
              ·
                refine ⟨93742123710209973651434677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124989498280279964868579569 93742123710209973651434677)
                ·
                  refine ⟨8788324097832185029822001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93742123710209973651434677 8788324097832185029822001)
                  ·
                    refine ⟨6591243073374138772366501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8788324097832185029822001 6591243073374138772366501)
                    ·
                      refine ⟨1235858076257651019818719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6591243073374138772366501 1235858076257651019818719)
                      ·
                        rfl

theorem cell23_2406825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_2406825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406825 prefixEnd_2406825 := by exact prefixLift 2406825
  have htrace : WordTrace (prefixWord ++ tailWord_2406825) baseStart_2406825 baseEnd_2406825 := by
    simpa [prefixWord, tailWord_2406825, baseEnd_2406825] using wordTrace_append hprefix tailTrace_2406825
  have hstable : (prefixWord ++ tailWord_2406825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406825).length < 2 ^ (prefixWord ++ tailWord_2406825).sum := by decide
  have hdescent : baseEnd_2406825 < baseStart_2406825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406852 : List Nat := [2, 3, 3, 2, 2, 11]
def baseStart_2406852 : Nat := 118140960795 + 2406852 * 2 ^ 59
def prefixEnd_2406852 : Nat := 4983230072969 + 3 ^ 40 * 2406852 * 2
def baseEnd_2406852 : Nat := 5085892758170051087165

theorem tailTrace_2406852 : CollatzResearch.WordTrace tailWord_2406852 prefixEnd_2406852 5085892758170051087165 := by
  unfold tailWord_2406852
  simp only [CollatzResearch.WordTrace]
  refine ⟨43892552138196868220371405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58523402850929157627161873 43892552138196868220371405)
  ·
    refine ⟨16459707051823825582639277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43892552138196868220371405 16459707051823825582639277)
    ·
      refine ⟨6172390144433934593489729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16459707051823825582639277 6172390144433934593489729)
      ·
        refine ⟨4629292608325450945117297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6172390144433934593489729 4629292608325450945117297)
        ·
          refine ⟨3471969456244088208837973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4629292608325450945117297 3471969456244088208837973)
          ·
            refine ⟨5085892758170051087165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3471969456244088208837973 5085892758170051087165)
            ·
              rfl

theorem cell23_2406852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 11].length) (baseStart_2406852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406852 prefixEnd_2406852 := by exact prefixLift 2406852
  have htrace : WordTrace (prefixWord ++ tailWord_2406852) baseStart_2406852 baseEnd_2406852 := by
    simpa [prefixWord, tailWord_2406852, baseEnd_2406852] using wordTrace_append hprefix tailTrace_2406852
  have hstable : (prefixWord ++ tailWord_2406852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406852).length < 2 ^ (prefixWord ++ tailWord_2406852).sum := by decide
  have hdescent : baseEnd_2406852 < baseStart_2406852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406862 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_2406862 : Nat := 118140960795 + 2406862 * 2 ^ 59
def prefixEnd_2406862 : Nat := 4983230072969 + 3 ^ 40 * 2406862 * 2
def baseEnd_2406862 : Nat := 1235877075041867375056049

theorem tailTrace_2406862 : CollatzResearch.WordTrace tailWord_2406862 prefixEnd_2406862 1235877075041867375056049 := by
  unfold tailWord_2406862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10973183625794688518575855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58523646004238338765737893 10973183625794688518575855)
  ·
    refine ⟨16459775438692032777863783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10973183625794688518575855 16459775438692032777863783)
    ·
      refine ⟨24689663158038049166795675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16459775438692032777863783 24689663158038049166795675)
      ·
        refine ⟨37034494737057073750193513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24689663158038049166795675 37034494737057073750193513)
        ·
          refine ⟨27775871052792805312645135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37034494737057073750193513 27775871052792805312645135)
          ·
            refine ⟨41663806579189207968967703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27775871052792805312645135 41663806579189207968967703)
            ·
              refine ⟨62495709868783811953451555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41663806579189207968967703 62495709868783811953451555)
              ·
                refine ⟨93743564803175717930177333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62495709868783811953451555 93743564803175717930177333)
                ·
                  refine ⟨8788459200297723555954125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 93743564803175717930177333 8788459200297723555954125)
                  ·
                    refine ⟨3295672200111646333482797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8788459200297723555954125 3295672200111646333482797)
                    ·
                      refine ⟨1235877075041867375056049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3295672200111646333482797 1235877075041867375056049)
                      ·
                        rfl

theorem cell23_2406862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_2406862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406862 prefixEnd_2406862 := by exact prefixLift 2406862
  have htrace : WordTrace (prefixWord ++ tailWord_2406862) baseStart_2406862 baseEnd_2406862 := by
    simpa [prefixWord, tailWord_2406862, baseEnd_2406862] using wordTrace_append hprefix tailTrace_2406862
  have hstable : (prefixWord ++ tailWord_2406862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406862).length < 2 ^ (prefixWord ++ tailWord_2406862).sum := by decide
  have hdescent : baseEnd_2406862 < baseStart_2406862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406879 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 3]
def baseStart_2406879 : Nat := 118140960795 + 2406879 * 2 ^ 59
def prefixEnd_2406879 : Nat := 4983230072969 + 3 ^ 40 * 2406879 * 2
def baseEnd_2406879 : Nat := 1235885804212993808543471

theorem tailTrace_2406879 : CollatzResearch.WordTrace tailWord_2406879 prefixEnd_2406879 1235885804212993808543471 := by
  unfold tailWord_2406879
  simp only [CollatzResearch.WordTrace]
  refine ⟨87786089047295920051975691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58524059364863946701317127 87786089047295920051975691)
  ·
    refine ⟨131679133570943880077963537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87786089047295920051975691 131679133570943880077963537)
    ·
      refine ⟨98759350178207910058472653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131679133570943880077963537 98759350178207910058472653)
      ·
        refine ⟨37034756316827966271927245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98759350178207910058472653 37034756316827966271927245)
        ·
          refine ⟨13888033618810487351972717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37034756316827966271927245 13888033618810487351972717)
          ·
            refine ⟨5208012607053932756989769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13888033618810487351972717 5208012607053932756989769)
            ·
              refine ⟨3906009455290449567742327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5208012607053932756989769 3906009455290449567742327)
              ·
                refine ⟨5859014182935674351613491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906009455290449567742327 5859014182935674351613491)
                ·
                  refine ⟨8788521274403511527420237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5859014182935674351613491 8788521274403511527420237)
                  ·
                    refine ⟨3295695477901316822782589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8788521274403511527420237 3295695477901316822782589)
                    ·
                      refine ⟨1235885804212993808543471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3295695477901316822782589 1235885804212993808543471)
                      ·
                        rfl

theorem cell23_2406879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_2406879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406879 prefixEnd_2406879 := by exact prefixLift 2406879
  have htrace : WordTrace (prefixWord ++ tailWord_2406879) baseStart_2406879 baseEnd_2406879 := by
    simpa [prefixWord, tailWord_2406879, baseEnd_2406879] using wordTrace_append hprefix tailTrace_2406879
  have hstable : (prefixWord ++ tailWord_2406879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406879).length < 2 ^ (prefixWord ++ tailWord_2406879).sum := by decide
  have hdescent : baseEnd_2406879 < baseStart_2406879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406895 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 3, 8]
def baseStart_2406895 : Nat := 118140960795 + 2406895 * 2 ^ 59
def prefixEnd_2406895 : Nat := 4983230072969 + 3 ^ 40 * 2406895 * 2
def baseEnd_2406895 : Nat := 411964673301155248647799

theorem tailTrace_2406895 : CollatzResearch.WordTrace tailWord_2406895 prefixEnd_2406895 411964673301155248647799 := by
  unfold tailWord_2406895
  simp only [CollatzResearch.WordTrace]
  refine ⟨87786672615237954784558139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58524448410158636523038759 87786672615237954784558139)
  ·
    refine ⟨131680008922856932176837209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87786672615237954784558139 131680008922856932176837209)
    ·
      refine ⟨98760006692142699132627907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131680008922856932176837209 98760006692142699132627907)
      ·
        refine ⟨148140010038214048698941861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98760006692142699132627907 148140010038214048698941861)
        ·
          refine ⟨27776251882165134131051599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148140010038214048698941861 27776251882165134131051599)
          ·
            refine ⟨41664377823247701196577399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27776251882165134131051599 41664377823247701196577399)
            ·
              refine ⟨62496566734871551794866099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41664377823247701196577399 62496566734871551794866099)
              ·
                refine ⟨93744850102307327692299149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62496566734871551794866099 93744850102307327692299149)
                ·
                  refine ⟨35154318788365247884612181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93744850102307327692299149 35154318788365247884612181)
                  ·
                    refine ⟨411964673301155248647799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35154318788365247884612181 411964673301155248647799)
                    ·
                      rfl

theorem cell23_2406895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_2406895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406895 prefixEnd_2406895 := by exact prefixLift 2406895
  have htrace : WordTrace (prefixWord ++ tailWord_2406895) baseStart_2406895 baseEnd_2406895 := by
    simpa [prefixWord, tailWord_2406895, baseEnd_2406895] using wordTrace_append hprefix tailTrace_2406895
  have hstable : (prefixWord ++ tailWord_2406895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406895).length < 2 ^ (prefixWord ++ tailWord_2406895).sum := by decide
  have hdescent : baseEnd_2406895 < baseStart_2406895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406913 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_2406913 : Nat := 118140960795 + 2406913 * 2 ^ 59
def prefixEnd_2406913 : Nat := 4983230072969 + 3 ^ 40 * 2406913 * 2
def baseEnd_2406913 : Nat := 1235903262555246675518315

theorem tailTrace_2406913 : CollatzResearch.WordTrace tailWord_2406913 prefixEnd_2406913 1235903262555246675518315 := by
  unfold tailWord_2406913
  simp only [CollatzResearch.WordTrace]
  refine ⟨87787329129172743858713393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58524886086115162572475595 87787329129172743858713393)
  ·
    refine ⟨65840496846879557894035045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87787329129172743858713393 65840496846879557894035045)
    ·
      refine ⟨12345093158789917105131571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65840496846879557894035045 12345093158789917105131571)
      ·
        refine ⟨18517639738184875657697357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12345093158789917105131571 18517639738184875657697357)
        ·
          refine ⟨6944114901819328371636509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18517639738184875657697357 6944114901819328371636509)
          ·
            refine ⟨2604043088182248139363691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6944114901819328371636509 2604043088182248139363691)
            ·
              refine ⟨3906064632273372209045537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2604043088182248139363691 3906064632273372209045537)
              ·
                refine ⟨2929548474205029156784153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3906064632273372209045537 2929548474205029156784153)
                ·
                  refine ⟨2197161355653771867588115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2929548474205029156784153 2197161355653771867588115)
                  ·
                    refine ⟨3295742033480657801382173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2197161355653771867588115 3295742033480657801382173)
                    ·
                      refine ⟨1235903262555246675518315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3295742033480657801382173 1235903262555246675518315)
                      ·
                        rfl

theorem cell23_2406913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_2406913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406913 prefixEnd_2406913 := by exact prefixLift 2406913
  have htrace : WordTrace (prefixWord ++ tailWord_2406913) baseStart_2406913 baseEnd_2406913 := by
    simpa [prefixWord, tailWord_2406913, baseEnd_2406913] using wordTrace_append hprefix tailTrace_2406913
  have hstable : (prefixWord ++ tailWord_2406913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406913).length < 2 ^ (prefixWord ++ tailWord_2406913).sum := by decide
  have hdescent : baseEnd_2406913 < baseStart_2406913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406936 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 1, 4, 2]
def baseStart_2406936 : Nat := 118140960795 + 2406936 * 2 ^ 59
def prefixEnd_2406936 : Nat := 4983230072969 + 3 ^ 40 * 2406936 * 2
def baseEnd_2406936 : Nat := 1235915072610300085530709

theorem tailTrace_2406936 : CollatzResearch.WordTrace tailWord_2406936 prefixEnd_2406936 1235915072610300085530709 := by
  unfold tailWord_2406936
  simp only [CollatzResearch.WordTrace]
  refine ⟨43894084004044709393400331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58525445338726279191200441 43894084004044709393400331)
  ·
    refine ⟨65841126006067064090100497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43894084004044709393400331 65841126006067064090100497)
    ·
      refine ⟨49380844504550298067575373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65841126006067064090100497 49380844504550298067575373)
      ·
        refine ⟨18517816689206361775340765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49380844504550298067575373 18517816689206361775340765)
        ·
          refine ⟨6944181258452385665752787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18517816689206361775340765 6944181258452385665752787)
          ·
            refine ⟨10416271887678578498629181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6944181258452385665752787 10416271887678578498629181)
            ·
              refine ⟨3906101957879466936985943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10416271887678578498629181 3906101957879466936985943)
              ·
                refine ⟨5859152936819200405478915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906101957879466936985943 5859152936819200405478915)
                ·
                  refine ⟨8788729405228800608218373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5859152936819200405478915 8788729405228800608218373)
                  ·
                    refine ⟨1647886763480400114040945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8788729405228800608218373 1647886763480400114040945)
                    ·
                      refine ⟨1235915072610300085530709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1647886763480400114040945 1235915072610300085530709)
                      ·
                        rfl

theorem cell23_2406936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_2406936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406936 prefixEnd_2406936 := by exact prefixLift 2406936
  have htrace : WordTrace (prefixWord ++ tailWord_2406936) baseStart_2406936 baseEnd_2406936 := by
    simpa [prefixWord, tailWord_2406936, baseEnd_2406936] using wordTrace_append hprefix tailTrace_2406936
  have hstable : (prefixWord ++ tailWord_2406936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406936).length < 2 ^ (prefixWord ++ tailWord_2406936).sum := by decide
  have hdescent : baseEnd_2406936 < baseStart_2406936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2406992 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 4]
def baseStart_2406992 : Nat := 118140960795 + 2406992 * 2 ^ 59
def prefixEnd_2406992 : Nat := 4983230072969 + 3 ^ 40 * 2406992 * 2
def baseEnd_2406992 : Nat := 1235943827526951866430451

theorem tailTrace_2406992 : CollatzResearch.WordTrace tailWord_2406992 prefixEnd_2406992 1235943827526951866430451 := by
  unfold tailWord_2406992
  simp only [CollatzResearch.WordTrace]
  refine ⟨43895105247943270175419615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58526806997257693567226153 43895105247943270175419615)
  ·
    refine ⟨65842657871914905263129423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43895105247943270175419615 65842657871914905263129423)
    ·
      refine ⟨98763986807872357894694135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65842657871914905263129423 98763986807872357894694135)
      ·
        refine ⟨148145980211808536842041203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98763986807872357894694135 148145980211808536842041203)
        ·
          refine ⟨222218970317712805263061805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148145980211808536842041203 222218970317712805263061805)
          ·
            refine ⟨83332113869142301973648177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222218970317712805263061805 83332113869142301973648177)
            ·
              refine ⟨62499085401856726480236133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83332113869142301973648177 62499085401856726480236133)
              ·
                refine ⟨11718578512848136215044275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62499085401856726480236133 11718578512848136215044275)
                ·
                  refine ⟨17577867769272204322566413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11718578512848136215044275 17577867769272204322566413)
                  ·
                    refine ⟨6591700413477076620962405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17577867769272204322566413 6591700413477076620962405)
                    ·
                      refine ⟨1235943827526951866430451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6591700413477076620962405 1235943827526951866430451)
                      ·
                        rfl

theorem cell23_2406992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_2406992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2406992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2406992 prefixEnd_2406992 := by exact prefixLift 2406992
  have htrace : WordTrace (prefixWord ++ tailWord_2406992) baseStart_2406992 baseEnd_2406992 := by
    simpa [prefixWord, tailWord_2406992, baseEnd_2406992] using wordTrace_append hprefix tailTrace_2406992
  have hstable : (prefixWord ++ tailWord_2406992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2406992).length < 2 ^ (prefixWord ++ tailWord_2406992).sum := by decide
  have hdescent : baseEnd_2406992 < baseStart_2406992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2406992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407009 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_2407009 : Nat := 118140960795 + 2407009 * 2 ^ 59
def prefixEnd_2407009 : Nat := 4983230072969 + 3 ^ 40 * 2407009 * 2
def baseEnd_2407009 : Nat := 1235952556698078299917873

theorem tailTrace_2407009 : CollatzResearch.WordTrace tailWord_2407009 prefixEnd_2407009 1235952556698078299917873 := by
  unfold tailWord_2407009
  simp only [CollatzResearch.WordTrace]
  refine ⟨87790830536824952254208081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58527220357883301502805387 87790830536824952254208081)
  ·
    refine ⟨65843122902618714190656061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87790830536824952254208081 65843122902618714190656061)
    ·
      refine ⟨24691171088482017821496023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65843122902618714190656061 24691171088482017821496023)
      ·
        refine ⟨37036756632723026732244035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24691171088482017821496023 37036756632723026732244035)
        ·
          refine ⟨55555134949084540098366053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37036756632723026732244035 55555134949084540098366053)
          ·
            refine ⟨10416587802953351268443635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55555134949084540098366053 10416587802953351268443635)
            ·
              refine ⟨15624881704430026902665453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10416587802953351268443635 15624881704430026902665453)
              ·
                refine ⟨5859330639161260088499545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15624881704430026902665453 5859330639161260088499545)
                ·
                  refine ⟨4394497979370945066374659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5859330639161260088499545 4394497979370945066374659)
                  ·
                    refine ⟨6591746969056417599561989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4394497979370945066374659 6591746969056417599561989)
                    ·
                      refine ⟨1235952556698078299917873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6591746969056417599561989 1235952556698078299917873)
                      ·
                        rfl

theorem cell23_2407009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_2407009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407009 prefixEnd_2407009 := by exact prefixLift 2407009
  have htrace : WordTrace (prefixWord ++ tailWord_2407009) baseStart_2407009 baseEnd_2407009 := by
    simpa [prefixWord, tailWord_2407009, baseEnd_2407009] using wordTrace_append hprefix tailTrace_2407009
  have hstable : (prefixWord ++ tailWord_2407009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407009).length < 2 ^ (prefixWord ++ tailWord_2407009).sum := by decide
  have hdescent : baseEnd_2407009 < baseStart_2407009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407052 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_2407052 : Nat := 118140960795 + 2407052 * 2 ^ 59
def prefixEnd_2407052 : Nat := 4983230072969 + 3 ^ 40 * 2407052 * 2
def baseEnd_2407052 : Nat := 1235974636366221631680175

theorem tailTrace_2407052 : CollatzResearch.WordTrace tailWord_2407052 prefixEnd_2407052 1235974636366221631680175 := by
  unfold tailWord_2407052
  simp only [CollatzResearch.WordTrace]
  refine ⟨43896199437834585299011705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58528265917112780398682273 43896199437834585299011705)
  ·
    refine ⟨32922149578375938974258779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43896199437834585299011705 32922149578375938974258779)
    ·
      refine ⟨49383224367563908461388169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32922149578375938974258779 49383224367563908461388169)
      ·
        refine ⟨37037418275672931346041127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49383224367563908461388169 37037418275672931346041127)
        ·
          refine ⟨55556127413509397019061691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37037418275672931346041127 55556127413509397019061691)
          ·
            refine ⟨83334191120264095528592537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55556127413509397019061691 83334191120264095528592537)
            ·
              refine ⟨62500643340198071646444403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83334191120264095528592537 62500643340198071646444403)
              ·
                refine ⟨93750965010297107469666605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62500643340198071646444403 93750965010297107469666605)
                ·
                  refine ⟨35156611878861415301124977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93750965010297107469666605 35156611878861415301124977)
                  ·
                    refine ⟨26367458909146061475843733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35156611878861415301124977 26367458909146061475843733)
                    ·
                      refine ⟨1235974636366221631680175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26367458909146061475843733 1235974636366221631680175)
                      ·
                        rfl

theorem cell23_2407052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_2407052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407052 prefixEnd_2407052 := by exact prefixLift 2407052
  have htrace : WordTrace (prefixWord ++ tailWord_2407052) baseStart_2407052 baseEnd_2407052 := by
    simpa [prefixWord, tailWord_2407052, baseEnd_2407052] using wordTrace_append hprefix tailTrace_2407052
  have hstable : (prefixWord ++ tailWord_2407052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407052).length < 2 ^ (prefixWord ++ tailWord_2407052).sum := by decide
  have hdescent : baseEnd_2407052 < baseStart_2407052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407070 : List Nat := [4, 3, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_2407070 : Nat := 118140960795 + 2407070 * 2 ^ 59
def prefixEnd_2407070 : Nat := 4983230072969 + 3 ^ 40 * 2407070 * 2
def baseEnd_2407070 : Nat := 411994626339334187085031

theorem tailTrace_2407070 : CollatzResearch.WordTrace tailWord_2407070 prefixEnd_2407070 411994626339334187085031 := by
  unfold tailWord_2407070
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974131923700494959022333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58528703593069306448119109 10974131923700494959022333)
  ·
    refine ⟨4115299471387685609633375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10974131923700494959022333 4115299471387685609633375)
    ·
      refine ⟨6172949207081528414450063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4115299471387685609633375 6172949207081528414450063)
      ·
        refine ⟨9259423810622292621675095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6172949207081528414450063 9259423810622292621675095)
        ·
          refine ⟨13889135715933438932512643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9259423810622292621675095 13889135715933438932512643)
          ·
            refine ⟨20833703573900158398768965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13889135715933438932512643 20833703573900158398768965)
            ·
              refine ⟨3906319420106279699769181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20833703573900158398768965 3906319420106279699769181)
              ·
                refine ⟨1464869782539854887413443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3906319420106279699769181 1464869782539854887413443)
                ·
                  refine ⟨2197304673809782331120165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464869782539854887413443 2197304673809782331120165)
                  ·
                    refine ⟨411994626339334187085031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2197304673809782331120165 411994626339334187085031)
                    ·
                      rfl

theorem cell23_2407070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_2407070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407070 prefixEnd_2407070 := by exact prefixLift 2407070
  have htrace : WordTrace (prefixWord ++ tailWord_2407070) baseStart_2407070 baseEnd_2407070 := by
    simpa [prefixWord, tailWord_2407070, baseEnd_2407070] using wordTrace_append hprefix tailTrace_2407070
  have hstable : (prefixWord ++ tailWord_2407070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407070).length < 2 ^ (prefixWord ++ tailWord_2407070).sum := by decide
  have hdescent : baseEnd_2407070 < baseStart_2407070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407076 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_2407076 : Nat := 118140960795 + 2407076 * 2 ^ 59
def prefixEnd_2407076 : Nat := 4983230072969 + 3 ^ 40 * 2407076 * 2
def baseEnd_2407076 : Nat := 1235986959901929537780065

theorem tailTrace_2407076 : CollatzResearch.WordTrace tailWord_2407076 prefixEnd_2407076 1235986959901929537780065 := by
  unfold tailWord_2407076
  simp only [CollatzResearch.WordTrace]
  refine ⟨43896637113791111348448541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58528849485054815131264721 43896637113791111348448541)
  ·
    refine ⟨16461238917671666755668203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43896637113791111348448541 16461238917671666755668203)
    ·
      refine ⟨24691858376507500133502305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16461238917671666755668203 24691858376507500133502305)
      ·
        refine ⟨18518893782380625100126729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24691858376507500133502305 18518893782380625100126729)
        ·
          refine ⟨13889170336785468825095047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18518893782380625100126729 13889170336785468825095047)
          ·
            refine ⟨20833755505178203237642571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13889170336785468825095047 20833755505178203237642571)
            ·
              refine ⟨31250633257767304856463857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20833755505178203237642571 31250633257767304856463857)
              ·
                refine ⟨23437974943325478642347893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31250633257767304856463857 23437974943325478642347893)
                ·
                  refine ⟨2197310150936763622720115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23437974943325478642347893 2197310150936763622720115)
                  ·
                    refine ⟨3295965226405145434080173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2197310150936763622720115 3295965226405145434080173)
                    ·
                      refine ⟨1235986959901929537780065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3295965226405145434080173 1235986959901929537780065)
                      ·
                        rfl

theorem cell23_2407076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_2407076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407076 prefixEnd_2407076 := by exact prefixLift 2407076
  have htrace : WordTrace (prefixWord ++ tailWord_2407076) baseStart_2407076 baseEnd_2407076 := by
    simpa [prefixWord, tailWord_2407076, baseEnd_2407076] using wordTrace_append hprefix tailTrace_2407076
  have hstable : (prefixWord ++ tailWord_2407076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407076).length < 2 ^ (prefixWord ++ tailWord_2407076).sum := by decide
  have hdescent : baseEnd_2407076 < baseStart_2407076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407086 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2407086 : Nat := 118140960795 + 2407086 * 2 ^ 59
def prefixEnd_2407086 : Nat := 4983230072969 + 3 ^ 40 * 2407086 * 2
def baseEnd_2407086 : Nat := 1235992094708474498655019

theorem tailTrace_2407086 : CollatzResearch.WordTrace tailWord_2407086 prefixEnd_2407086 1235992094708474498655019 := by
  unfold tailWord_2407086
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974204869693249300595139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58529092638363996269840741 10974204869693249300595139)
  ·
    refine ⟨16461307304539873950892709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10974204869693249300595139 16461307304539873950892709)
    ·
      refine ⟨3086495119601226365792383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16461307304539873950892709 3086495119601226365792383)
      ·
        refine ⟨4629742679401839548688575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3086495119601226365792383 4629742679401839548688575)
        ·
          refine ⟨6944614019102759323032863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4629742679401839548688575 6944614019102759323032863)
          ·
            refine ⟨10416921028654138984549295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6944614019102759323032863 10416921028654138984549295)
            ·
              refine ⟨15625381542981208476823943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10416921028654138984549295 15625381542981208476823943)
              ·
                refine ⟨23438072314471812715235915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15625381542981208476823943 23438072314471812715235915)
                ·
                  refine ⟨35157108471707719072853873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23438072314471812715235915 35157108471707719072853873)
                  ·
                    refine ⟨26367831353780789304640405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35157108471707719072853873 26367831353780789304640405)
                    ·
                      refine ⟨1235992094708474498655019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26367831353780789304640405 1235992094708474498655019)
                      ·
                        rfl

theorem cell23_2407086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2407086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407086 prefixEnd_2407086 := by exact prefixLift 2407086
  have htrace : WordTrace (prefixWord ++ tailWord_2407086) baseStart_2407086 baseEnd_2407086 := by
    simpa [prefixWord, tailWord_2407086, baseEnd_2407086] using wordTrace_append hprefix tailTrace_2407086
  have hstable : (prefixWord ++ tailWord_2407086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407086).length < 2 ^ (prefixWord ++ tailWord_2407086).sum := by decide
  have hdescent : baseEnd_2407086 < baseStart_2407086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407093 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2407093 : Nat := 118140960795 + 2407093 * 2 ^ 59
def prefixEnd_2407093 : Nat := 4983230072969 + 3 ^ 40 * 2407093 * 2
def baseEnd_2407093 : Nat := 1235995689073055971267487

theorem tailTrace_2407093 : CollatzResearch.WordTrace tailWord_2407093 prefixEnd_2407093 1235995689073055971267487 := by
  unfold tailWord_2407093
  simp only [CollatzResearch.WordTrace]
  refine ⟨87793894268520634600265933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58529262845680423066843955 87793894268520634600265933)
  ·
    refine ⟨32922710350695237975099725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87793894268520634600265933 32922710350695237975099725)
    ·
      refine ⟨12346016381510714240662397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32922710350695237975099725 12346016381510714240662397)
      ·
        refine ⟨4629756143066517840248399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12346016381510714240662397 4629756143066517840248399)
        ·
          refine ⟨6944634214599776760372599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4629756143066517840248399 6944634214599776760372599)
          ·
            refine ⟨10416951321899665140558899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6944634214599776760372599 10416951321899665140558899)
            ·
              refine ⟨15625426982849497710838349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10416951321899665140558899 15625426982849497710838349)
              ·
                refine ⟨5859535118568561641564381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15625426982849497710838349 5859535118568561641564381)
                ·
                  refine ⟨2197325669463210615586643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5859535118568561641564381 2197325669463210615586643)
                  ·
                    refine ⟨3295988504194815923379965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2197325669463210615586643 3295988504194815923379965)
                    ·
                      refine ⟨1235995689073055971267487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3295988504194815923379965 1235995689073055971267487)
                      ·
                        rfl

theorem cell23_2407093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2407093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407093 prefixEnd_2407093 := by exact prefixLift 2407093
  have htrace : WordTrace (prefixWord ++ tailWord_2407093) baseStart_2407093 baseEnd_2407093 := by
    simpa [prefixWord, tailWord_2407093, baseEnd_2407093] using wordTrace_append hprefix tailTrace_2407093
  have hstable : (prefixWord ++ tailWord_2407093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407093).length < 2 ^ (prefixWord ++ tailWord_2407093).sum := by decide
  have hdescent : baseEnd_2407093 < baseStart_2407093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407109 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 8, 4]
def baseStart_2407109 : Nat := 118140960795 + 2407109 * 2 ^ 59
def prefixEnd_2407109 : Nat := 4983230072969 + 3 ^ 40 * 2407109 * 2
def baseEnd_2407109 : Nat := 412001301587842636222471

theorem tailTrace_2407109 : CollatzResearch.WordTrace tailWord_2407109 prefixEnd_2407109 412001301587842636222471 := by
  unfold tailWord_2407109
  simp only [CollatzResearch.WordTrace]
  refine ⟨87794477836462669332848381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58529651890975112888565587 87794477836462669332848381)
  ·
    refine ⟨32922929188673500999818143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87794477836462669332848381 32922929188673500999818143)
    ·
      refine ⟨49384393783010251499727215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32922929188673500999818143 49384393783010251499727215)
      ·
        refine ⟨74076590674515377249590823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49384393783010251499727215 74076590674515377249590823)
        ·
          refine ⟨111114886011773065874386235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74076590674515377249590823 111114886011773065874386235)
          ·
            refine ⟨166672329017659598811579353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111114886011773065874386235 166672329017659598811579353)
            ·
              refine ⟨125004246763244699108684515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166672329017659598811579353 125004246763244699108684515)
              ·
                refine ⟨187506370144867048663026773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125004246763244699108684515 187506370144867048663026773)
                ·
                  refine ⟨2197340275135160726519845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 187506370144867048663026773 2197340275135160726519845)
                  ·
                    refine ⟨412001301587842636222471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2197340275135160726519845 412001301587842636222471)
                    ·
                      rfl

theorem cell23_2407109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 4].length) (baseStart_2407109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407109 prefixEnd_2407109 := by exact prefixLift 2407109
  have htrace : WordTrace (prefixWord ++ tailWord_2407109) baseStart_2407109 baseEnd_2407109 := by
    simpa [prefixWord, tailWord_2407109, baseEnd_2407109] using wordTrace_append hprefix tailTrace_2407109
  have hstable : (prefixWord ++ tailWord_2407109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407109).length < 2 ^ (prefixWord ++ tailWord_2407109).sum := by decide
  have hdescent : baseEnd_2407109 < baseStart_2407109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407129 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 4]
def baseStart_2407129 : Nat := 118140960795 + 2407129 * 2 ^ 59
def prefixEnd_2407129 : Nat := 4983230072969 + 3 ^ 40 * 2407129 * 2
def baseEnd_2407129 : Nat := 1236014174376617830417321

theorem tailTrace_2407129 : CollatzResearch.WordTrace tailWord_2407129 prefixEnd_2407129 1236014174376617830417321 := by
  unfold tailWord_2407129
  simp only [CollatzResearch.WordTrace]
  refine ⟨87795207296390212748576441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58530138197593475165717627 87795207296390212748576441)
  ·
    refine ⟨65846405472292659561432331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87795207296390212748576441 65846405472292659561432331)
    ·
      refine ⟨98769608208438989342148497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65846405472292659561432331 98769608208438989342148497)
      ·
        refine ⟨74077206156329242006611373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98769608208438989342148497 74077206156329242006611373)
        ·
          refine ⟨27778952308623465752479265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74077206156329242006611373 27778952308623465752479265)
          ·
            refine ⟨20834214231467599314359449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27778952308623465752479265 20834214231467599314359449)
            ·
              refine ⟨15625660673600699485769587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20834214231467599314359449 15625660673600699485769587)
              ·
                refine ⟨23438491010401049228654381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15625660673600699485769587 23438491010401049228654381)
                ·
                  refine ⟨8789434128900393460745393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23438491010401049228654381 8789434128900393460745393)
                  ·
                    refine ⟨6592075596675295095559045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8789434128900393460745393 6592075596675295095559045)
                    ·
                      refine ⟨1236014174376617830417321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6592075596675295095559045 1236014174376617830417321)
                      ·
                        rfl

theorem cell23_2407129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_2407129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407129 prefixEnd_2407129 := by exact prefixLift 2407129
  have htrace : WordTrace (prefixWord ++ tailWord_2407129) baseStart_2407129 baseEnd_2407129 := by
    simpa [prefixWord, tailWord_2407129, baseEnd_2407129] using wordTrace_append hprefix tailTrace_2407129
  have hstable : (prefixWord ++ tailWord_2407129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407129).length < 2 ^ (prefixWord ++ tailWord_2407129).sum := by decide
  have hdescent : baseEnd_2407129 < baseStart_2407129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407139 : List Nat := [1, 1, 1, 7, 1, 1, 11]
def baseStart_2407139 : Nat := 118140960795 + 2407139 * 2 ^ 59
def prefixEnd_2407139 : Nat := 4983230072969 + 3 ^ 40 * 2407139 * 2
def baseEnd_2407139 : Nat := 15259497644236577670275

theorem tailTrace_2407139 : CollatzResearch.WordTrace tailWord_2407139 prefixEnd_2407139 15259497644236577670275 := by
  unfold tailWord_2407139
  simp only [CollatzResearch.WordTrace]
  refine ⟨87795572026353984456440471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58530381350902656304293647 87795572026353984456440471)
  ·
    refine ⟨131693358039530976684660707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87795572026353984456440471 131693358039530976684660707)
    ·
      refine ⟨197540037059296465026991061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131693358039530976684660707 197540037059296465026991061)
      ·
        refine ⟨4629844618577260899070103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 197540037059296465026991061 4629844618577260899070103)
        ·
          refine ⟨6944766927865891348605155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4629844618577260899070103 6944766927865891348605155)
          ·
            refine ⟨10417150391798837022907733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6944766927865891348605155 10417150391798837022907733)
            ·
              refine ⟨15259497644236577670275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10417150391798837022907733 15259497644236577670275)
              ·
                rfl

theorem cell23_2407139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 11].length) (baseStart_2407139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407139 prefixEnd_2407139 := by exact prefixLift 2407139
  have htrace : WordTrace (prefixWord ++ tailWord_2407139) baseStart_2407139 baseEnd_2407139 := by
    simpa [prefixWord, tailWord_2407139, baseEnd_2407139] using wordTrace_append hprefix tailTrace_2407139
  have hstable : (prefixWord ++ tailWord_2407139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407139).length < 2 ^ (prefixWord ++ tailWord_2407139).sum := by decide
  have hdescent : baseEnd_2407139 < baseStart_2407139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407150 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_2407150 : Nat := 118140960795 + 2407150 * 2 ^ 59
def prefixEnd_2407150 : Nat := 4983230072969 + 3 ^ 40 * 2407150 * 2
def baseEnd_2407150 : Nat := 1236024957470362248254725

theorem tailTrace_2407150 : CollatzResearch.WordTrace tailWord_2407150 prefixEnd_2407150 1236024957470362248254725 := by
  unfold tailWord_2407150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974496653664266666886363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58530648819542755556727269 10974496653664266666886363)
  ·
    refine ⟨16461744980496400000329545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10974496653664266666886363 16461744980496400000329545)
    ·
      refine ⟨12346308735372300000247159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16461744980496400000329545 12346308735372300000247159)
      ·
        refine ⟨18519463103058450000370739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12346308735372300000247159 18519463103058450000370739)
        ·
          refine ⟨27779194654587675000556109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18519463103058450000370739 27779194654587675000556109)
          ·
            refine ⟨10417197995470378125208541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27779194654587675000556109 10417197995470378125208541)
            ·
              refine ⟨3906449248301391796953203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10417197995470378125208541 3906449248301391796953203)
              ·
                refine ⟨5859673872452087695429805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906449248301391796953203 5859673872452087695429805)
                ·
                  refine ⟨2197377702169532885786177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5859673872452087695429805 2197377702169532885786177)
                  ·
                    refine ⟨1648033276627149664339633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2197377702169532885786177 1648033276627149664339633)
                    ·
                      refine ⟨1236024957470362248254725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648033276627149664339633 1236024957470362248254725)
                      ·
                        rfl

theorem cell23_2407150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_2407150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407150 prefixEnd_2407150 := by exact prefixLift 2407150
  have htrace : WordTrace (prefixWord ++ tailWord_2407150) baseStart_2407150 baseEnd_2407150 := by
    simpa [prefixWord, tailWord_2407150, baseEnd_2407150] using wordTrace_append hprefix tailTrace_2407150
  have hstable : (prefixWord ++ tailWord_2407150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407150).length < 2 ^ (prefixWord ++ tailWord_2407150).sum := by decide
  have hdescent : baseEnd_2407150 < baseStart_2407150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407170 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_2407170 : Nat := 118140960795 + 2407170 * 2 ^ 59
def prefixEnd_2407170 : Nat := 4983230072969 + 3 ^ 40 * 2407170 * 2
def baseEnd_2407170 : Nat := 1236035227083452170004633

theorem tailTrace_2407170 : CollatzResearch.WordTrace tailWord_2407170 prefixEnd_2407170 1236035227083452170004633 := by
  unfold tailWord_2407170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21949175672310419187704741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58531135126161117833879309 21949175672310419187704741)
  ·
    refine ⟨4115470438558203597694639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21949175672310419187704741 4115470438558203597694639)
    ·
      refine ⟨6173205657837305396541959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4115470438558203597694639 6173205657837305396541959)
      ·
        refine ⟨9259808486755958094812939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6173205657837305396541959 9259808486755958094812939)
        ·
          refine ⟨13889712730133937142219409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9259808486755958094812939 13889712730133937142219409)
          ·
            refine ⟨10417284547600452856664557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13889712730133937142219409 10417284547600452856664557)
            ·
              refine ⟨3906481705350169821249209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10417284547600452856664557 3906481705350169821249209)
              ·
                refine ⟨2929861279012627365936907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3906481705350169821249209 2929861279012627365936907)
                ·
                  refine ⟨4394791918518941048905361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2929861279012627365936907 4394791918518941048905361)
                  ·
                    refine ⟨3296093938889205786679021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4394791918518941048905361 3296093938889205786679021)
                    ·
                      refine ⟨1236035227083452170004633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3296093938889205786679021 1236035227083452170004633)
                      ·
                        rfl

theorem cell23_2407170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_2407170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407170 prefixEnd_2407170 := by exact prefixLift 2407170
  have htrace : WordTrace (prefixWord ++ tailWord_2407170) baseStart_2407170 baseEnd_2407170 := by
    simpa [prefixWord, tailWord_2407170, baseEnd_2407170] using wordTrace_append hprefix tailTrace_2407170
  have hstable : (prefixWord ++ tailWord_2407170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407170).length < 2 ^ (prefixWord ++ tailWord_2407170).sum := by decide
  have hdescent : baseEnd_2407170 < baseStart_2407170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407200 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2407200 : Nat := 118140960795 + 2407200 * 2 ^ 59
def prefixEnd_2407200 : Nat := 4983230072969 + 3 ^ 40 * 2407200 * 2
def baseEnd_2407200 : Nat := 1236050631503087052629495

theorem tailTrace_2407200 : CollatzResearch.WordTrace tailWord_2407200 prefixEnd_2407200 1236050631503087052629495 := by
  unfold tailWord_2407200
  simp only [CollatzResearch.WordTrace]
  refine ⟨43898898439566495937205527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58531864586088661249607369 43898898439566495937205527)
  ·
    refine ⟨65848347659349743905808291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43898898439566495937205527 65848347659349743905808291)
    ·
      refine ⟨98772521489024615858712437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65848347659349743905808291 98772521489024615858712437)
      ·
        refine ⟨9259923889596057736754291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98772521489024615858712437 9259923889596057736754291)
        ·
          refine ⟨13889885834394086605131437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9259923889596057736754291 13889885834394086605131437)
          ·
            refine ⟨5208707187897782476924289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13889885834394086605131437 5208707187897782476924289)
            ·
              refine ⟨3906530390923336857693217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5208707187897782476924289 3906530390923336857693217)
              ·
                refine ⟨2929897793192502643269913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3906530390923336857693217 2929897793192502643269913)
                ·
                  refine ⟨2197423344894376982452435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2929897793192502643269913 2197423344894376982452435)
                  ·
                    refine ⟨3296135017341565473678653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2197423344894376982452435 3296135017341565473678653)
                    ·
                      refine ⟨1236050631503087052629495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3296135017341565473678653 1236050631503087052629495)
                      ·
                        rfl

theorem cell23_2407200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2407200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407200 prefixEnd_2407200 := by exact prefixLift 2407200
  have htrace : WordTrace (prefixWord ++ tailWord_2407200) baseStart_2407200 baseEnd_2407200 := by
    simpa [prefixWord, tailWord_2407200, baseEnd_2407200] using wordTrace_append hprefix tailTrace_2407200
  have hstable : (prefixWord ++ tailWord_2407200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407200).length < 2 ^ (prefixWord ++ tailWord_2407200).sum := by decide
  have hdescent : baseEnd_2407200 < baseStart_2407200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407223 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 1, 4, 2]
def baseStart_2407223 : Nat := 118140960795 + 2407223 * 2 ^ 59
def prefixEnd_2407223 : Nat := 4983230072969 + 3 ^ 40 * 2407223 * 2
def baseEnd_2407223 : Nat := 1236062441558140462641889

theorem tailTrace_2407223 : CollatzResearch.WordTrace tailWord_2407223 prefixEnd_2407223 1236062441558140462641889 := by
  unfold tailWord_2407223
  simp only [CollatzResearch.WordTrace]
  refine ⟨87798635758049666802498323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58532423838699777868332215 87798635758049666802498323)
  ·
    refine ⟨131697953637074500203747485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87798635758049666802498323 131697953637074500203747485)
    ·
      refine ⟨49386732613902937576405307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131697953637074500203747485 49386732613902937576405307)
      ·
        refine ⟨74080098920854406364607961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49386732613902937576405307 74080098920854406364607961)
        ·
          refine ⟨55560074190640804773455971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74080098920854406364607961 55560074190640804773455971)
          ·
            refine ⟨83340111285961207160183957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55560074190640804773455971 83340111285961207160183957)
            ·
              refine ⟨3906567716529431585633623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83340111285961207160183957 3906567716529431585633623)
              ·
                refine ⟨5859851574794147378450435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906567716529431585633623 5859851574794147378450435)
                ·
                  refine ⟨8789777362191221067675653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5859851574794147378450435 8789777362191221067675653)
                  ·
                    refine ⟨1648083255410853950189185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8789777362191221067675653 1648083255410853950189185)
                    ·
                      refine ⟨1236062441558140462641889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648083255410853950189185 1236062441558140462641889)
                      ·
                        rfl

theorem cell23_2407223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 4, 2].length) (baseStart_2407223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407223 prefixEnd_2407223 := by exact prefixLift 2407223
  have htrace : WordTrace (prefixWord ++ tailWord_2407223) baseStart_2407223 baseEnd_2407223 := by
    simpa [prefixWord, tailWord_2407223, baseEnd_2407223] using wordTrace_append hprefix tailTrace_2407223
  have hstable : (prefixWord ++ tailWord_2407223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407223).length < 2 ^ (prefixWord ++ tailWord_2407223).sum := by decide
  have hdescent : baseEnd_2407223 < baseStart_2407223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407239 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_2407239 : Nat := 118140960795 + 2407239 * 2 ^ 59
def prefixEnd_2407239 : Nat := 4983230072969 + 3 ^ 40 * 2407239 * 2
def baseEnd_2407239 : Nat := 1236070657248612400041815

theorem tailTrace_2407239 : CollatzResearch.WordTrace tailWord_2407239 prefixEnd_2407239 1236070657248612400041815 := by
  unfold tailWord_2407239
  simp only [CollatzResearch.WordTrace]
  refine ⟨87799219325991701535080771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58532812883994467690053847 87799219325991701535080771)
  ·
    refine ⟨131698828988987552302621157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87799219325991701535080771 131698828988987552302621157)
    ·
      refine ⟨24693530435435166056741467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131698828988987552302621157 24693530435435166056741467)
      ·
        refine ⟨37040295653152749085112201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24693530435435166056741467 37040295653152749085112201)
        ·
          refine ⟨27780221739864561813834151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37040295653152749085112201 27780221739864561813834151)
          ·
            refine ⟨41670332609796842720751227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27780221739864561813834151 41670332609796842720751227)
            ·
              refine ⟨62505498914695264081126841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41670332609796842720751227 62505498914695264081126841)
              ·
                refine ⟨46879124186021448060845131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62505498914695264081126841 46879124186021448060845131)
                ·
                  refine ⟨70318686279032172091267697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46879124186021448060845131 70318686279032172091267697)
                  ·
                    refine ⟨52739014709274129068450773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70318686279032172091267697 52739014709274129068450773)
                    ·
                      refine ⟨1236070657248612400041815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52739014709274129068450773 1236070657248612400041815)
                      ·
                        rfl

theorem cell23_2407239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_2407239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407239 prefixEnd_2407239 := by exact prefixLift 2407239
  have htrace : WordTrace (prefixWord ++ tailWord_2407239) baseStart_2407239 baseEnd_2407239 := by
    simpa [prefixWord, tailWord_2407239, baseEnd_2407239] using wordTrace_append hprefix tailTrace_2407239
  have hstable : (prefixWord ++ tailWord_2407239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407239).length < 2 ^ (prefixWord ++ tailWord_2407239).sum := by decide
  have hdescent : baseEnd_2407239 < baseStart_2407239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407257 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 2, 2, 2]
def baseStart_2407257 : Nat := 118140960795 + 2407257 * 2 ^ 59
def prefixEnd_2407257 : Nat := 4983230072969 + 3 ^ 40 * 2407257 * 2
def baseEnd_2407257 : Nat := 1236079899900393329616733

theorem tailTrace_2407257 : CollatzResearch.WordTrace tailWord_2407257 prefixEnd_2407257 1236079899900393329616733 := by
  unfold tailWord_2407257
  simp only [CollatzResearch.WordTrace]
  refine ⟨87799875839926490609236025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58533250559950993739490683 87799875839926490609236025)
  ·
    refine ⟨65849906879944867956927019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87799875839926490609236025 65849906879944867956927019)
    ·
      refine ⟨98774860319917301935390529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65849906879944867956927019 98774860319917301935390529)
      ·
        refine ⟨74081145239937976451542897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98774860319917301935390529 74081145239937976451542897)
        ·
          refine ⟨55560858929953482338657173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74081145239937976451542897 55560858929953482338657173)
          ·
            refine ⟨2604415262341569484624555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55560858929953482338657173 2604415262341569484624555)
            ·
              refine ⟨3906622893512354226936833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2604415262341569484624555 3906622893512354226936833)
              ·
                refine ⟨2929967170134265670202625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3906622893512354226936833 2929967170134265670202625)
                ·
                  refine ⟨2197475377600699252651969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2929967170134265670202625 2197475377600699252651969)
                  ·
                    refine ⟨1648106533200524439488977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2197475377600699252651969 1648106533200524439488977)
                    ·
                      refine ⟨1236079899900393329616733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648106533200524439488977 1236079899900393329616733)
                      ·
                        rfl

theorem cell23_2407257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 2, 2].length) (baseStart_2407257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407257 prefixEnd_2407257 := by exact prefixLift 2407257
  have htrace : WordTrace (prefixWord ++ tailWord_2407257) baseStart_2407257 baseEnd_2407257 := by
    simpa [prefixWord, tailWord_2407257, baseEnd_2407257] using wordTrace_append hprefix tailTrace_2407257
  have hstable : (prefixWord ++ tailWord_2407257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407257).length < 2 ^ (prefixWord ++ tailWord_2407257).sum := by decide
  have hdescent : baseEnd_2407257 < baseStart_2407257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407363 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 5, 1, 3]
def baseStart_2407363 : Nat := 118140960795 + 2407363 * 2 ^ 59
def prefixEnd_2407363 : Nat := 4983230072969 + 3 ^ 40 * 2407363 * 2
def baseEnd_2407363 : Nat := 1236134328849769914891245

theorem tailTrace_2407363 : CollatzResearch.WordTrace tailWord_2407363 prefixEnd_2407363 1236134328849769914891245 := by
  unfold tailWord_2407363
  simp only [CollatzResearch.WordTrace]
  refine ⟨87803741977542470712594743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58535827985028313808396495 87803741977542470712594743)
  ·
    refine ⟨131705612966313706068892115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87803741977542470712594743 131705612966313706068892115)
    ·
      refine ⟨197558419449470559103338173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131705612966313706068892115 197558419449470559103338173)
      ·
        refine ⟨74084407293551459663751815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197558419449470559103338173 74084407293551459663751815)
        ·
          refine ⟨111126610940327189495627723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74084407293551459663751815 111126610940327189495627723)
          ·
            refine ⟨166689916410490784243441585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111126610940327189495627723 166689916410490784243441585)
            ·
              refine ⟨125017437307868088182581189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166689916410490784243441585 125017437307868088182581189)
              ·
                refine ⟨23440769495225266534233973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125017437307868088182581189 23440769495225266534233973)
                ·
                  refine ⟨2197572140177368737584435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23440769495225266534233973 2197572140177368737584435)
                  ·
                    refine ⟨3296358210266053106376653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2197572140177368737584435 3296358210266053106376653)
                    ·
                      refine ⟨1236134328849769914891245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3296358210266053106376653 1236134328849769914891245)
                      ·
                        rfl

theorem cell23_2407363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_2407363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407363 prefixEnd_2407363 := by exact prefixLift 2407363
  have htrace : WordTrace (prefixWord ++ tailWord_2407363) baseStart_2407363 baseEnd_2407363 := by
    simpa [prefixWord, tailWord_2407363, baseEnd_2407363] using wordTrace_append hprefix tailTrace_2407363
  have hstable : (prefixWord ++ tailWord_2407363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407363).length < 2 ^ (prefixWord ++ tailWord_2407363).sum := by decide
  have hdescent : baseEnd_2407363 < baseStart_2407363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407374 : List Nat := [4, 1, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_2407374 : Nat := 118140960795 + 2407374 * 2 ^ 59
def prefixEnd_2407374 : Nat := 4983230072969 + 3 ^ 40 * 2407374 * 2
def baseEnd_2407374 : Nat := 412046659045656457284565

theorem tailTrace_2407374 : CollatzResearch.WordTrace tailWord_2407374 prefixEnd_2407374 412046659045656457284565 := by
  unfold tailWord_2407374
  simp only [CollatzResearch.WordTrace]
  refine ⟨10975517897562827448905647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58536095453668413060830117 10975517897562827448905647)
  ·
    refine ⟨16463276846344241173358471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10975517897562827448905647 16463276846344241173358471)
    ·
      refine ⟨24694915269516361760037707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16463276846344241173358471 24694915269516361760037707)
      ·
        refine ⟨37042372904274542640056561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24694915269516361760037707 37042372904274542640056561)
        ·
          refine ⟨27781779678205906980042421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37042372904274542640056561 27781779678205906980042421)
          ·
            refine ⟨2604541844831803779378977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27781779678205906980042421 2604541844831803779378977)
            ·
              refine ⟨1953406383623852834534233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2604541844831803779378977 1953406383623852834534233)
              ·
                refine ⟨1465054787717889625900675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1953406383623852834534233 1465054787717889625900675)
                ·
                  refine ⟨2197582181576834438851013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1465054787717889625900675 2197582181576834438851013)
                  ·
                    refine ⟨412046659045656457284565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2197582181576834438851013 412046659045656457284565)
                    ·
                      rfl

theorem cell23_2407374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_2407374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407374 prefixEnd_2407374 := by exact prefixLift 2407374
  have htrace : WordTrace (prefixWord ++ tailWord_2407374) baseStart_2407374 baseEnd_2407374 := by
    simpa [prefixWord, tailWord_2407374, baseEnd_2407374] using wordTrace_append hprefix tailTrace_2407374
  have hstable : (prefixWord ++ tailWord_2407374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407374).length < 2 ^ (prefixWord ++ tailWord_2407374).sum := by decide
  have hdescent : baseEnd_2407374 < baseStart_2407374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407407 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 2, 3, 2]
def baseStart_2407407 : Nat := 118140960795 + 2407407 * 2 ^ 59
def prefixEnd_2407407 : Nat := 4983230072969 + 3 ^ 40 * 2407407 * 2
def baseEnd_2407407 : Nat := 1236156921998567742741043

theorem tailTrace_2407407 : CollatzResearch.WordTrace tailWord_2407407 prefixEnd_2407407 1236156921998567742741043 := by
  unfold tailWord_2407407
  simp only [CollatzResearch.WordTrace]
  refine ⟨87805346789383066227196475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58536897859588710818130983 87805346789383066227196475)
  ·
    refine ⟨131708020184074599340794713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87805346789383066227196475 131708020184074599340794713)
    ·
      refine ⟨98781015138055949505596035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131708020184074599340794713 98781015138055949505596035)
      ·
        refine ⟨148171522707083924258394053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98781015138055949505596035 148171522707083924258394053)
        ·
          refine ⟨27782160507578235798448885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148171522707083924258394053 27782160507578235798448885)
          ·
            refine ⟨2604577547585459606104583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27782160507578235798448885 2604577547585459606104583)
            ·
              refine ⟨3906866321378189409156875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2604577547585459606104583 3906866321378189409156875)
              ·
                refine ⟨5860299482067284113735313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906866321378189409156875 5860299482067284113735313)
                ·
                  refine ⟨4395224611550463085301485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5860299482067284113735313 4395224611550463085301485)
                  ·
                    refine ⟨1648209229331423656988057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4395224611550463085301485 1648209229331423656988057)
                    ·
                      refine ⟨1236156921998567742741043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648209229331423656988057 1236156921998567742741043)
                      ·
                        rfl

theorem cell23_2407407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 3, 2].length) (baseStart_2407407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407407 prefixEnd_2407407 := by exact prefixLift 2407407
  have htrace : WordTrace (prefixWord ++ tailWord_2407407) baseStart_2407407 baseEnd_2407407 := by
    simpa [prefixWord, tailWord_2407407, baseEnd_2407407] using wordTrace_append hprefix tailTrace_2407407
  have hstable : (prefixWord ++ tailWord_2407407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407407).length < 2 ^ (prefixWord ++ tailWord_2407407).sum := by decide
  have hdescent : baseEnd_2407407 < baseStart_2407407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407414 : List Nat := [5, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_2407414 : Nat := 118140960795 + 2407414 * 2 ^ 59
def prefixEnd_2407414 : Nat := 4983230072969 + 3 ^ 40 * 2407414 * 2
def baseEnd_2407414 : Nat := 1236160516363149215353511

theorem tailTrace_2407414 : CollatzResearch.WordTrace tailWord_2407414 prefixEnd_2407414 1236160516363149215353511 := by
  unfold tailWord_2407414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5487850131272356651418831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58537068066905137615134197 5487850131272356651418831)
  ·
    refine ⟨8231775196908534977128247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5487850131272356651418831 8231775196908534977128247)
    ·
      refine ⟨12347662795362802465692371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8231775196908534977128247 12347662795362802465692371)
      ·
        refine ⟨18521494193044203698538557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12347662795362802465692371 18521494193044203698538557)
        ·
          refine ⟨6945560322391576386951959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18521494193044203698538557 6945560322391576386951959)
          ·
            refine ⟨10418340483587364580427939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6945560322391576386951959 10418340483587364580427939)
            ·
              refine ⟨15627510725381046870641909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10418340483587364580427939 15627510725381046870641909)
              ·
                refine ⟨1465079130504473144122679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15627510725381046870641909 1465079130504473144122679)
                ·
                  refine ⟨2197618695756709716184019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1465079130504473144122679 2197618695756709716184019)
                  ·
                    refine ⟨3296428043635064574276029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2197618695756709716184019 3296428043635064574276029)
                    ·
                      refine ⟨1236160516363149215353511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3296428043635064574276029 1236160516363149215353511)
                      ·
                        rfl

theorem cell23_2407414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_2407414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407414 prefixEnd_2407414 := by exact prefixLift 2407414
  have htrace : WordTrace (prefixWord ++ tailWord_2407414) baseStart_2407414 baseEnd_2407414 := by
    simpa [prefixWord, tailWord_2407414, baseEnd_2407414] using wordTrace_append hprefix tailTrace_2407414
  have hstable : (prefixWord ++ tailWord_2407414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407414).length < 2 ^ (prefixWord ++ tailWord_2407414).sum := by decide
  have hdescent : baseEnd_2407414 < baseStart_2407414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407416 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 6]
def baseStart_2407416 : Nat := 118140960795 + 2407416 * 2 ^ 59
def prefixEnd_2407416 : Nat := 4983230072969 + 3 ^ 40 * 2407416 * 2
def baseEnd_2407416 : Nat := 1236161543324458207528501

theorem tailTrace_2407416 : CollatzResearch.WordTrace tailWord_2407416 prefixEnd_2407416 1236161543324458207528501 := by
  unfold tailWord_2407416
  simp only [CollatzResearch.WordTrace]
  refine ⟨43902837523175230382137051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58537116697566973842849401 43902837523175230382137051)
  ·
    refine ⟨65854256284762845573205577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43902837523175230382137051 65854256284762845573205577)
    ·
      refine ⟨49390692213572134179904183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65854256284762845573205577 49390692213572134179904183)
      ·
        refine ⟨74086038320358201269856275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49390692213572134179904183 74086038320358201269856275)
        ·
          refine ⟨111129057480537301904784413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74086038320358201269856275 111129057480537301904784413)
          ·
            refine ⟨41673396555201488214294155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111129057480537301904784413 41673396555201488214294155)
            ·
              refine ⟨62510094832802232321441233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41673396555201488214294155 62510094832802232321441233)
              ·
                refine ⟨46882571124601674241080925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62510094832802232321441233 46882571124601674241080925)
                ·
                  refine ⟨17580964171725627840405347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46882571124601674241080925 17580964171725627840405347)
                  ·
                    refine ⟨26371446257588441760608021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17580964171725627840405347 26371446257588441760608021)
                    ·
                      refine ⟨1236161543324458207528501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26371446257588441760608021 1236161543324458207528501)
                      ·
                        rfl

theorem cell23_2407416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_2407416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407416 prefixEnd_2407416 := by exact prefixLift 2407416
  have htrace : WordTrace (prefixWord ++ tailWord_2407416) baseStart_2407416 baseEnd_2407416 := by
    simpa [prefixWord, tailWord_2407416, baseEnd_2407416] using wordTrace_append hprefix tailTrace_2407416
  have hstable : (prefixWord ++ tailWord_2407416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407416).length < 2 ^ (prefixWord ++ tailWord_2407416).sum := by decide
  have hdescent : baseEnd_2407416 < baseStart_2407416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407420 : List Nat := [2, 2, 2, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_2407420 : Nat := 118140960795 + 2407420 * 2 ^ 59
def prefixEnd_2407420 : Nat := 4983230072969 + 3 ^ 40 * 2407420 * 2
def baseEnd_2407420 : Nat := 1236163597247076191878483

theorem tailTrace_2407420 : CollatzResearch.WordTrace tailWord_2407420 prefixEnd_2407420 1236163597247076191878483 := by
  unfold tailWord_2407420
  simp only [CollatzResearch.WordTrace]
  refine ⟨43902910469167984723709857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58537213958890646298279809 43902910469167984723709857)
  ·
    refine ⟨32927182851875988542782393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43902910469167984723709857 32927182851875988542782393)
    ·
      refine ⟨24695387138906991407086795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32927182851875988542782393 24695387138906991407086795)
      ·
        refine ⟨37043080708360487110630193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24695387138906991407086795 37043080708360487110630193)
        ·
          refine ⟨27782310531270365332972645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37043080708360487110630193 27782310531270365332972645)
          ·
            refine ⟨5209183224613193499932371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27782310531270365332972645 5209183224613193499932371)
            ·
              refine ⟨7813774836919790249898557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209183224613193499932371 7813774836919790249898557)
              ·
                refine ⟨2930165563844921343711959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7813774836919790249898557 2930165563844921343711959)
                ·
                  refine ⟨4395248345767382015567939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930165563844921343711959 4395248345767382015567939)
                  ·
                    refine ⟨6592872518651073023351909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4395248345767382015567939 6592872518651073023351909)
                    ·
                      refine ⟨1236163597247076191878483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6592872518651073023351909 1236163597247076191878483)
                      ·
                        rfl

theorem cell23_2407420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_2407420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407420 prefixEnd_2407420 := by exact prefixLift 2407420
  have htrace : WordTrace (prefixWord ++ tailWord_2407420) baseStart_2407420 baseEnd_2407420 := by
    simpa [prefixWord, tailWord_2407420, baseEnd_2407420] using wordTrace_append hprefix tailTrace_2407420
  have hstable : (prefixWord ++ tailWord_2407420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407420).length < 2 ^ (prefixWord ++ tailWord_2407420).sum := by decide
  have hdescent : baseEnd_2407420 < baseStart_2407420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407457 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_2407457 : Nat := 118140960795 + 2407457 * 2 ^ 59
def prefixEnd_2407457 : Nat := 4983230072969 + 3 ^ 40 * 2407457 * 2
def baseEnd_2407457 : Nat := 1236182596031292547115813

theorem tailTrace_2407457 : CollatzResearch.WordTrace tailWord_2407457 prefixEnd_2407457 1236182596031292547115813 := by
  unfold tailWord_2407457
  simp only [CollatzResearch.WordTrace]
  refine ⟨87807170439201924766516625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58538113626134616511011083 87807170439201924766516625)
  ·
    refine ⟨65855377829401443574887469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87807170439201924766516625 65855377829401443574887469)
    ·
      refine ⟨24695766686025541340582801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65855377829401443574887469 24695766686025541340582801)
      ·
        refine ⟨18521825014519156005437101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24695766686025541340582801 18521825014519156005437101)
        ·
          refine ⟨6945684380444683502038913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18521825014519156005437101 6945684380444683502038913)
          ·
            refine ⟨5209263285333512626529185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6945684380444683502038913 5209263285333512626529185)
            ·
              refine ⟨3906947464000134469896889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5209263285333512626529185 3906947464000134469896889)
              ·
                refine ⟨2930210598000100852422667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3906947464000134469896889 2930210598000100852422667)
                ·
                  refine ⟨4395315897000151278634001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930210598000100852422667 4395315897000151278634001)
                  ·
                    refine ⟨3296486922750113458975501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4395315897000151278634001 3296486922750113458975501)
                    ·
                      refine ⟨1236182596031292547115813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3296486922750113458975501 1236182596031292547115813)
                      ·
                        rfl

theorem cell23_2407457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_2407457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407457 prefixEnd_2407457 := by exact prefixLift 2407457
  have htrace : WordTrace (prefixWord ++ tailWord_2407457) baseStart_2407457 baseEnd_2407457 := by
    simpa [prefixWord, tailWord_2407457, baseEnd_2407457] using wordTrace_append hprefix tailTrace_2407457
  have hstable : (prefixWord ++ tailWord_2407457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407457).length < 2 ^ (prefixWord ++ tailWord_2407457).sum := by decide
  have hdescent : baseEnd_2407457 < baseStart_2407457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407460 : List Nat := [2, 3, 1, 4, 1, 1, 4, 7]
def baseStart_2407460 : Nat := 118140960795 + 2407460 * 2 ^ 59
def prefixEnd_2407460 : Nat := 4983230072969 + 3 ^ 40 * 2407460 * 2
def baseEnd_2407460 : Nat := 45784597647157630939937

theorem tailTrace_2407460 : CollatzResearch.WordTrace tailWord_2407460 prefixEnd_2407460 45784597647157630939937 := by
  unfold tailWord_2407460
  simp only [CollatzResearch.WordTrace]
  refine ⟨43903639929095528139437917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58538186572127370852583889 43903639929095528139437917)
  ·
    refine ⟨16463864973410823052289219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43903639929095528139437917 16463864973410823052289219)
    ·
      refine ⟨24695797460116234578433829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16463864973410823052289219 24695797460116234578433829)
      ·
        refine ⟨4630462023771793983456343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24695797460116234578433829 4630462023771793983456343)
        ·
          refine ⟨6945693035657690975184515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4630462023771793983456343 6945693035657690975184515)
          ·
            refine ⟨10418539553486536462776773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6945693035657690975184515 10418539553486536462776773)
            ·
              refine ⟨1953476166278725586770645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10418539553486536462776773 1953476166278725586770645)
              ·
                refine ⟨45784597647157630939937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1953476166278725586770645 45784597647157630939937)
                ·
                  rfl

theorem cell23_2407460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 7].length) (baseStart_2407460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407460 prefixEnd_2407460 := by exact prefixLift 2407460
  have htrace : WordTrace (prefixWord ++ tailWord_2407460) baseStart_2407460 baseEnd_2407460 := by
    simpa [prefixWord, tailWord_2407460, baseEnd_2407460] using wordTrace_append hprefix tailTrace_2407460
  have hstable : (prefixWord ++ tailWord_2407460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407460).length < 2 ^ (prefixWord ++ tailWord_2407460).sum := by decide
  have hdescent : baseEnd_2407460 < baseStart_2407460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407470 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_2407470 : Nat := 118140960795 + 2407470 * 2 ^ 59
def prefixEnd_2407470 : Nat := 4983230072969 + 3 ^ 40 * 2407470 * 2
def baseEnd_2407470 : Nat := 1236189271279800996253253

theorem tailTrace_2407470 : CollatzResearch.WordTrace tailWord_2407470 prefixEnd_2407470 1236189271279800996253253 := by
  unfold tailWord_2407470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10975955573519353498342483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58538429725436551991159909 10975955573519353498342483)
  ·
    refine ⟨16463933360279030247513725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10975955573519353498342483 16463933360279030247513725)
    ·
      refine ⟨6173975010104636342817647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16463933360279030247513725 6173975010104636342817647)
      ·
        refine ⟨9260962515156954514226471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6173975010104636342817647 9260962515156954514226471)
        ·
          refine ⟨13891443772735431771339707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9260962515156954514226471 13891443772735431771339707)
          ·
            refine ⟨20837165659103147657009561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13891443772735431771339707 20837165659103147657009561)
            ·
              refine ⟨15627874244327360742757171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20837165659103147657009561 15627874244327360742757171)
              ·
                refine ⟨23441811366491041114135757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15627874244327360742757171 23441811366491041114135757)
                ·
                  refine ⟨8790679262434140417800909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23441811366491041114135757 8790679262434140417800909)
                  ·
                    refine ⟨3296504723412802656675341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8790679262434140417800909 3296504723412802656675341)
                    ·
                      refine ⟨1236189271279800996253253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3296504723412802656675341 1236189271279800996253253)
                      ·
                        rfl

theorem cell23_2407470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_2407470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407470 prefixEnd_2407470 := by exact prefixLift 2407470
  have htrace : WordTrace (prefixWord ++ tailWord_2407470) baseStart_2407470 baseEnd_2407470 := by
    simpa [prefixWord, tailWord_2407470, baseEnd_2407470] using wordTrace_append hprefix tailTrace_2407470
  have hstable : (prefixWord ++ tailWord_2407470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407470).length < 2 ^ (prefixWord ++ tailWord_2407470).sum := by decide
  have hdescent : baseEnd_2407470 < baseStart_2407470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407513 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 4, 4, 3]
def baseStart_2407513 : Nat := 118140960795 + 2407513 * 2 ^ 59
def prefixEnd_2407513 : Nat := 4983230072969 + 3 ^ 40 * 2407513 * 2
def baseEnd_2407513 : Nat := 1236211350947944328015555

theorem tailTrace_2407513 : CollatzResearch.WordTrace tailWord_2407513 prefixEnd_2407513 1236211350947944328015555 := by
  unfold tailWord_2407513
  simp only [CollatzResearch.WordTrace]
  refine ⟨87809212926999046330555193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58539475284666030887036795 87809212926999046330555193)
  ·
    refine ⟨65856909695249284747916395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87809212926999046330555193 65856909695249284747916395)
    ·
      refine ⟨98785364542873927121874593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65856909695249284747916395 98785364542873927121874593)
      ·
        refine ⟨74089023407155445341405945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98785364542873927121874593 74089023407155445341405945)
        ·
          refine ⟨55566767555366584006054459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74089023407155445341405945 55566767555366584006054459)
          ·
            refine ⟨83350151333049876009081689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55566767555366584006054459 83350151333049876009081689)
            ·
              refine ⟨62512613499787407006811267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83350151333049876009081689 62512613499787407006811267)
              ·
                refine ⟨93768920249681110510216901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62512613499787407006811267 93768920249681110510216901)
                ·
                  refine ⟨17581672546815208220665669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93768920249681110510216901 17581672546815208220665669)
                  ·
                    refine ⟨3296563602527851541374813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17581672546815208220665669 3296563602527851541374813)
                    ·
                      refine ⟨1236211350947944328015555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3296563602527851541374813 1236211350947944328015555)
                      ·
                        rfl

theorem cell23_2407513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_2407513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407513 prefixEnd_2407513 := by exact prefixLift 2407513
  have htrace : WordTrace (prefixWord ++ tailWord_2407513) baseStart_2407513 baseEnd_2407513 := by
    simpa [prefixWord, tailWord_2407513, baseEnd_2407513] using wordTrace_append hprefix tailTrace_2407513
  have hstable : (prefixWord ++ tailWord_2407513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407513).length < 2 ^ (prefixWord ++ tailWord_2407513).sum := by decide
  have hdescent : baseEnd_2407513 < baseStart_2407513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407523 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 4]
def baseStart_2407523 : Nat := 118140960795 + 2407523 * 2 ^ 59
def prefixEnd_2407523 : Nat := 4983230072969 + 3 ^ 40 * 2407523 * 2
def baseEnd_2407523 : Nat := 1236216485754489288890509

theorem tailTrace_2407523 : CollatzResearch.WordTrace tailWord_2407523 prefixEnd_2407523 1236216485754489288890509 := by
  unfold tailWord_2407523
  simp only [CollatzResearch.WordTrace]
  refine ⟨87809577656962818038419223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58539718437975212025612815 87809577656962818038419223)
  ·
    refine ⟨131714366485444227057628835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87809577656962818038419223 131714366485444227057628835)
    ·
      refine ⟨197571549728166340586443253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131714366485444227057628835 197571549728166340586443253)
      ·
        refine ⟨18522332787015594429979055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197571549728166340586443253 18522332787015594429979055)
        ·
          refine ⟨27783499180523391644968583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18522332787015594429979055 27783499180523391644968583)
          ·
            refine ⟨41675248770785087467452875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27783499180523391644968583 41675248770785087467452875)
            ·
              refine ⟨62512873156177631201179313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41675248770785087467452875 62512873156177631201179313)
              ·
                refine ⟨46884654867133223400884485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62512873156177631201179313 46884654867133223400884485)
                ·
                  refine ⟨8790872787587479387665841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46884654867133223400884485 8790872787587479387665841)
                  ·
                    refine ⟨6593154590690609540749381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8790872787587479387665841 6593154590690609540749381)
                    ·
                      refine ⟨1236216485754489288890509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6593154590690609540749381 1236216485754489288890509)
                      ·
                        rfl

theorem cell23_2407523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_2407523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407523 prefixEnd_2407523 := by exact prefixLift 2407523
  have htrace : WordTrace (prefixWord ++ tailWord_2407523) baseStart_2407523 baseEnd_2407523 := by
    simpa [prefixWord, tailWord_2407523, baseEnd_2407523] using wordTrace_append hprefix tailTrace_2407523
  have hstable : (prefixWord ++ tailWord_2407523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407523).length < 2 ^ (prefixWord ++ tailWord_2407523).sum := by decide
  have hdescent : baseEnd_2407523 < baseStart_2407523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407527 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_2407527 : Nat := 118140960795 + 2407527 * 2 ^ 59
def prefixEnd_2407527 : Nat := 4983230072969 + 3 ^ 40 * 2407527 * 2
def baseEnd_2407527 : Nat := 1236218539677107273240491

theorem tailTrace_2407527 : CollatzResearch.WordTrace tailWord_2407527 prefixEnd_2407527 1236218539677107273240491 := by
  unfold tailWord_2407527
  simp only [CollatzResearch.WordTrace]
  refine ⟨87809723548948326721564835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58539815699298884481043223 87809723548948326721564835)
  ·
    refine ⟨131714585323422490082347253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87809723548948326721564835 131714585323422490082347253)
    ·
      refine ⟨12348242374070858445220055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131714585323422490082347253 12348242374070858445220055)
      ·
        refine ⟨18522363561106287667830083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12348242374070858445220055 18522363561106287667830083)
        ·
          refine ⟨27783545341659431501745125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18522363561106287667830083 27783545341659431501745125)
          ·
            refine ⟨5209414751561143406577211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27783545341659431501745125 5209414751561143406577211)
            ·
              refine ⟨7814122127341715109865817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209414751561143406577211 7814122127341715109865817)
              ·
                refine ⟨5860591595506286332399363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7814122127341715109865817 5860591595506286332399363)
                ·
                  refine ⟨8790887393259429498599045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5860591595506286332399363 8790887393259429498599045)
                  ·
                    refine ⟨1648291386236143030987321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8790887393259429498599045 1648291386236143030987321)
                    ·
                      refine ⟨1236218539677107273240491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648291386236143030987321 1236218539677107273240491)
                      ·
                        rfl

theorem cell23_2407527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_2407527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407527 prefixEnd_2407527 := by exact prefixLift 2407527
  have htrace : WordTrace (prefixWord ++ tailWord_2407527) baseStart_2407527 baseEnd_2407527 := by
    simpa [prefixWord, tailWord_2407527, baseEnd_2407527] using wordTrace_append hprefix tailTrace_2407527
  have hstable : (prefixWord ++ tailWord_2407527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407527).length < 2 ^ (prefixWord ++ tailWord_2407527).sum := by decide
  have hdescent : baseEnd_2407527 < baseStart_2407527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407530 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2407530 : Nat := 118140960795 + 2407530 * 2 ^ 59
def prefixEnd_2407530 : Nat := 4983230072969 + 3 ^ 40 * 2407530 * 2
def baseEnd_2407530 : Nat := 1236220080119070761502977

theorem tailTrace_2407530 : CollatzResearch.WordTrace tailWord_2407530 prefixEnd_2407530 1236220080119070761502977 := by
  unfold tailWord_2407530
  simp only [CollatzResearch.WordTrace]
  refine ⟨21952458241984364558481011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58539888645291638822616029 21952458241984364558481011)
  ·
    refine ⟨32928687362976546837721517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21952458241984364558481011 32928687362976546837721517)
    ·
      refine ⟨12348257761116205064145569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32928687362976546837721517 12348257761116205064145569)
      ·
        refine ⟨9261193320837153798109177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12348257761116205064145569 9261193320837153798109177)
        ·
          refine ⟨6945894990627865348581883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9261193320837153798109177 6945894990627865348581883)
          ·
            refine ⟨10418842485941798022872825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6945894990627865348581883 10418842485941798022872825)
            ·
              refine ⟨7814131864456348517154619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10418842485941798022872825 7814131864456348517154619)
              ·
                refine ⟨11721197796684522775731929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7814131864456348517154619 11721197796684522775731929)
                ·
                  refine ⟨8790898347513392081798947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11721197796684522775731929 8790898347513392081798947)
                  ·
                    refine ⟨13186347521270088122698421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8790898347513392081798947 13186347521270088122698421)
                    ·
                      refine ⟨1236220080119070761502977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13186347521270088122698421 1236220080119070761502977)
                      ·
                        rfl

theorem cell23_2407530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2407530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407530 prefixEnd_2407530 := by exact prefixLift 2407530
  have htrace : WordTrace (prefixWord ++ tailWord_2407530) baseStart_2407530 baseEnd_2407530 := by
    simpa [prefixWord, tailWord_2407530, baseEnd_2407530] using wordTrace_append hprefix tailTrace_2407530
  have hstable : (prefixWord ++ tailWord_2407530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407530).length < 2 ^ (prefixWord ++ tailWord_2407530).sum := by decide
  have hdescent : baseEnd_2407530 < baseStart_2407530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407563 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 4, 5]
def baseStart_2407563 : Nat := 118140960795 + 2407563 * 2 ^ 59
def prefixEnd_2407563 : Nat := 4983230072969 + 3 ^ 40 * 2407563 * 2
def baseEnd_2407563 : Nat := 412079008326889710796775

theorem tailTrace_2407563 : CollatzResearch.WordTrace tailWord_2407563 prefixEnd_2407563 412079008326889710796775 := by
  unfold tailWord_2407563
  simp only [CollatzResearch.WordTrace]
  refine ⟨87811036576817904869875343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58540691051211936579916895 87811036576817904869875343)
  ·
    refine ⟨131716554865226857304813015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87811036576817904869875343 131716554865226857304813015)
    ·
      refine ⟨197574832297840285957219523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131716554865226857304813015 197574832297840285957219523)
      ·
        refine ⟨296362248446760428935829285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197574832297840285957219523 296362248446760428935829285)
        ·
          refine ⟨55567921583767580425467991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296362248446760428935829285 55567921583767580425467991)
          ·
            refine ⟨83351882375651370638201987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55567921583767580425467991 83351882375651370638201987)
            ·
              refine ⟨125027823563477055957302981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83351882375651370638201987 125027823563477055957302981)
              ·
                refine ⟨23442716918151947991994309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125027823563477055957302981 23442716918151947991994309)
                ·
                  refine ⟨4395509422153490248498933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23442716918151947991994309 4395509422153490248498933)
                  ·
                    refine ⟨412079008326889710796775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4395509422153490248498933 412079008326889710796775)
                    ·
                      rfl

theorem cell23_2407563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 5].length) (baseStart_2407563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407563 prefixEnd_2407563 := by exact prefixLift 2407563
  have htrace : WordTrace (prefixWord ++ tailWord_2407563) baseStart_2407563 baseEnd_2407563 := by
    simpa [prefixWord, tailWord_2407563, baseEnd_2407563] using wordTrace_append hprefix tailTrace_2407563
  have hstable : (prefixWord ++ tailWord_2407563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407563).length < 2 ^ (prefixWord ++ tailWord_2407563).sum := by decide
  have hdescent : baseEnd_2407563 < baseStart_2407563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407573 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_2407573 : Nat := 118140960795 + 2407573 * 2 ^ 59
def prefixEnd_2407573 : Nat := 4983230072969 + 3 ^ 40 * 2407573 * 2
def baseEnd_2407573 : Nat := 1236242159787214093265279

theorem tailTrace_2407573 : CollatzResearch.WordTrace tailWord_2407573 prefixEnd_2407573 1236242159787214093265279 := by
  unfold tailWord_2407573
  simp only [CollatzResearch.WordTrace]
  refine ⟨87811401306781676577739373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58540934204521117718492915 87811401306781676577739373)
  ·
    refine ⟨32929275490043128716652265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87811401306781676577739373 32929275490043128716652265)
    ·
      refine ⟨24696956617532346537489199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32929275490043128716652265 24696956617532346537489199)
      ·
        refine ⟨37045434926298519806233799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24696956617532346537489199 37045434926298519806233799)
        ·
          refine ⟨55568152389447779709350699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37045434926298519806233799 55568152389447779709350699)
          ·
            refine ⟨83352228584171669564026049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55568152389447779709350699 83352228584171669564026049)
            ·
              refine ⟨62514171438128752173019537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83352228584171669564026049 62514171438128752173019537)
              ·
                refine ⟨46885628578596564129764653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62514171438128752173019537 46885628578596564129764653)
                ·
                  refine ⟨17582110716973711548661745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46885628578596564129764653 17582110716973711548661745)
                  ·
                    refine ⟨13186583037730283661496309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17582110716973711548661745 13186583037730283661496309)
                    ·
                      refine ⟨1236242159787214093265279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13186583037730283661496309 1236242159787214093265279)
                      ·
                        rfl

theorem cell23_2407573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_2407573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407573 prefixEnd_2407573 := by exact prefixLift 2407573
  have htrace : WordTrace (prefixWord ++ tailWord_2407573) baseStart_2407573 baseEnd_2407573 := by
    simpa [prefixWord, tailWord_2407573, baseEnd_2407573] using wordTrace_append hprefix tailTrace_2407573
  have hstable : (prefixWord ++ tailWord_2407573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407573).length < 2 ^ (prefixWord ++ tailWord_2407573).sum := by decide
  have hdescent : baseEnd_2407573 < baseStart_2407573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407580 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_2407580 : Nat := 118140960795 + 2407580 * 2 ^ 59
def prefixEnd_2407580 : Nat := 4983230072969 + 3 ^ 40 * 2407580 * 2
def baseEnd_2407580 : Nat := 412081918050598521959249

theorem tailTrace_2407580 : CollatzResearch.WordTrace tailWord_2407580 prefixEnd_2407580 412081918050598521959249 := by
  unfold tailWord_2407580
  simp only [CollatzResearch.WordTrace]
  refine ⟨43905828308878158386622097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58541104411837544515496129 43905828308878158386622097)
  ·
    refine ⟨32929371231658618789966573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43905828308878158386622097 32929371231658618789966573)
    ·
      refine ⟨12348514211871982046237465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32929371231658618789966573 12348514211871982046237465)
      ·
        refine ⟨9261385658903986534678099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12348514211871982046237465 9261385658903986534678099)
        ·
          refine ⟨13892078488355979802017149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9261385658903986534678099 13892078488355979802017149)
          ·
            refine ⟨5209529433133492425756431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13892078488355979802017149 5209529433133492425756431)
            ·
              refine ⟨7814294149700238638634647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209529433133492425756431 7814294149700238638634647)
              ·
                refine ⟨11721441224550357957951971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7814294149700238638634647 11721441224550357957951971)
                ·
                  refine ⟨17582161836825536936927957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11721441224550357957951971 17582161836825536936927957)
                  ·
                    refine ⟨412081918050598521959249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17582161836825536936927957 412081918050598521959249)
                    ·
                      rfl

theorem cell23_2407580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_2407580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407580 prefixEnd_2407580 := by exact prefixLift 2407580
  have htrace : WordTrace (prefixWord ++ tailWord_2407580) baseStart_2407580 baseEnd_2407580 := by
    simpa [prefixWord, tailWord_2407580, baseEnd_2407580] using wordTrace_append hprefix tailTrace_2407580
  have hstable : (prefixWord ++ tailWord_2407580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407580).length < 2 ^ (prefixWord ++ tailWord_2407580).sum := by decide
  have hdescent : baseEnd_2407580 < baseStart_2407580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407600 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 3, 6, 2]
def baseStart_2407600 : Nat := 118140960795 + 2407600 * 2 ^ 59
def prefixEnd_2407600 : Nat := 4983230072969 + 3 ^ 40 * 2407600 * 2
def baseEnd_2407600 : Nat := 1236256023764885487627655

theorem tailTrace_2407600 : CollatzResearch.WordTrace tailWord_2407600 prefixEnd_2407600 1236256023764885487627655 := by
  unfold tailWord_2407600
  simp only [CollatzResearch.WordTrace]
  refine ⟨43906193038841930094486127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58541590718455906792648169 43906193038841930094486127)
  ·
    refine ⟨65859289558262895141729191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43906193038841930094486127 65859289558262895141729191)
    ·
      refine ⟨98788934337394342712593787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65859289558262895141729191 98788934337394342712593787)
      ·
        refine ⟨148183401506091514068890681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98788934337394342712593787 148183401506091514068890681)
        ·
          refine ⟨111137551129568635551668011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148183401506091514068890681 111137551129568635551668011)
          ·
            refine ⟨166706326694352953327502017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111137551129568635551668011 166706326694352953327502017)
            ·
              refine ⟨125029745020764714995626513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166706326694352953327502017 125029745020764714995626513)
              ·
                refine ⟨93772308765573536246719885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125029745020764714995626513 93772308765573536246719885)
                ·
                  refine ⟨35164615787090076092519957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93772308765573536246719885 35164615787090076092519957)
                  ·
                    refine ⟨1648341365019847316836873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35164615787090076092519957 1648341365019847316836873)
                    ·
                      refine ⟨1236256023764885487627655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648341365019847316836873 1236256023764885487627655)
                      ·
                        rfl

theorem cell23_2407600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 6, 2].length) (baseStart_2407600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407600 prefixEnd_2407600 := by exact prefixLift 2407600
  have htrace : WordTrace (prefixWord ++ tailWord_2407600) baseStart_2407600 baseEnd_2407600 := by
    simpa [prefixWord, tailWord_2407600, baseEnd_2407600] using wordTrace_append hprefix tailTrace_2407600
  have hstable : (prefixWord ++ tailWord_2407600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407600).length < 2 ^ (prefixWord ++ tailWord_2407600).sum := by decide
  have hdescent : baseEnd_2407600 < baseStart_2407600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407603 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 5]
def baseStart_2407603 : Nat := 118140960795 + 2407603 * 2 ^ 59
def prefixEnd_2407603 : Nat := 4983230072969 + 3 ^ 40 * 2407603 * 2
def baseEnd_2407603 : Nat := 1236257564206848975890141

theorem tailTrace_2407603 : CollatzResearch.WordTrace tailWord_2407603 prefixEnd_2407603 1236257564206848975890141 := by
  unfold tailWord_2407603
  simp only [CollatzResearch.WordTrace]
  refine ⟨87812495496672991701331463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58541663664448661134220975 87812495496672991701331463)
  ·
    refine ⟨131718743245009487551997195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87812495496672991701331463 131718743245009487551997195)
    ·
      refine ⟨197578114867514231327995793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131718743245009487551997195 197578114867514231327995793)
      ·
        refine ⟨148183586150635673495996845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197578114867514231327995793 148183586150635673495996845)
        ·
          refine ⟨55568844806488377560998817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148183586150635673495996845 55568844806488377560998817)
          ·
            refine ⟨41676633604866283170749113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55568844806488377560998817 41676633604866283170749113)
            ·
              refine ⟨31257475203649712378061835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41676633604866283170749113 31257475203649712378061835)
              ·
                refine ⟨46886212805474568567092753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31257475203649712378061835 46886212805474568567092753)
                ·
                  refine ⟨35164659604105926425319565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46886212805474568567092753 35164659604105926425319565)
                  ·
                    refine ⟨13186747351539722409494837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35164659604105926425319565 13186747351539722409494837)
                    ·
                      refine ⟨1236257564206848975890141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13186747351539722409494837 1236257564206848975890141)
                      ·
                        rfl

theorem cell23_2407603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_2407603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407603 prefixEnd_2407603 := by exact prefixLift 2407603
  have htrace : WordTrace (prefixWord ++ tailWord_2407603) baseStart_2407603 baseEnd_2407603 := by
    simpa [prefixWord, tailWord_2407603, baseEnd_2407603] using wordTrace_append hprefix tailTrace_2407603
  have hstable : (prefixWord ++ tailWord_2407603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407603).length < 2 ^ (prefixWord ++ tailWord_2407603).sum := by decide
  have hdescent : baseEnd_2407603 < baseStart_2407603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407617 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2407617 : Nat := 118140960795 + 2407617 * 2 ^ 59
def prefixEnd_2407617 : Nat := 4983230072969 + 3 ^ 40 * 2407617 * 2
def baseEnd_2407617 : Nat := 1236264752936011921115077

theorem tailTrace_2407617 : CollatzResearch.WordTrace tailWord_2407617 prefixEnd_2407617 1236264752936011921115077 := by
  unfold tailWord_2407617
  simp only [CollatzResearch.WordTrace]
  refine ⟨87813006118622272092341105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58542004079081514728227403 87813006118622272092341105)
  ·
    refine ⟨65859754588966704069255829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87813006118622272092341105 65859754588966704069255829)
    ·
      refine ⟨3087175996357814253246367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65859754588966704069255829 3087175996357814253246367)
      ·
        refine ⟨4630763994536721379869551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3087175996357814253246367 4630763994536721379869551)
        ·
          refine ⟨6946145991805082069804327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4630763994536721379869551 6946145991805082069804327)
          ·
            refine ⟨10419218987707623104706491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6946145991805082069804327 10419218987707623104706491)
            ·
              refine ⟨15628828481561434657059737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10419218987707623104706491 15628828481561434657059737)
              ·
                refine ⟨11721621361171075992794803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15628828481561434657059737 11721621361171075992794803)
                ·
                  refine ⟨17582432041756613989192205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11721621361171075992794803 17582432041756613989192205)
                  ·
                    refine ⟨6593412015658730245947077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17582432041756613989192205 6593412015658730245947077)
                    ·
                      refine ⟨1236264752936011921115077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6593412015658730245947077 1236264752936011921115077)
                      ·
                        rfl

theorem cell23_2407617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2407617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407617 prefixEnd_2407617 := by exact prefixLift 2407617
  have htrace : WordTrace (prefixWord ++ tailWord_2407617) baseStart_2407617 baseEnd_2407617 := by
    simpa [prefixWord, tailWord_2407617, baseEnd_2407617] using wordTrace_append hprefix tailTrace_2407617
  have hstable : (prefixWord ++ tailWord_2407617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407617).length < 2 ^ (prefixWord ++ tailWord_2407617).sum := by decide
  have hdescent : baseEnd_2407617 < baseStart_2407617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407637 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2407637 : Nat := 118140960795 + 2407637 * 2 ^ 59
def prefixEnd_2407637 : Nat := 4983230072969 + 3 ^ 40 * 2407637 * 2
def baseEnd_2407637 : Nat := 1236275022549101842864985

theorem tailTrace_2407637 : CollatzResearch.WordTrace tailWord_2407637 prefixEnd_2407637 1236275022549101842864985 := by
  unfold tailWord_2407637
  simp only [CollatzResearch.WordTrace]
  refine ⟨87813735578549815508069165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58542490385699877005379443 87813735578549815508069165)
  ·
    refine ⟨32930150841956180815525937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87813735578549815508069165 32930150841956180815525937)
    ·
      refine ⟨24697613131467135611644453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32930150841956180815525937 24697613131467135611644453)
      ·
        refine ⟨4630802462150087927183335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24697613131467135611644453 4630802462150087927183335)
        ·
          refine ⟨6946203693225131890775003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4630802462150087927183335 6946203693225131890775003)
          ·
            refine ⟨10419305539837697836162505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6946203693225131890775003 10419305539837697836162505)
            ·
              refine ⟨7814479154878273377121879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10419305539837697836162505 7814479154878273377121879)
              ·
                refine ⟨11721718732317410065682819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7814479154878273377121879 11721718732317410065682819)
                ·
                  refine ⟨17582578098476115098524229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11721718732317410065682819 17582578098476115098524229)
                  ·
                    refine ⟨3296733393464271580973293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17582578098476115098524229 3296733393464271580973293)
                    ·
                      refine ⟨1236275022549101842864985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3296733393464271580973293 1236275022549101842864985)
                      ·
                        rfl

theorem cell23_2407637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2407637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407637 prefixEnd_2407637 := by exact prefixLift 2407637
  have htrace : WordTrace (prefixWord ++ tailWord_2407637) baseStart_2407637 baseEnd_2407637 := by
    simpa [prefixWord, tailWord_2407637, baseEnd_2407637] using wordTrace_append hprefix tailTrace_2407637
  have hstable : (prefixWord ++ tailWord_2407637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407637).length < 2 ^ (prefixWord ++ tailWord_2407637).sum := by decide
  have hdescent : baseEnd_2407637 < baseStart_2407637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407670 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_2407670 : Nat := 118140960795 + 2407670 * 2 ^ 59
def prefixEnd_2407670 : Nat := 4983230072969 + 3 ^ 40 * 2407670 * 2
def baseEnd_2407670 : Nat := 412097322470233404584111

theorem tailTrace_2407670 : CollatzResearch.WordTrace tailWord_2407670 prefixEnd_2407670 412097322470233404584111 := by
  unfold tailWord_2407670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5488433699214391384001279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58543292791620174762680309 5488433699214391384001279)
  ·
    refine ⟨8232650548821587076001919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5488433699214391384001279 8232650548821587076001919)
    ·
      refine ⟨12348975823232380614002879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8232650548821587076001919 12348975823232380614002879)
      ·
        refine ⟨18523463734848570921004319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12348975823232380614002879 18523463734848570921004319)
        ·
          refine ⟨27785195602272856381506479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18523463734848570921004319 27785195602272856381506479)
          ·
            refine ⟨41677793403409284572259719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27785195602272856381506479 41677793403409284572259719)
            ·
              refine ⟨62516690105113926858389579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41677793403409284572259719 62516690105113926858389579)
              ·
                refine ⟨93775035157670890287584369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62516690105113926858389579 93775035157670890287584369)
                ·
                  refine ⟨70331276368253167715688277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93775035157670890287584369 70331276368253167715688277)
                  ·
                    refine ⟨412097322470233404584111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 70331276368253167715688277 412097322470233404584111)
                    ·
                      rfl

theorem cell23_2407670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_2407670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407670 prefixEnd_2407670 := by exact prefixLift 2407670
  have htrace : WordTrace (prefixWord ++ tailWord_2407670) baseStart_2407670 baseEnd_2407670 := by
    simpa [prefixWord, tailWord_2407670, baseEnd_2407670] using wordTrace_append hprefix tailTrace_2407670
  have hstable : (prefixWord ++ tailWord_2407670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407670).length < 2 ^ (prefixWord ++ tailWord_2407670).sum := by decide
  have hdescent : baseEnd_2407670 < baseStart_2407670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407694 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2]
def baseStart_2407694 : Nat := 118140960795 + 2407694 * 2 ^ 59
def prefixEnd_2407694 : Nat := 4983230072969 + 3 ^ 40 * 2407694 * 2
def baseEnd_2407694 : Nat := 1236304290946408119852223

theorem tailTrace_2407694 : CollatzResearch.WordTrace tailWord_2407694 prefixEnd_2407694 1236304290946408119852223 := by
  unfold tailWord_2407694
  simp only [CollatzResearch.WordTrace]
  refine ⟨10976976817417914280361767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58543876359562209495262757 10976976817417914280361767)
  ·
    refine ⟨16465465226126871420542651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10976976817417914280361767 16465465226126871420542651)
    ·
      refine ⟨24698197839190307130813977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16465465226126871420542651 24698197839190307130813977)
      ·
        refine ⟨18523648379392730348110483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24698197839190307130813977 18523648379392730348110483)
        ·
          refine ⟨27785472569089095522165725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18523648379392730348110483 27785472569089095522165725)
          ·
            refine ⟨10419552213408410820812147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27785472569089095522165725 10419552213408410820812147)
            ·
              refine ⟨15629328320112616231218221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10419552213408410820812147 15629328320112616231218221)
              ·
                refine ⟨5860998120042231086706833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15629328320112616231218221 5860998120042231086706833)
                ·
                  refine ⟨4395748590031673315030125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5860998120042231086706833 4395748590031673315030125)
                  ·
                    refine ⟨1648405721261877493136297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4395748590031673315030125 1648405721261877493136297)
                    ·
                      refine ⟨1236304290946408119852223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648405721261877493136297 1236304290946408119852223)
                      ·
                        rfl

theorem cell23_2407694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_2407694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407694 prefixEnd_2407694 := by exact prefixLift 2407694
  have htrace : WordTrace (prefixWord ++ tailWord_2407694) baseStart_2407694 baseEnd_2407694 := by
    simpa [prefixWord, tailWord_2407694, baseEnd_2407694] using wordTrace_append hprefix tailTrace_2407694
  have hstable : (prefixWord ++ tailWord_2407694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407694).length < 2 ^ (prefixWord ++ tailWord_2407694).sum := by decide
  have hdescent : baseEnd_2407694 < baseStart_2407694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407704 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 1, 5]
def baseStart_2407704 : Nat := 118140960795 + 2407704 * 2 ^ 59
def prefixEnd_2407704 : Nat := 4983230072969 + 3 ^ 40 * 2407704 * 2
def baseEnd_2407704 : Nat := 412103141917651026909059

theorem tailTrace_2407704 : CollatzResearch.WordTrace tailWord_2407704 prefixEnd_2407704 412103141917651026909059 := by
  unfold tailWord_2407704
  simp only [CollatzResearch.WordTrace]
  refine ⟨43908089634653542975379083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58544119512871390633838777 43908089634653542975379083)
  ·
    refine ⟨65862134451980314463068625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43908089634653542975379083 65862134451980314463068625)
    ·
      refine ⟨49396600838985235847301469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65862134451980314463068625 49396600838985235847301469)
      ·
        refine ⟨18523725314619463442738051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49396600838985235847301469 18523725314619463442738051)
        ·
          refine ⟨27785587971929195164107077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18523725314619463442738051 27785587971929195164107077)
          ·
            refine ⟨5209797744736724093270077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27785587971929195164107077 5209797744736724093270077)
            ·
              refine ⟨1953674154276271534976279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5209797744736724093270077 1953674154276271534976279)
              ·
                refine ⟨2930511231414407302464419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1953674154276271534976279 2930511231414407302464419)
                ·
                  refine ⟨4395766847121610953696629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930511231414407302464419 4395766847121610953696629)
                  ·
                    refine ⟨412103141917651026909059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4395766847121610953696629 412103141917651026909059)
                    ·
                      rfl

theorem cell23_2407704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_2407704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407704 prefixEnd_2407704 := by exact prefixLift 2407704
  have htrace : WordTrace (prefixWord ++ tailWord_2407704) baseStart_2407704 baseEnd_2407704 := by
    simpa [prefixWord, tailWord_2407704, baseEnd_2407704] using wordTrace_append hprefix tailTrace_2407704
  have hstable : (prefixWord ++ tailWord_2407704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407704).length < 2 ^ (prefixWord ++ tailWord_2407704).sum := by decide
  have hdescent : baseEnd_2407704 < baseStart_2407704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407724 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 3, 2, 2]
def baseStart_2407724 : Nat := 118140960795 + 2407724 * 2 ^ 59
def prefixEnd_2407724 : Nat := 4983230072969 + 3 ^ 40 * 2407724 * 2
def baseEnd_2407724 : Nat := 1236319695366043002477085

theorem tailTrace_2407724 : CollatzResearch.WordTrace tailWord_2407724 prefixEnd_2407724 1236319695366043002477085 := by
  unfold tailWord_2407724
  simp only [CollatzResearch.WordTrace]
  refine ⟨43908454364617314683243113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58544605819489752910990817 43908454364617314683243113)
  ·
    refine ⟨32931340773462986012432335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43908454364617314683243113 32931340773462986012432335)
    ·
      refine ⟨49397011160194479018648503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32931340773462986012432335 49397011160194479018648503)
      ·
        refine ⟨74095516740291718527972755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49397011160194479018648503 74095516740291718527972755)
        ·
          refine ⟨111143275110437577791959133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74095516740291718527972755 111143275110437577791959133)
          ·
            refine ⟨41678728166414091671984675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111143275110437577791959133 41678728166414091671984675)
            ·
              refine ⟨62518092249621137507977013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41678728166414091671984675 62518092249621137507977013)
              ·
                refine ⟨5861071148401981641372845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62518092249621137507977013 5861071148401981641372845)
                ·
                  refine ⟨2197901680650743115514817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5861071148401981641372845 2197901680650743115514817)
                  ·
                    refine ⟨1648426260488057336636113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2197901680650743115514817 1648426260488057336636113)
                    ·
                      refine ⟨1236319695366043002477085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648426260488057336636113 1236319695366043002477085)
                      ·
                        rfl

theorem cell23_2407724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 2, 2].length) (baseStart_2407724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407724 prefixEnd_2407724 := by exact prefixLift 2407724
  have htrace : WordTrace (prefixWord ++ tailWord_2407724) baseStart_2407724 baseEnd_2407724 := by
    simpa [prefixWord, tailWord_2407724, baseEnd_2407724] using wordTrace_append hprefix tailTrace_2407724
  have hstable : (prefixWord ++ tailWord_2407724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407724).length < 2 ^ (prefixWord ++ tailWord_2407724).sum := by decide
  have hdescent : baseEnd_2407724 < baseStart_2407724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407758 : List Nat := [4, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2]
def baseStart_2407758 : Nat := 118140960795 + 2407758 * 2 ^ 59
def prefixEnd_2407758 : Nat := 4983230072969 + 3 ^ 40 * 2407758 * 2
def baseEnd_2407758 : Nat := 1236337153708295869451929

theorem tailTrace_2407758 : CollatzResearch.WordTrace tailWord_2407758 prefixEnd_2407758 1236337153708295869451929 := by
  unfold tailWord_2407758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10977268601388931646652991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58545432540740968782149285 10977268601388931646652991)
  ·
    refine ⟨16465902902083397469979487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10977268601388931646652991 16465902902083397469979487)
    ·
      refine ⟨24698854353125096204969231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16465902902083397469979487 24698854353125096204969231)
      ·
        refine ⟨37048281529687644307453847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24698854353125096204969231 37048281529687644307453847)
        ·
          refine ⟨55572422294531466461180771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37048281529687644307453847 55572422294531466461180771)
          ·
            refine ⟨83358633441797199691771157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55572422294531466461180771 83358633441797199691771157)
            ·
              refine ⟨3907435942584243735551773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83358633441797199691771157 3907435942584243735551773)
              ·
                refine ⟨1465288478469091400831915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3907435942584243735551773 1465288478469091400831915)
                ·
                  refine ⟨2197932717703637101247873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1465288478469091400831915 2197932717703637101247873)
                  ·
                    refine ⟨1648449538277727825935905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2197932717703637101247873 1648449538277727825935905)
                    ·
                      refine ⟨1236337153708295869451929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648449538277727825935905 1236337153708295869451929)
                      ·
                        rfl

theorem cell23_2407758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_2407758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407758 prefixEnd_2407758 := by exact prefixLift 2407758
  have htrace : WordTrace (prefixWord ++ tailWord_2407758) baseStart_2407758 baseEnd_2407758 := by
    simpa [prefixWord, tailWord_2407758, baseEnd_2407758] using wordTrace_append hprefix tailTrace_2407758
  have hstable : (prefixWord ++ tailWord_2407758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407758).length < 2 ^ (prefixWord ++ tailWord_2407758).sum := by decide
  have hdescent : baseEnd_2407758 < baseStart_2407758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407791 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 2, 1, 3]
def baseStart_2407791 : Nat := 118140960795 + 2407791 * 2 ^ 59
def prefixEnd_2407791 : Nat := 4983230072969 + 3 ^ 40 * 2407791 * 2
def baseEnd_2407791 : Nat := 1236354098569894240339277

theorem tailTrace_2407791 : CollatzResearch.WordTrace tailWord_2407791 prefixEnd_2407791 1236354098569894240339277 := by
  unfold tailWord_2407791
  simp only [CollatzResearch.WordTrace]
  refine ⟨87819352419991899809175227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58546234946661266539450151 87819352419991899809175227)
  ·
    refine ⟨131729028629987849713762841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87819352419991899809175227 131729028629987849713762841)
    ·
      refine ⟨98796771472490887285322131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131729028629987849713762841 98796771472490887285322131)
      ·
        refine ⟨148195157208736330927983197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98796771472490887285322131 148195157208736330927983197)
        ·
          refine ⟨55573183953276124097993699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148195157208736330927983197 55573183953276124097993699)
          ·
            refine ⟨83359775929914186146990549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55573183953276124097993699 83359775929914186146990549)
            ·
              refine ⟨1953744748357363737820091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83359775929914186146990549 1953744748357363737820091)
              ·
                refine ⟨2930617122536045606730137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1953744748357363737820091 2930617122536045606730137)
                ·
                  refine ⟨2197962841902034205047603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2930617122536045606730137 2197962841902034205047603)
                  ·
                    refine ⟨3296944262853051307571405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2197962841902034205047603 3296944262853051307571405)
                    ·
                      refine ⟨1236354098569894240339277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3296944262853051307571405 1236354098569894240339277)
                      ·
                        rfl

theorem cell23_2407791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 2, 1, 3].length) (baseStart_2407791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407791 prefixEnd_2407791 := by exact prefixLift 2407791
  have htrace : WordTrace (prefixWord ++ tailWord_2407791) baseStart_2407791 baseEnd_2407791 := by
    simpa [prefixWord, tailWord_2407791, baseEnd_2407791] using wordTrace_append hprefix tailTrace_2407791
  have hstable : (prefixWord ++ tailWord_2407791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407791).length < 2 ^ (prefixWord ++ tailWord_2407791).sum := by decide
  have hdescent : baseEnd_2407791 < baseStart_2407791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407800 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_2407800 : Nat := 118140960795 + 2407800 * 2 ^ 59
def prefixEnd_2407800 : Nat := 4983230072969 + 3 ^ 40 * 2407800 * 2
def baseEnd_2407800 : Nat := 1236358719895784705126735

theorem tailTrace_2407800 : CollatzResearch.WordTrace tailWord_2407800 prefixEnd_2407800 1236358719895784705126735 := by
  unfold tailWord_2407800
  simp only [CollatzResearch.WordTrace]
  refine ⟨43909840338479647173126427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58546453784639529564168569 43909840338479647173126427)
  ·
    refine ⟨65864760507719470759689641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43909840338479647173126427 65864760507719470759689641)
    ·
      refine ⟨49398570380789603069767231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65864760507719470759689641 49398570380789603069767231)
      ·
        refine ⟨74097855571184404604650847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49398570380789603069767231 74097855571184404604650847)
        ·
          refine ⟨111146783356776606906976271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74097855571184404604650847 111146783356776606906976271)
          ·
            refine ⟨166720175035164910360464407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111146783356776606906976271 166720175035164910360464407)
            ·
              refine ⟨250080262552747365540696611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166720175035164910360464407 250080262552747365540696611)
              ·
                refine ⟨375120393829121048311044917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250080262552747365540696611 375120393829121048311044917)
                ·
                  refine ⟨35167536921480098279160461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375120393829121048311044917 35167536921480098279160461)
                  ·
                    refine ⟨13187826345555036854685173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35167536921480098279160461 13187826345555036854685173)
                    ·
                      refine ⟨1236358719895784705126735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13187826345555036854685173 1236358719895784705126735)
                      ·
                        rfl

theorem cell23_2407800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_2407800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407800 prefixEnd_2407800 := by exact prefixLift 2407800
  have htrace : WordTrace (prefixWord ++ tailWord_2407800) baseStart_2407800 baseEnd_2407800 := by
    simpa [prefixWord, tailWord_2407800, baseEnd_2407800] using wordTrace_append hprefix tailTrace_2407800
  have hstable : (prefixWord ++ tailWord_2407800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407800).length < 2 ^ (prefixWord ++ tailWord_2407800).sum := by decide
  have hdescent : baseEnd_2407800 < baseStart_2407800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407831 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 2, 2, 2]
def baseStart_2407831 : Nat := 118140960795 + 2407831 * 2 ^ 59
def prefixEnd_2407831 : Nat := 4983230072969 + 3 ^ 40 * 2407831 * 2
def baseEnd_2407831 : Nat := 1236374637796074083839093

theorem tailTrace_2407831 : CollatzResearch.WordTrace tailWord_2407831 prefixEnd_2407831 1236374637796074083839093 := by
  unfold tailWord_2407831
  simp only [CollatzResearch.WordTrace]
  refine ⟨87820811339846986640631347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58547207559897991093754231 87820811339846986640631347)
  ·
    refine ⟨131731217009770479960947021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87820811339846986640631347 131731217009770479960947021)
    ·
      refine ⟨49399206378663929985355133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131731217009770479960947021 49399206378663929985355133)
      ·
        refine ⟨18524702391998973744508175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49399206378663929985355133 18524702391998973744508175)
        ·
          refine ⟨27787053587998460616762263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18524702391998973744508175 27787053587998460616762263)
          ·
            refine ⟨41680580381997690925143395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27787053587998460616762263 41680580381997690925143395)
            ·
              refine ⟨62520870572996536387715093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41680580381997690925143395 62520870572996536387715093)
              ·
                refine ⟨2930665808109212643174145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62520870572996536387715093 2930665808109212643174145)
                ·
                  refine ⟨2197999356081909482380609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2930665808109212643174145 2197999356081909482380609)
                  ·
                    refine ⟨1648499517061432111785457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2197999356081909482380609 1648499517061432111785457)
                    ·
                      refine ⟨1236374637796074083839093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648499517061432111785457 1236374637796074083839093)
                      ·
                        rfl

theorem cell23_2407831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_2407831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407831 prefixEnd_2407831 := by exact prefixLift 2407831
  have htrace : WordTrace (prefixWord ++ tailWord_2407831) baseStart_2407831 baseEnd_2407831 := by
    simpa [prefixWord, tailWord_2407831, baseEnd_2407831] using wordTrace_append hprefix tailTrace_2407831
  have hstable : (prefixWord ++ tailWord_2407831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407831).length < 2 ^ (prefixWord ++ tailWord_2407831).sum := by decide
  have hdescent : baseEnd_2407831 < baseStart_2407831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407884 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_2407884 : Nat := 118140960795 + 2407884 * 2 ^ 59
def prefixEnd_2407884 : Nat := 4983230072969 + 3 ^ 40 * 2407884 * 2
def baseEnd_2407884 : Nat := 412133950756920792158783

theorem tailTrace_2407884 : CollatzResearch.WordTrace tailWord_2407884 prefixEnd_2407884 412133950756920792158783 := by
  unfold tailWord_2407884
  simp only [CollatzResearch.WordTrace]
  refine ⟨43911372204327488346155353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58548496272436651128207137 43911372204327488346155353)
  ·
    refine ⟨32933529153245616259616515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43911372204327488346155353 32933529153245616259616515)
    ·
      refine ⟨49400293729868424389424773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32933529153245616259616515 49400293729868424389424773)
      ·
        refine ⟨9262555074350329573017145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49400293729868424389424773 9262555074350329573017145)
        ·
          refine ⟨6946916305762747179762859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9262555074350329573017145 6946916305762747179762859)
          ·
            refine ⟨10420374458644120769644289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6946916305762747179762859 10420374458644120769644289)
            ·
              refine ⟨7815280843983090577233217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10420374458644120769644289 7815280843983090577233217)
              ·
                refine ⟨5861460632987317932924913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7815280843983090577233217 5861460632987317932924913)
                ·
                  refine ⟨4396095474740488449693685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5861460632987317932924913 4396095474740488449693685)
                  ·
                    refine ⟨412133950756920792158783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4396095474740488449693685 412133950756920792158783)
                    ·
                      rfl

theorem cell23_2407884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_2407884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407884 prefixEnd_2407884 := by exact prefixLift 2407884
  have htrace : WordTrace (prefixWord ++ tailWord_2407884) baseStart_2407884 baseEnd_2407884 := by
    simpa [prefixWord, tailWord_2407884, baseEnd_2407884] using wordTrace_append hprefix tailTrace_2407884
  have hstable : (prefixWord ++ tailWord_2407884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407884).length < 2 ^ (prefixWord ++ tailWord_2407884).sum := by decide
  have hdescent : baseEnd_2407884 < baseStart_2407884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407921 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 4]
def baseStart_2407921 : Nat := 118140960795 + 2407921 * 2 ^ 59
def prefixEnd_2407921 : Nat := 4983230072969 + 3 ^ 40 * 2407921 * 2
def baseEnd_2407921 : Nat := 1236420851054978731713679

theorem tailTrace_2407921 : CollatzResearch.WordTrace tailWord_2407921 prefixEnd_2407921 1236420851054978731713679 := by
  unfold tailWord_2407921
  simp only [CollatzResearch.WordTrace]
  refine ⟨87824093909520932011407617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58549395939680621340938411 87824093909520932011407617)
  ·
    refine ⟨65868070432140699008555713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87824093909520932011407617 65868070432140699008555713)
    ·
      refine ⟨49401052824105524256416785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65868070432140699008555713 49401052824105524256416785)
      ·
        refine ⟨37050789618079143192312589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49401052824105524256416785 37050789618079143192312589)
        ·
          refine ⟨13894046106779678697117221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37050789618079143192312589 13894046106779678697117221)
          ·
            refine ⟨2605133645021189755709479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13894046106779678697117221 2605133645021189755709479)
            ·
              refine ⟨3907700467531784633564219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605133645021189755709479 3907700467531784633564219)
              ·
                refine ⟨5861550701297676950346329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3907700467531784633564219 5861550701297676950346329)
                ·
                  refine ⟨4396163025973257712759747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5861550701297676950346329 4396163025973257712759747)
                  ·
                    refine ⟨6594244538959886569139621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4396163025973257712759747 6594244538959886569139621)
                    ·
                      refine ⟨1236420851054978731713679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6594244538959886569139621 1236420851054978731713679)
                      ·
                        rfl

theorem cell23_2407921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_2407921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407921 prefixEnd_2407921 := by exact prefixLift 2407921
  have htrace : WordTrace (prefixWord ++ tailWord_2407921) baseStart_2407921 baseEnd_2407921 := by
    simpa [prefixWord, tailWord_2407921, baseEnd_2407921] using wordTrace_append hprefix tailTrace_2407921
  have hstable : (prefixWord ++ tailWord_2407921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407921).length < 2 ^ (prefixWord ++ tailWord_2407921).sum := by decide
  have hdescent : baseEnd_2407921 < baseStart_2407921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407938 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_2407938 : Nat := 118140960795 + 2407938 * 2 ^ 59
def prefixEnd_2407938 : Nat := 4983230072969 + 3 ^ 40 * 2407938 * 2
def baseEnd_2407938 : Nat := 1236429580226105165201101

theorem tailTrace_2407938 : CollatzResearch.WordTrace tailWord_2407938 prefixEnd_2407938 1236429580226105165201101 := by
  unfold tailWord_2407938
  simp only [CollatzResearch.WordTrace]
  refine ⟨21956178487614835978694117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58549809300306229276517645 21956178487614835978694117)
  ·
    refine ⟨4116783466427781746005147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21956178487614835978694117 4116783466427781746005147)
    ·
      refine ⟨6175175199641672619007721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4116783466427781746005147 6175175199641672619007721)
      ·
        refine ⟨4631381399731254464255791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6175175199641672619007721 4631381399731254464255791)
        ·
          refine ⟨6947072099596881696383687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4631381399731254464255791 6947072099596881696383687)
          ·
            refine ⟨10420608149395322544575531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6947072099596881696383687 10420608149395322544575531)
            ·
              refine ⟨15630912224092983816863297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10420608149395322544575531 15630912224092983816863297)
              ·
                refine ⟨11723184168069737862647473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15630912224092983816863297 11723184168069737862647473)
                ·
                  refine ⟨8792388126052303396985605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11723184168069737862647473 8792388126052303396985605)
                  ·
                    refine ⟨1648572773634806886934801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8792388126052303396985605 1648572773634806886934801)
                    ·
                      refine ⟨1236429580226105165201101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648572773634806886934801 1236429580226105165201101)
                      ·
                        rfl

theorem cell23_2407938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_2407938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407938 prefixEnd_2407938 := by exact prefixLift 2407938
  have htrace : WordTrace (prefixWord ++ tailWord_2407938) baseStart_2407938 baseEnd_2407938 := by
    simpa [prefixWord, tailWord_2407938, baseEnd_2407938] using wordTrace_append hprefix tailTrace_2407938
  have hstable : (prefixWord ++ tailWord_2407938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407938).length < 2 ^ (prefixWord ++ tailWord_2407938).sum := by decide
  have hdescent : baseEnd_2407938 < baseStart_2407938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407944 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 6]
def baseStart_2407944 : Nat := 118140960795 + 2407944 * 2 ^ 59
def prefixEnd_2407944 : Nat := 4983230072969 + 3 ^ 40 * 2407944 * 2
def baseEnd_2407944 : Nat := 137381406790003571302897

theorem tailTrace_2407944 : CollatzResearch.WordTrace tailWord_2407944 prefixEnd_2407944 137381406790003571302897 := by
  unfold tailWord_2407944
  simp only [CollatzResearch.WordTrace]
  refine ⟨43912466394218803469747443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58549955192291737959663257 43912466394218803469747443)
  ·
    refine ⟨65868699591328205204621165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43912466394218803469747443 65868699591328205204621165)
    ·
      refine ⟨24700762346748076951732937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65868699591328205204621165 24700762346748076951732937)
      ·
        refine ⟨18525571760061057713799703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24700762346748076951732937 18525571760061057713799703)
        ·
          refine ⟨27788357640091586570699555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18525571760061057713799703 27788357640091586570699555)
          ·
            refine ⟨41682536460137379856049333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27788357640091586570699555 41682536460137379856049333)
            ·
              refine ⟨3907737793137879361504625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41682536460137379856049333 3907737793137879361504625)
              ·
                refine ⟨2930803344853409521128469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3907737793137879361504625 2930803344853409521128469)
                ·
                  refine ⟨137381406790003571302897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2930803344853409521128469 137381406790003571302897)
                  ·
                    rfl

theorem cell23_2407944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 6].length) (baseStart_2407944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407944 prefixEnd_2407944 := by exact prefixLift 2407944
  have htrace : WordTrace (prefixWord ++ tailWord_2407944) baseStart_2407944 baseEnd_2407944 := by
    simpa [prefixWord, tailWord_2407944, baseEnd_2407944] using wordTrace_append hprefix tailTrace_2407944
  have hstable : (prefixWord ++ tailWord_2407944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407944).length < 2 ^ (prefixWord ++ tailWord_2407944).sum := by decide
  have hdescent : baseEnd_2407944 < baseStart_2407944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2407967 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_2407967 : Nat := 118140960795 + 2407967 * 2 ^ 59
def prefixEnd_2407967 : Nat := 4983230072969 + 3 ^ 40 * 2407967 * 2
def baseEnd_2407967 : Nat := 1236444471165085551738467

theorem tailTrace_2407967 : CollatzResearch.WordTrace tailWord_2407967 prefixEnd_2407967 1236444471165085551738467 := by
  unfold tailWord_2407967
  simp only [CollatzResearch.WordTrace]
  refine ⟨87825771667354281867582155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58550514444902854578388103 87825771667354281867582155)
  ·
    refine ⟨131738657501031422801373233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87825771667354281867582155 131738657501031422801373233)
    ·
      refine ⟨98803993125773567101029925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131738657501031422801373233 98803993125773567101029925)
      ·
        refine ⟨18525748711082543831443111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98803993125773567101029925 18525748711082543831443111)
        ·
          refine ⟨27788623066623815747164667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18525748711082543831443111 27788623066623815747164667)
          ·
            refine ⟨41682934599935723620747001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27788623066623815747164667 41682934599935723620747001)
            ·
              refine ⟨31262200949951792715560251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41682934599935723620747001 31262200949951792715560251)
              ·
                refine ⟨46893301424927689073340377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31262200949951792715560251 46893301424927689073340377)
                ·
                  refine ⟨35169976068695766805005283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46893301424927689073340377 35169976068695766805005283)
                  ·
                    refine ⟨52754964103043650207507925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35169976068695766805005283 52754964103043650207507925)
                    ·
                      refine ⟨1236444471165085551738467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52754964103043650207507925 1236444471165085551738467)
                      ·
                        rfl

theorem cell23_2407967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_2407967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2407967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2407967 prefixEnd_2407967 := by exact prefixLift 2407967
  have htrace : WordTrace (prefixWord ++ tailWord_2407967) baseStart_2407967 baseEnd_2407967 := by
    simpa [prefixWord, tailWord_2407967, baseEnd_2407967] using wordTrace_append hprefix tailTrace_2407967
  have hstable : (prefixWord ++ tailWord_2407967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2407967).length < 2 ^ (prefixWord ++ tailWord_2407967).sum := by decide
  have hdescent : baseEnd_2407967 < baseStart_2407967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2407967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408005 : List Nat := [1, 3, 1, 1, 1, 4, 5, 2, 1, 1, 3]
def baseStart_2408005 : Nat := 118140960795 + 2408005 * 2 ^ 59
def prefixEnd_2408005 : Nat := 4983230072969 + 3 ^ 40 * 2408005 * 2
def baseEnd_2408005 : Nat := 1236463983429956403063293

theorem tailTrace_2408005 : CollatzResearch.WordTrace tailWord_2408005 prefixEnd_2408005 1236463983429956403063293 := by
  unfold tailWord_2408005
  simp only [CollatzResearch.WordTrace]
  refine ⟨87827157641216614357465469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58551438427477742904976979 87827157641216614357465469)
  ·
    refine ⟨32935184115456230384049551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87827157641216614357465469 32935184115456230384049551)
    ·
      refine ⟨49402776173184345576074327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32935184115456230384049551 49402776173184345576074327)
      ·
        refine ⟨74104164259776518364111491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49402776173184345576074327 74104164259776518364111491)
        ·
          refine ⟨111156246389664777546167237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74104164259776518364111491 111156246389664777546167237)
          ·
            refine ⟨20841796198062145789906357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111156246389664777546167237 20841796198062145789906357)
            ·
              refine ⟨1953918393568326167803721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20841796198062145789906357 1953918393568326167803721)
              ·
                refine ⟨1465438795176244625852791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1953918393568326167803721 1465438795176244625852791)
                ·
                  refine ⟨2198158192764366938779187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1465438795176244625852791 2198158192764366938779187)
                  ·
                    refine ⟨3297237289146550408168781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2198158192764366938779187 3297237289146550408168781)
                    ·
                      refine ⟨1236463983429956403063293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3297237289146550408168781 1236463983429956403063293)
                      ·
                        rfl

theorem cell23_2408005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 1, 1, 3].length) (baseStart_2408005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408005 prefixEnd_2408005 := by exact prefixLift 2408005
  have htrace : WordTrace (prefixWord ++ tailWord_2408005) baseStart_2408005 baseEnd_2408005 := by
    simpa [prefixWord, tailWord_2408005, baseEnd_2408005] using wordTrace_append hprefix tailTrace_2408005
  have hstable : (prefixWord ++ tailWord_2408005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408005).length < 2 ^ (prefixWord ++ tailWord_2408005).sum := by decide
  have hdescent : baseEnd_2408005 < baseStart_2408005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408014 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_2408014 : Nat := 118140960795 + 2408014 * 2 ^ 59
def prefixEnd_2408014 : Nat := 4983230072969 + 3 ^ 40 * 2408014 * 2
def baseEnd_2408014 : Nat := 1236468604755846867850751

theorem tailTrace_2408014 : CollatzResearch.WordTrace tailWord_2408014 prefixEnd_2408014 1236468604755846867850751 := by
  unfold tailWord_2408014
  simp only [CollatzResearch.WordTrace]
  refine ⟨10978435737273001111817887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58551657265456005929695397 10978435737273001111817887)
  ·
    refine ⟨16467653605909501667726831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10978435737273001111817887 16467653605909501667726831)
    ·
      refine ⟨24701480408864252501590247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16467653605909501667726831 24701480408864252501590247)
      ·
        refine ⟨37052220613296378752385371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24701480408864252501590247 37052220613296378752385371)
        ·
          refine ⟨55578330919944568128578057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37052220613296378752385371 55578330919944568128578057)
          ·
            refine ⟨41683748189958426096433543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55578330919944568128578057 41683748189958426096433543)
            ·
              refine ⟨62525622284937639144650315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41683748189958426096433543 62525622284937639144650315)
              ·
                refine ⟨93788433427406458716975473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62525622284937639144650315 93788433427406458716975473)
                ·
                  refine ⟨70341325070554844037731605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93788433427406458716975473 70341325070554844037731605)
                  ·
                    refine ⟨3297249612682258314268669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70341325070554844037731605 3297249612682258314268669)
                    ·
                      refine ⟨1236468604755846867850751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3297249612682258314268669 1236468604755846867850751)
                      ·
                        rfl

theorem cell23_2408014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_2408014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408014 prefixEnd_2408014 := by exact prefixLift 2408014
  have htrace : WordTrace (prefixWord ++ tailWord_2408014) baseStart_2408014 baseEnd_2408014 := by
    simpa [prefixWord, tailWord_2408014, baseEnd_2408014] using wordTrace_append hprefix tailTrace_2408014
  have hstable : (prefixWord ++ tailWord_2408014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408014).length < 2 ^ (prefixWord ++ tailWord_2408014).sum := by decide
  have hdescent : baseEnd_2408014 < baseStart_2408014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408024 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_2408024 : Nat := 118140960795 + 2408024 * 2 ^ 59
def prefixEnd_2408024 : Nat := 4983230072969 + 3 ^ 40 * 2408024 * 2
def baseEnd_2408024 : Nat := 1236473739562391828725705

theorem tailTrace_2408024 : CollatzResearch.WordTrace tailWord_2408024 prefixEnd_2408024 1236473739562391828725705 := by
  unfold tailWord_2408024
  simp only [CollatzResearch.WordTrace]
  refine ⟨43913925314073890301203563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58551900418765187068271417 43913925314073890301203563)
  ·
    refine ⟨65870887971110835451805345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43913925314073890301203563 65870887971110835451805345)
    ·
      refine ⟨49403165978333126588854009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65870887971110835451805345 49403165978333126588854009)
      ·
        refine ⟨37052374483749844941640507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49403165978333126588854009 37052374483749844941640507)
        ·
          refine ⟨55578561725624767412460761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37052374483749844941640507 55578561725624767412460761)
          ·
            refine ⟨41683921294218575559345571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55578561725624767412460761 41683921294218575559345571)
            ·
              refine ⟨62525881941327863339018357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41683921294218575559345571 62525881941327863339018357)
              ·
                refine ⟨5861801431999487188032971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62525881941327863339018357 5861801431999487188032971)
                ·
                  refine ⟨8792702147999230782049457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5861801431999487188032971 8792702147999230782049457)
                  ·
                    refine ⟨6594526610999423086537093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8792702147999230782049457 6594526610999423086537093)
                    ·
                      refine ⟨1236473739562391828725705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6594526610999423086537093 1236473739562391828725705)
                      ·
                        rfl

theorem cell23_2408024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_2408024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408024 prefixEnd_2408024 := by exact prefixLift 2408024
  have htrace : WordTrace (prefixWord ++ tailWord_2408024) baseStart_2408024 baseEnd_2408024 := by
    simpa [prefixWord, tailWord_2408024, baseEnd_2408024] using wordTrace_append hprefix tailTrace_2408024
  have hstable : (prefixWord ++ tailWord_2408024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408024).length < 2 ^ (prefixWord ++ tailWord_2408024).sum := by decide
  have hdescent : baseEnd_2408024 < baseStart_2408024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408028 : List Nat := [2, 2, 4, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_2408028 : Nat := 118140960795 + 2408028 * 2 ^ 59
def prefixEnd_2408028 : Nat := 4983230072969 + 3 ^ 40 * 2408028 * 2
def baseEnd_2408028 : Nat := 1236475793485009813075687

theorem tailTrace_2408028 : CollatzResearch.WordTrace tailWord_2408028 prefixEnd_2408028 1236475793485009813075687 := by
  unfold tailWord_2408028
  simp only [CollatzResearch.WordTrace]
  refine ⟨43913998260066644642776369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58551997680088859523701825 43913998260066644642776369)
  ·
    refine ⟨32935498695049983482082277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43913998260066644642776369 32935498695049983482082277)
    ·
      refine ⟨6175406005321871902890427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32935498695049983482082277 6175406005321871902890427)
      ·
        refine ⟨9263109007982807854335641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6175406005321871902890427 9263109007982807854335641)
        ·
          refine ⟨6947331755987105890751731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9263109007982807854335641 6947331755987105890751731)
          ·
            refine ⟨10420997633980658836127597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6947331755987105890751731 10420997633980658836127597)
            ·
              refine ⟨3907874112742747063547849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10420997633980658836127597 3907874112742747063547849)
              ·
                refine ⟨2930905584557060297660887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3907874112742747063547849 2930905584557060297660887)
                ·
                  refine ⟨4396358376835590446491331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930905584557060297660887 4396358376835590446491331)
                  ·
                    refine ⟨6594537565253385669736997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4396358376835590446491331 6594537565253385669736997)
                    ·
                      refine ⟨1236475793485009813075687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6594537565253385669736997 1236475793485009813075687)
                      ·
                        rfl

theorem cell23_2408028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_2408028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408028 prefixEnd_2408028 := by exact prefixLift 2408028
  have htrace : WordTrace (prefixWord ++ tailWord_2408028) baseStart_2408028 baseEnd_2408028 := by
    simpa [prefixWord, tailWord_2408028, baseEnd_2408028] using wordTrace_append hprefix tailTrace_2408028
  have hstable : (prefixWord ++ tailWord_2408028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408028).length < 2 ^ (prefixWord ++ tailWord_2408028).sum := by decide
  have hdescent : baseEnd_2408028 < baseStart_2408028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408045 : List Nat := [1, 5, 1, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_2408045 : Nat := 118140960795 + 2408045 * 2 ^ 59
def prefixEnd_2408045 : Nat := 4983230072969 + 3 ^ 40 * 2408045 * 2
def baseEnd_2408045 : Nat := 1236484522656136246563109

theorem tailTrace_2408045 : CollatzResearch.WordTrace tailWord_2408045 prefixEnd_2408045 1236484522656136246563109 := by
  unfold tailWord_2408045
  simp only [CollatzResearch.WordTrace]
  refine ⟨87828616561071701188921589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58552411040714467459281059 87828616561071701188921589)
  ·
    refine ⟨8233932802600471986461399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87828616561071701188921589 8233932802600471986461399)
    ·
      refine ⟨12350899203900707979692099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8233932802600471986461399 12350899203900707979692099)
      ·
        refine ⟨18526348805851061969538149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12350899203900707979692099 18526348805851061969538149)
        ·
          refine ⟨3473690401097074119288403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18526348805851061969538149 3473690401097074119288403)
          ·
            refine ⟨5210535601645611178932605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3473690401097074119288403 5210535601645611178932605)
            ·
              refine ⟨1953950850617104192099727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5210535601645611178932605 1953950850617104192099727)
              ·
                refine ⟨2930926275925656288149591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1953950850617104192099727 2930926275925656288149591)
                ·
                  refine ⟨4396389413888484432224387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930926275925656288149591 4396389413888484432224387)
                  ·
                    refine ⟨6594584120832726648336581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4396389413888484432224387 6594584120832726648336581)
                    ·
                      refine ⟨1236484522656136246563109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6594584120832726648336581 1236484522656136246563109)
                      ·
                        rfl

theorem cell23_2408045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_2408045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408045 prefixEnd_2408045 := by exact prefixLift 2408045
  have htrace : WordTrace (prefixWord ++ tailWord_2408045) baseStart_2408045 baseEnd_2408045 := by
    simpa [prefixWord, tailWord_2408045, baseEnd_2408045] using wordTrace_append hprefix tailTrace_2408045
  have hstable : (prefixWord ++ tailWord_2408045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408045).length < 2 ^ (prefixWord ++ tailWord_2408045).sum := by decide
  have hdescent : baseEnd_2408045 < baseStart_2408045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408068 : List Nat := [2, 3, 2, 1, 5, 1, 1, 8]
def baseStart_2408068 : Nat := 118140960795 + 2408068 * 2 ^ 59
def prefixEnd_2408068 : Nat := 4983230072969 + 3 ^ 40 * 2408068 * 2
def baseEnd_2408068 : Nat := 45796160470784802095389

theorem tailTrace_2408068 : CollatzResearch.WordTrace tailWord_2408068 prefixEnd_2408068 45796160470784802095389 := by
  unfold tailWord_2408068
  simp only [CollatzResearch.WordTrace]
  refine ⟨43914727719994188058504429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58552970293325584078005905 43914727719994188058504429)
  ·
    refine ⟨16468022894997820521939161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43914727719994188058504429 16468022894997820521939161)
    ·
      refine ⟨12351017171248365391454371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16468022894997820521939161 12351017171248365391454371)
      ·
        refine ⟨18526525756872548087181557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12351017171248365391454371 18526525756872548087181557)
        ·
          refine ⟨1736861789706801383173271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18526525756872548087181557 1736861789706801383173271)
          ·
            refine ⟨2605292684560202074759907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736861789706801383173271 2605292684560202074759907)
            ·
              refine ⟨3907939026840303112139861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605292684560202074759907 3907939026840303112139861)
              ·
                refine ⟨45796160470784802095389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3907939026840303112139861 45796160470784802095389)
                ·
                  rfl

theorem cell23_2408068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 8].length) (baseStart_2408068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408068 prefixEnd_2408068 := by exact prefixLift 2408068
  have htrace : WordTrace (prefixWord ++ tailWord_2408068) baseStart_2408068 baseEnd_2408068 := by
    simpa [prefixWord, tailWord_2408068, baseEnd_2408068] using wordTrace_append hprefix tailTrace_2408068
  have hstable : (prefixWord ++ tailWord_2408068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408068).length < 2 ^ (prefixWord ++ tailWord_2408068).sum := by decide
  have hdescent : baseEnd_2408068 < baseStart_2408068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408078 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_2408078 : Nat := 118140960795 + 2408078 * 2 ^ 59
def prefixEnd_2408078 : Nat := 4983230072969 + 3 ^ 40 * 2408078 * 2
def baseEnd_2408078 : Nat := 1236501467517734617450457

theorem tailTrace_2408078 : CollatzResearch.WordTrace tailWord_2408078 prefixEnd_2408078 1236501467517734617450457 := by
  unfold tailWord_2408078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10978727521244018478109111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58553213446634765216581925 10978727521244018478109111)
  ·
    refine ⟨16468091281866027717163667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10978727521244018478109111 16468091281866027717163667)
    ·
      refine ⟨24702136922799041575745501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16468091281866027717163667 24702136922799041575745501)
      ·
        refine ⟨9263301346049640590904563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24702136922799041575745501 9263301346049640590904563)
        ·
          refine ⟨13894952019074460886356845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9263301346049640590904563 13894952019074460886356845)
          ·
            refine ⟨5210607007152922832383817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13894952019074460886356845 5210607007152922832383817)
            ·
              refine ⟨3907955255364692124287863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5210607007152922832383817 3907955255364692124287863)
              ·
                refine ⟨5861932883047038186431795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3907955255364692124287863 5861932883047038186431795)
                ·
                  refine ⟨8792899324570557279647693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5861932883047038186431795 8792899324570557279647693)
                  ·
                    refine ⟨3297337246713958979867885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8792899324570557279647693 3297337246713958979867885)
                    ·
                      refine ⟨1236501467517734617450457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3297337246713958979867885 1236501467517734617450457)
                      ·
                        rfl

theorem cell23_2408078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_2408078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408078 prefixEnd_2408078 := by exact prefixLift 2408078
  have htrace : WordTrace (prefixWord ++ tailWord_2408078) baseStart_2408078 baseEnd_2408078 := by
    simpa [prefixWord, tailWord_2408078, baseEnd_2408078] using wordTrace_append hprefix tailTrace_2408078
  have hstable : (prefixWord ++ tailWord_2408078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408078).length < 2 ^ (prefixWord ++ tailWord_2408078).sum := by decide
  have hdescent : baseEnd_2408078 < baseStart_2408078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408088 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 3, 3, 2]
def baseStart_2408088 : Nat := 118140960795 + 2408088 * 2 ^ 59
def prefixEnd_2408088 : Nat := 4983230072969 + 3 ^ 40 * 2408088 * 2
def baseEnd_2408088 : Nat := 1236506602324279578325411

theorem tailTrace_2408088 : CollatzResearch.WordTrace tailWord_2408088 prefixEnd_2408088 1236506602324279578325411 := by
  unfold tailWord_2408088
  simp only [CollatzResearch.WordTrace]
  refine ⟨43915092449957959766368459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58553456599943946355157945 43915092449957959766368459)
  ·
    refine ⟨65872638674936939649552689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43915092449957959766368459 65872638674936939649552689)
    ·
      refine ⟨49404479006202704737164517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65872638674936939649552689 49404479006202704737164517)
      ·
        refine ⟨9263339813663007138218347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49404479006202704737164517 9263339813663007138218347)
        ·
          refine ⟨13895009720494510707327521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9263339813663007138218347 13895009720494510707327521)
          ·
            refine ⟨10421257290370883030495641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13895009720494510707327521 10421257290370883030495641)
            ·
              refine ⟨7815942967778162272871731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10421257290370883030495641 7815942967778162272871731)
              ·
                refine ⟨11723914451667243409307597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7815942967778162272871731 11723914451667243409307597)
                ·
                  refine ⟨4396467919375216278490349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11723914451667243409307597 4396467919375216278490349)
                  ·
                    refine ⟨1648675469765706104433881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4396467919375216278490349 1648675469765706104433881)
                    ·
                      refine ⟨1236506602324279578325411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648675469765706104433881 1236506602324279578325411)
                      ·
                        rfl

theorem cell23_2408088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_2408088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408088 prefixEnd_2408088 := by exact prefixLift 2408088
  have htrace : WordTrace (prefixWord ++ tailWord_2408088) baseStart_2408088 baseEnd_2408088 := by
    simpa [prefixWord, tailWord_2408088, baseEnd_2408088] using wordTrace_append hprefix tailTrace_2408088
  have hstable : (prefixWord ++ tailWord_2408088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408088).length < 2 ^ (prefixWord ++ tailWord_2408088).sum := by decide
  have hdescent : baseEnd_2408088 < baseStart_2408088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408178 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 2, 5, 2]
def baseStart_2408178 : Nat := 118140960795 + 2408178 * 2 ^ 59
def prefixEnd_2408178 : Nat := 4983230072969 + 3 ^ 40 * 2408178 * 2
def baseEnd_2408178 : Nat := 1236552815583184226199997

theorem tailTrace_2408178 : CollatzResearch.WordTrace tailWord_2408178 prefixEnd_2408178 1236552815583184226199997 := by
  unfold tailWord_2408178
  simp only [CollatzResearch.WordTrace]
  refine ⟨21958366867397466225878297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58555644979726576602342125 21958366867397466225878297)
  ·
    refine ⟨16468775150548099669408723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21958366867397466225878297 16468775150548099669408723)
    ·
      refine ⟨24703162725822149504113085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16468775150548099669408723 24703162725822149504113085)
      ·
        refine ⟨9263686022183306064042407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24703162725822149504113085 9263686022183306064042407)
        ·
          refine ⟨13895529033274959096063611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9263686022183306064042407 13895529033274959096063611)
          ·
            refine ⟨20843293549912438644095417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13895529033274959096063611 20843293549912438644095417)
            ·
              refine ⟨15632470162434328983071563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20843293549912438644095417 15632470162434328983071563)
              ·
                refine ⟨23448705243651493474607345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15632470162434328983071563 23448705243651493474607345)
                ·
                  refine ⟨17586528932738620105955509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23448705243651493474607345 17586528932738620105955509)
                  ·
                    refine ⟨1648737087444245634933329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17586528932738620105955509 1648737087444245634933329)
                    ·
                      refine ⟨1236552815583184226199997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648737087444245634933329 1236552815583184226199997)
                      ·
                        rfl

theorem cell23_2408178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_2408178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408178 prefixEnd_2408178 := by exact prefixLift 2408178
  have htrace : WordTrace (prefixWord ++ tailWord_2408178) baseStart_2408178 baseEnd_2408178 := by
    simpa [prefixWord, tailWord_2408178, baseEnd_2408178] using wordTrace_append hprefix tailTrace_2408178
  have hstable : (prefixWord ++ tailWord_2408178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408178).length < 2 ^ (prefixWord ++ tailWord_2408178).sum := by decide
  have hdescent : baseEnd_2408178 < baseStart_2408178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408184 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 2, 8]
def baseStart_2408184 : Nat := 118140960795 + 2408184 * 2 ^ 59
def prefixEnd_2408184 : Nat := 4983230072969 + 3 ^ 40 * 2408184 * 2
def baseEnd_2408184 : Nat := 412185298822370400908323

theorem tailTrace_2408184 : CollatzResearch.WordTrace tailWord_2408184 prefixEnd_2408184 412185298822370400908323 := by
  unfold tailWord_2408184
  simp only [CollatzResearch.WordTrace]
  refine ⟨43916843153784063964115803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58555790871712085285487737 43916843153784063964115803)
  ·
    refine ⟨65875264730676095946173705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43916843153784063964115803 65875264730676095946173705)
    ·
      refine ⟨49406448548007071959630279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65875264730676095946173705 49406448548007071959630279)
      ·
        refine ⟨74109672822010607939445419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49406448548007071959630279 74109672822010607939445419)
        ·
          refine ⟨111164509233015911909168129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74109672822010607939445419 111164509233015911909168129)
          ·
            refine ⟨83373381924761933931876097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111164509233015911909168129 83373381924761933931876097)
            ·
              refine ⟨62530036443571450448907073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83373381924761933931876097 62530036443571450448907073)
              ·
                refine ⟨46897527332678587836680305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62530036443571450448907073 46897527332678587836680305)
                ·
                  refine ⟨35173145499508940877510229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46897527332678587836680305 35173145499508940877510229)
                  ·
                    refine ⟨412185298822370400908323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35173145499508940877510229 412185298822370400908323)
                    ·
                      rfl

theorem cell23_2408184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_2408184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408184 prefixEnd_2408184 := by exact prefixLift 2408184
  have htrace : WordTrace (prefixWord ++ tailWord_2408184) baseStart_2408184 baseEnd_2408184 := by
    simpa [prefixWord, tailWord_2408184, baseEnd_2408184] using wordTrace_append hprefix tailTrace_2408184
  have hstable : (prefixWord ++ tailWord_2408184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408184).length < 2 ^ (prefixWord ++ tailWord_2408184).sum := by decide
  have hdescent : baseEnd_2408184 < baseStart_2408184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408201 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 5, 4]
def baseStart_2408201 : Nat := 118140960795 + 2408201 * 2 ^ 59
def prefixEnd_2408201 : Nat := 4983230072969 + 3 ^ 40 * 2408201 * 2
def baseEnd_2408201 : Nat := 412188208546079212070797

theorem tailTrace_2408201 : CollatzResearch.WordTrace tailWord_2408201 prefixEnd_2408201 412188208546079212070797 := by
  unfold tailWord_2408201
  simp only [CollatzResearch.WordTrace]
  refine ⟨87834306348506539831600457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58556204232337693221066971 87834306348506539831600457)
  ·
    refine ⟨65875729761379904873700343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87834306348506539831600457 65875729761379904873700343)
    ·
      refine ⟨98813594642069857310550515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65875729761379904873700343 98813594642069857310550515)
      ·
        refine ⟨148220391963104785965825773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98813594642069857310550515 148220391963104785965825773)
        ·
          refine ⟨55582646986164294737184665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148220391963104785965825773 55582646986164294737184665)
          ·
            refine ⟨41686985239623221052888499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55582646986164294737184665 41686985239623221052888499)
            ·
              refine ⟨62530477859434831579332749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41686985239623221052888499 62530477859434831579332749)
              ·
                refine ⟨23448929197288061842249781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62530477859434831579332749 23448929197288061842249781)
                ·
                  refine ⟨2198337112245755797710917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23448929197288061842249781 2198337112245755797710917)
                  ·
                    refine ⟨412188208546079212070797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2198337112245755797710917 412188208546079212070797)
                    ·
                      rfl

theorem cell23_2408201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 4].length) (baseStart_2408201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408201 prefixEnd_2408201 := by exact prefixLift 2408201
  have htrace : WordTrace (prefixWord ++ tailWord_2408201) baseStart_2408201 baseEnd_2408201 := by
    simpa [prefixWord, tailWord_2408201, baseEnd_2408201] using wordTrace_append hprefix tailTrace_2408201
  have hstable : (prefixWord ++ tailWord_2408201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408201).length < 2 ^ (prefixWord ++ tailWord_2408201).sum := by decide
  have hdescent : baseEnd_2408201 < baseStart_2408201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408261 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_2408261 : Nat := 118140960795 + 2408261 * 2 ^ 59
def prefixEnd_2408261 : Nat := 4983230072969 + 3 ^ 40 * 2408261 * 2
def baseEnd_2408261 : Nat := 412198478159169133820705

theorem tailTrace_2408261 : CollatzResearch.WordTrace tailWord_2408261 prefixEnd_2408261 412198478159169133820705 := by
  unfold tailWord_2408261
  simp only [CollatzResearch.WordTrace]
  refine ⟨87836494728289170078784637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58557663152192780052523091 87836494728289170078784637)
  ·
    refine ⟨32938685523108438779544239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87836494728289170078784637 32938685523108438779544239)
    ·
      refine ⟨49408028284662658169316359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32938685523108438779544239 49408028284662658169316359)
      ·
        refine ⟨74112042426993987253974539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49408028284662658169316359 74112042426993987253974539)
        ·
          refine ⟨111168063640490980880961809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74112042426993987253974539 111168063640490980880961809)
          ·
            refine ⟨83376047730368235660721357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111168063640490980880961809 83376047730368235660721357)
            ·
              refine ⟨31266017898888088372770509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83376047730368235660721357 31266017898888088372770509)
              ·
                refine ⟨11724756712083033139788941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31266017898888088372770509 11724756712083033139788941)
                ·
                  refine ⟨4396783767031137427420853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11724756712083033139788941 4396783767031137427420853)
                  ·
                    refine ⟨412198478159169133820705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4396783767031137427420853 412198478159169133820705)
                    ·
                      rfl

theorem cell23_2408261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_2408261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408261 prefixEnd_2408261 := by exact prefixLift 2408261
  have htrace : WordTrace (prefixWord ++ tailWord_2408261) baseStart_2408261 baseEnd_2408261 := by
    simpa [prefixWord, tailWord_2408261, baseEnd_2408261] using wordTrace_append hprefix tailTrace_2408261
  have hstable : (prefixWord ++ tailWord_2408261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408261).length < 2 ^ (prefixWord ++ tailWord_2408261).sum := by decide
  have hdescent : baseEnd_2408261 < baseStart_2408261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408262 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2408262 : Nat := 118140960795 + 2408262 * 2 ^ 59
def prefixEnd_2408262 : Nat := 4983230072969 + 3 ^ 40 * 2408262 * 2
def baseEnd_2408262 : Nat := 1236595947958161897549611

theorem tailTrace_2408262 : CollatzResearch.WordTrace tailWord_2408262 prefixEnd_2408262 1236595947958161897549611 := by
  unfold tailWord_2408262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2744891600040173351549095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58557687467523698166380693 2744891600040173351549095)
  ·
    refine ⟨4117337400060260027323643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2744891600040173351549095 4117337400060260027323643)
    ·
      refine ⟨6176006100090390040985465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4117337400060260027323643 6176006100090390040985465)
      ·
        refine ⟨4632004575067792530739099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6176006100090390040985465 4632004575067792530739099)
        ·
          refine ⟨6948006862601688796108649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4632004575067792530739099 6948006862601688796108649)
          ·
            refine ⟨5211005146951266597081487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6948006862601688796108649 5211005146951266597081487)
            ·
              refine ⟨7816507720426899895622231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5211005146951266597081487 7816507720426899895622231)
              ·
                refine ⟨11724761580640349843433347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7816507720426899895622231 11724761580640349843433347)
                ·
                  refine ⟨17587142370960524765150021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11724761580640349843433347 17587142370960524765150021)
                  ·
                    refine ⟨3297589194555098393465629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17587142370960524765150021 3297589194555098393465629)
                    ·
                      refine ⟨1236595947958161897549611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3297589194555098393465629 1236595947958161897549611)
                      ·
                        rfl

theorem cell23_2408262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2408262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408262 prefixEnd_2408262 := by exact prefixLift 2408262
  have htrace : WordTrace (prefixWord ++ tailWord_2408262) baseStart_2408262 baseEnd_2408262 := by
    simpa [prefixWord, tailWord_2408262, baseEnd_2408262] using wordTrace_append hprefix tailTrace_2408262
  have hstable : (prefixWord ++ tailWord_2408262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408262).length < 2 ^ (prefixWord ++ tailWord_2408262).sum := by decide
  have hdescent : baseEnd_2408262 < baseStart_2408262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408269 : List Nat := [1, 6, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_2408269 : Nat := 118140960795 + 2408269 * 2 ^ 59
def prefixEnd_2408269 : Nat := 4983230072969 + 3 ^ 40 * 2408269 * 2
def baseEnd_2408269 : Nat := 412199847440914456720693

theorem tailTrace_2408269 : CollatzResearch.WordTrace tailWord_2408269 prefixEnd_2408269 412199847440914456720693 := by
  unfold tailWord_2408269
  simp only [CollatzResearch.WordTrace]
  refine ⟨87836786512260187445075861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58557857674840124963383907 87836786512260187445075861)
  ·
    refine ⟨4117349367762196286487931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87836786512260187445075861 4117349367762196286487931)
    ·
      refine ⟨6176024051643294429731897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4117349367762196286487931 6176024051643294429731897)
      ·
        refine ⟨4632018038732470822298923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6176024051643294429731897 4632018038732470822298923)
        ·
          refine ⟨6948027058098706233448385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4632018038732470822298923 6948027058098706233448385)
          ·
            refine ⟨5211020293574029675086289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6948027058098706233448385 5211020293574029675086289)
            ·
              refine ⟨3908265220180522256314717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5211020293574029675086289 3908265220180522256314717)
              ·
                refine ⟨1465599457567695846118019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3908265220180522256314717 1465599457567695846118019)
                ·
                  refine ⟨2198399186351543769177029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1465599457567695846118019 2198399186351543769177029)
                  ·
                    refine ⟨412199847440914456720693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2198399186351543769177029 412199847440914456720693)
                    ·
                      rfl

theorem cell23_2408269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_2408269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408269 prefixEnd_2408269 := by exact prefixLift 2408269
  have htrace : WordTrace (prefixWord ++ tailWord_2408269) baseStart_2408269 baseEnd_2408269 := by
    simpa [prefixWord, tailWord_2408269, baseEnd_2408269] using wordTrace_append hprefix tailTrace_2408269
  have hstable : (prefixWord ++ tailWord_2408269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408269).length < 2 ^ (prefixWord ++ tailWord_2408269).sum := by decide
  have hdescent : baseEnd_2408269 < baseStart_2408269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408292 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_2408292 : Nat := 118140960795 + 2408292 * 2 ^ 59
def prefixEnd_2408292 : Nat := 4983230072969 + 3 ^ 40 * 2408292 * 2
def baseEnd_2408292 : Nat := 1236611352377796780174473

theorem tailTrace_2408292 : CollatzResearch.WordTrace tailWord_2408292 prefixEnd_2408292 1236611352377796780174473 := by
  unfold tailWord_2408292
  simp only [CollatzResearch.WordTrace]
  refine ⟨43918812695588431186581565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58558416927451241582108753 43918812695588431186581565)
  ·
    refine ⟨16469554760845661694968087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43918812695588431186581565 16469554760845661694968087)
    ·
      refine ⟨24704332141268492542452131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16469554760845661694968087 24704332141268492542452131)
      ·
        refine ⟨37056498211902738813678197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24704332141268492542452131 37056498211902738813678197)
        ·
          refine ⟨3474046707365881763782331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37056498211902738813678197 3474046707365881763782331)
          ·
            refine ⟨5211070061048822645673497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3474046707365881763782331 5211070061048822645673497)
            ·
              refine ⟨3908302545786616984255123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5211070061048822645673497 3908302545786616984255123)
              ·
                refine ⟨5862453818679925476382685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3908302545786616984255123 5862453818679925476382685)
                ·
                  refine ⟨2198420182004972053643507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5862453818679925476382685 2198420182004972053643507)
                  ·
                    refine ⟨3297630273007458080465261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2198420182004972053643507 3297630273007458080465261)
                    ·
                      refine ⟨1236611352377796780174473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3297630273007458080465261 1236611352377796780174473)
                      ·
                        rfl

theorem cell23_2408292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_2408292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408292 prefixEnd_2408292 := by exact prefixLift 2408292
  have htrace : WordTrace (prefixWord ++ tailWord_2408292) baseStart_2408292 baseEnd_2408292 := by
    simpa [prefixWord, tailWord_2408292, baseEnd_2408292] using wordTrace_append hprefix tailTrace_2408292
  have hstable : (prefixWord ++ tailWord_2408292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408292).length < 2 ^ (prefixWord ++ tailWord_2408292).sum := by decide
  have hdescent : baseEnd_2408292 < baseStart_2408292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408338 : List Nat := [3, 2, 3, 2, 1, 1, 11]
def baseStart_2408338 : Nat := 118140960795 + 2408338 * 2 ^ 59
def prefixEnd_2408338 : Nat := 4983230072969 + 3 ^ 40 * 2408338 * 2
def baseEnd_2408338 : Nat := 15267098425776587656781

theorem tailTrace_2408338 : CollatzResearch.WordTrace tailWord_2408338 prefixEnd_2408338 15267098425776587656781 := by
  unfold tailWord_2408338
  simp only [CollatzResearch.WordTrace]
  refine ⟨21959825787252553057334417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58559535432673474819558445 21959825787252553057334417)
  ·
    refine ⟨16469869340439414793000813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21959825787252553057334417 16469869340439414793000813)
    ·
      refine ⟨6176201002664780547375305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16469869340439414793000813 6176201002664780547375305)
      ·
        refine ⟨4632150751998585410531479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6176201002664780547375305 4632150751998585410531479)
        ·
          refine ⟨6948226127997878115797219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4632150751998585410531479 6948226127997878115797219)
          ·
            refine ⟨10422339191996817173695829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6948226127997878115797219 10422339191996817173695829)
            ·
              refine ⟨15267098425776587656781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10422339191996817173695829 15267098425776587656781)
              ·
                rfl

theorem cell23_2408338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 11].length) (baseStart_2408338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408338 prefixEnd_2408338 := by exact prefixLift 2408338
  have htrace : WordTrace (prefixWord ++ tailWord_2408338) baseStart_2408338 baseEnd_2408338 := by
    simpa [prefixWord, tailWord_2408338, baseEnd_2408338] using wordTrace_append hprefix tailTrace_2408338
  have hstable : (prefixWord ++ tailWord_2408338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408338).length < 2 ^ (prefixWord ++ tailWord_2408338).sum := by decide
  have hdescent : baseEnd_2408338 < baseStart_2408338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408349 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_2408349 : Nat := 118140960795 + 2408349 * 2 ^ 59
def prefixEnd_2408349 : Nat := 4983230072969 + 3 ^ 40 * 2408349 * 2
def baseEnd_2408349 : Nat := 1236640620775103057161711

theorem tailTrace_2408349 : CollatzResearch.WordTrace tailWord_2408349 prefixEnd_2408349 1236640620775103057161711 := by
  unfold tailWord_2408349
  simp only [CollatzResearch.WordTrace]
  refine ⟨87839704351970361107988101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58559802901313574071992067 87839704351970361107988101)
  ·
    refine ⟨16469944565994442707747769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87839704351970361107988101 16469944565994442707747769)
    ·
      refine ⟨12352458424495832030810827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16469944565994442707747769 12352458424495832030810827)
      ·
        refine ⟨18528687636743748046216241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12352458424495832030810827 18528687636743748046216241)
        ·
          refine ⟨13896515727557811034662181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18528687636743748046216241 13896515727557811034662181)
          ·
            refine ⟨2605596698917089568999159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13896515727557811034662181 2605596698917089568999159)
            ·
              refine ⟨3908395048375634353498739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605596698917089568999159 3908395048375634353498739)
              ·
                refine ⟨5862592572563451530248109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3908395048375634353498739 5862592572563451530248109)
                ·
                  refine ⟨2198472214711294323843041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5862592572563451530248109 2198472214711294323843041)
                  ·
                    refine ⟨1648854161033470742882281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2198472214711294323843041 1648854161033470742882281)
                    ·
                      refine ⟨1236640620775103057161711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648854161033470742882281 1236640620775103057161711)
                      ·
                        rfl

theorem cell23_2408349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_2408349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408349 prefixEnd_2408349 := by exact prefixLift 2408349
  have htrace : WordTrace (prefixWord ++ tailWord_2408349) baseStart_2408349 baseEnd_2408349 := by
    simpa [prefixWord, tailWord_2408349, baseEnd_2408349] using wordTrace_append hprefix tailTrace_2408349
  have hstable : (prefixWord ++ tailWord_2408349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408349).length < 2 ^ (prefixWord ++ tailWord_2408349).sum := by decide
  have hdescent : baseEnd_2408349 < baseStart_2408349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408359 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 2, 4]
def baseStart_2408359 : Nat := 118140960795 + 2408359 * 2 ^ 59
def prefixEnd_2408359 : Nat := 4983230072969 + 3 ^ 40 * 2408359 * 2
def baseEnd_2408359 : Nat := 412215251860549339345555

theorem tailTrace_2408359 : CollatzResearch.WordTrace tailWord_2408359 prefixEnd_2408359 412215251860549339345555 := by
  unfold tailWord_2408359
  simp only [CollatzResearch.WordTrace]
  refine ⟨87840069081934132815852131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58560046054622755210568087 87840069081934132815852131)
  ·
    refine ⟨131760103622901199223778197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87840069081934132815852131 131760103622901199223778197)
    ·
      refine ⟨6176254857323493713614603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 131760103622901199223778197 6176254857323493713614603)
      ·
        refine ⟨9264382285985240570421905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6176254857323493713614603 9264382285985240570421905)
        ·
          refine ⟨6948286714488930427816429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9264382285985240570421905 6948286714488930427816429)
          ·
            refine ⟨2605607517933348910431161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6948286714488930427816429 2605607517933348910431161)
            ·
              refine ⟨1954205638450011682823371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2605607517933348910431161 1954205638450011682823371)
              ·
                refine ⟨2931308457675017524235057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954205638450011682823371 2931308457675017524235057)
                ·
                  refine ⟨2198481343256263143176293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2931308457675017524235057 2198481343256263143176293)
                  ·
                    refine ⟨412215251860549339345555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2198481343256263143176293 412215251860549339345555)
                    ·
                      rfl

theorem cell23_2408359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_2408359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408359 prefixEnd_2408359 := by exact prefixLift 2408359
  have htrace : WordTrace (prefixWord ++ tailWord_2408359) baseStart_2408359 baseEnd_2408359 := by
    simpa [prefixWord, tailWord_2408359, baseEnd_2408359] using wordTrace_append hprefix tailTrace_2408359
  have hstable : (prefixWord ++ tailWord_2408359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408359).length < 2 ^ (prefixWord ++ tailWord_2408359).sum := by decide
  have hdescent : baseEnd_2408359 < baseStart_2408359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408361 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_2408361 : Nat := 118140960795 + 2408361 * 2 ^ 59
def prefixEnd_2408361 : Nat := 4983230072969 + 3 ^ 40 * 2408361 * 2
def baseEnd_2408361 : Nat := 1236646782542957010211655

theorem tailTrace_2408361 : CollatzResearch.WordTrace tailWord_2408361 prefixEnd_2408361 1236646782542957010211655 := by
  unfold tailWord_2408361
  simp only [CollatzResearch.WordTrace]
  refine ⟨87840142027926887157424937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58560094685284591438283291 87840142027926887157424937)
  ·
    refine ⟨65880106520945165368068703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87840142027926887157424937 65880106520945165368068703)
    ·
      refine ⟨98820159781417748052103055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65880106520945165368068703 98820159781417748052103055)
      ·
        refine ⟨148230239672126622078154583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98820159781417748052103055 148230239672126622078154583)
        ·
          refine ⟨222345359508189933117231875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148230239672126622078154583 222345359508189933117231875)
          ·
            refine ⟨333518039262284899675847813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222345359508189933117231875 333518039262284899675847813)
            ·
              refine ⟨62534632361678418689221465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 333518039262284899675847813 62534632361678418689221465)
              ·
                refine ⟨46900974271258814016916099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62534632361678418689221465 46900974271258814016916099)
                ·
                  refine ⟨70351461406888221025374149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46900974271258814016916099 70351461406888221025374149)
                  ·
                    refine ⟨13190899013791541442257653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70351461406888221025374149 13190899013791541442257653)
                    ·
                      refine ⟨1236646782542957010211655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13190899013791541442257653 1236646782542957010211655)
                      ·
                        rfl

theorem cell23_2408361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_2408361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408361 prefixEnd_2408361 := by exact prefixLift 2408361
  have htrace : WordTrace (prefixWord ++ tailWord_2408361) baseStart_2408361 baseEnd_2408361 := by
    simpa [prefixWord, tailWord_2408361, baseEnd_2408361] using wordTrace_append hprefix tailTrace_2408361
  have hstable : (prefixWord ++ tailWord_2408361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408361).length < 2 ^ (prefixWord ++ tailWord_2408361).sum := by decide
  have hdescent : baseEnd_2408361 < baseStart_2408361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408398 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_2408398 : Nat := 118140960795 + 2408398 * 2 ^ 59
def prefixEnd_2408398 : Nat := 4983230072969 + 3 ^ 40 * 2408398 * 2
def baseEnd_2408398 : Nat := 412221927109057788482995

theorem tailTrace_2408398 : CollatzResearch.WordTrace tailWord_2408398 prefixEnd_2408398 412221927109057788482995 := by
  unfold tailWord_2408398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10980186441099105309565231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58560994352528561651014565 10980186441099105309565231)
  ·
    refine ⟨16470279661648657964347847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10980186441099105309565231 16470279661648657964347847)
    ·
      refine ⟨24705419492472986946521771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16470279661648657964347847 24705419492472986946521771)
      ·
        refine ⟨37058129238709480419782657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24705419492472986946521771 37058129238709480419782657)
        ·
          refine ⟨27793596929032110314836993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37058129238709480419782657 27793596929032110314836993)
          ·
            refine ⟨20845197696774082736127745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27793596929032110314836993 20845197696774082736127745)
            ·
              refine ⟨15633898272580562052095809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20845197696774082736127745 15633898272580562052095809)
              ·
                refine ⟨11725423704435421539071857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15633898272580562052095809 11725423704435421539071857)
                ·
                  refine ⟨8794067778326566154303893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11725423704435421539071857 8794067778326566154303893)
                  ·
                    refine ⟨412221927109057788482995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8794067778326566154303893 412221927109057788482995)
                    ·
                      rfl

theorem cell23_2408398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_2408398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408398 prefixEnd_2408398 := by exact prefixLift 2408398
  have htrace : WordTrace (prefixWord ++ tailWord_2408398) baseStart_2408398 baseEnd_2408398 := by
    simpa [prefixWord, tailWord_2408398, baseEnd_2408398] using wordTrace_append hprefix tailTrace_2408398
  have hstable : (prefixWord ++ tailWord_2408398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408398).length < 2 ^ (prefixWord ++ tailWord_2408398).sum := by decide
  have hdescent : baseEnd_2408398 < baseStart_2408398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408408 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 1, 6, 3]
def baseStart_2408408 : Nat := 118140960795 + 2408408 * 2 ^ 59
def prefixEnd_2408408 : Nat := 4983230072969 + 3 ^ 40 * 2408408 * 2
def baseEnd_2408408 : Nat := 1236670916133718326323939

theorem tailTrace_2408408 : CollatzResearch.WordTrace tailWord_2408408 prefixEnd_2408408 1236670916133718326323939 := by
  unfold tailWord_2408408
  simp only [CollatzResearch.WordTrace]
  refine ⟨43920928129378307092192939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58561237505837742789590585 43920928129378307092192939)
  ·
    refine ⟨65881392194067460638289409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43920928129378307092192939 65881392194067460638289409)
    ·
      refine ⟨49411044145550595478717057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65881392194067460638289409 49411044145550595478717057)
      ·
        refine ⟨37058283109162946609037793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49411044145550595478717057 37058283109162946609037793)
        ·
          refine ⟨27793712331872209956778345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37058283109162946609037793 27793712331872209956778345)
          ·
            refine ⟨20845284248904157467583759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27793712331872209956778345 20845284248904157467583759)
            ·
              refine ⟨31267926373356236201375639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20845284248904157467583759 31267926373356236201375639)
              ·
                refine ⟨46901889560034354302063459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31267926373356236201375639 46901889560034354302063459)
                ·
                  refine ⟨70352834340051531453095189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46901889560034354302063459 70352834340051531453095189)
                  ·
                    refine ⟨3297789109689915536863837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70352834340051531453095189 3297789109689915536863837)
                    ·
                      refine ⟨1236670916133718326323939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3297789109689915536863837 1236670916133718326323939)
                      ·
                        rfl

theorem cell23_2408408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_2408408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408408 prefixEnd_2408408 := by exact prefixLift 2408408
  have htrace : WordTrace (prefixWord ++ tailWord_2408408) baseStart_2408408 baseEnd_2408408 := by
    simpa [prefixWord, tailWord_2408408, baseEnd_2408408] using wordTrace_append hprefix tailTrace_2408408
  have hstable : (prefixWord ++ tailWord_2408408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408408).length < 2 ^ (prefixWord ++ tailWord_2408408).sum := by decide
  have hdescent : baseEnd_2408408 < baseStart_2408408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408445 : List Nat := [1, 4, 1, 1, 1, 2, 3, 5, 5]
def baseStart_2408445 : Nat := 118140960795 + 2408445 * 2 ^ 59
def prefixEnd_2408445 : Nat := 4983230072969 + 3 ^ 40 * 2408445 * 2
def baseEnd_2408445 : Nat := 137409990546437186840141

theorem tailTrace_2408445 : CollatzResearch.WordTrace tailWord_2408445 prefixEnd_2408445 137409990546437186840141 := by
  unfold tailWord_2408445
  simp only [CollatzResearch.WordTrace]
  refine ⟨87843205759622569503482789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58562137173081713002321859 87843205759622569503482789)
  ·
    refine ⟨16470601079929231781903023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87843205759622569503482789 16470601079929231781903023)
    ·
      refine ⟨24705901619893847672854535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16470601079929231781903023 24705901619893847672854535)
      ·
        refine ⟨37058852429840771509281803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24705901619893847672854535 37058852429840771509281803)
        ·
          refine ⟨55588278644761157263922705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37058852429840771509281803 55588278644761157263922705)
          ·
            refine ⟨41691208983570867947942029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55588278644761157263922705 41691208983570867947942029)
            ·
              refine ⟨15634203368839075480478261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41691208983570867947942029 15634203368839075480478261)
              ·
                refine ⟨1465706565828663326294837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15634203368839075480478261 1465706565828663326294837)
                ·
                  refine ⟨137409990546437186840141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1465706565828663326294837 137409990546437186840141)
                  ·
                    rfl

theorem cell23_2408445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_2408445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408445 prefixEnd_2408445 := by exact prefixLift 2408445
  have htrace : WordTrace (prefixWord ++ tailWord_2408445) baseStart_2408445 baseEnd_2408445 := by
    simpa [prefixWord, tailWord_2408445, baseEnd_2408445] using wordTrace_append hprefix tailTrace_2408445
  have hstable : (prefixWord ++ tailWord_2408445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408445).length < 2 ^ (prefixWord ++ tailWord_2408445).sum := by decide
  have hdescent : baseEnd_2408445 < baseStart_2408445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408455 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_2408455 : Nat := 118140960795 + 2408455 * 2 ^ 59
def prefixEnd_2408455 : Nat := 4983230072969 + 3 ^ 40 * 2408455 * 2
def baseEnd_2408455 : Nat := 1236695049724479642436223

theorem tailTrace_2408455 : CollatzResearch.WordTrace tailWord_2408455 prefixEnd_2408455 1236695049724479642436223 := by
  unfold tailWord_2408455
  simp only [CollatzResearch.WordTrace]
  refine ⟨87843570489586341211346819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58562380326390894140897879 87843570489586341211346819)
  ·
    refine ⟨131765355734379511817020229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87843570489586341211346819 131765355734379511817020229)
    ·
      refine ⟨24706004200196158465691293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131765355734379511817020229 24706004200196158465691293)
      ·
        refine ⟨9264751575073559424634235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24706004200196158465691293 9264751575073559424634235)
        ·
          refine ⟨13897127362610339136951353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9264751575073559424634235 13897127362610339136951353)
          ·
            refine ⟨10422845521957754352713515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13897127362610339136951353 10422845521957754352713515)
            ·
              refine ⟨15634268282936631529070273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10422845521957754352713515 15634268282936631529070273)
              ·
                refine ⟨11725701212202473646802705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15634268282936631529070273 11725701212202473646802705)
                ·
                  refine ⟨8794275909151855235102029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11725701212202473646802705 8794275909151855235102029)
                  ·
                    refine ⟨3297853465931945713163261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8794275909151855235102029 3297853465931945713163261)
                    ·
                      refine ⟨1236695049724479642436223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3297853465931945713163261 1236695049724479642436223)
                      ·
                        rfl

theorem cell23_2408455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_2408455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408455 prefixEnd_2408455 := by exact prefixLift 2408455
  have htrace : WordTrace (prefixWord ++ tailWord_2408455) baseStart_2408455 baseEnd_2408455 := by
    simpa [prefixWord, tailWord_2408455, baseEnd_2408455] using wordTrace_append hprefix tailTrace_2408455
  have hstable : (prefixWord ++ tailWord_2408455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408455).length < 2 ^ (prefixWord ++ tailWord_2408455).sum := by decide
  have hdescent : baseEnd_2408455 < baseStart_2408455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408495 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 4, 4, 2]
def baseStart_2408495 : Nat := 118140960795 + 2408495 * 2 ^ 59
def prefixEnd_2408495 : Nat := 4983230072969 + 3 ^ 40 * 2408495 * 2
def baseEnd_2408495 : Nat := 1236715588950659485936039

theorem tailTrace_2408495 : CollatzResearch.WordTrace tailWord_2408495 prefixEnd_2408495 1236715588950659485936039 := by
  unfold tailWord_2408495
  simp only [CollatzResearch.WordTrace]
  refine ⟨87845029409441428042802939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58563352939627618695201959 87845029409441428042802939)
  ·
    refine ⟨131767544114162142064204409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87845029409441428042802939 131767544114162142064204409)
    ·
      refine ⟨98825658085621606548153307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131767544114162142064204409 98825658085621606548153307)
      ·
        refine ⟨148238487128432409822229961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98825658085621606548153307 148238487128432409822229961)
        ·
          refine ⟨111178865346324307366672471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148238487128432409822229961 111178865346324307366672471)
          ·
            refine ⟨166768298019486461050008707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111178865346324307366672471 166768298019486461050008707)
            ·
              refine ⟨250152447029229691575013061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166768298019486461050008707 250152447029229691575013061)
              ·
                refine ⟨46903583817980567170314949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250152447029229691575013061 46903583817980567170314949)
                ·
                  refine ⟨8794421965871356344434053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46903583817980567170314949 8794421965871356344434053)
                  ·
                    refine ⟨1648954118600879314581385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8794421965871356344434053 1648954118600879314581385)
                    ·
                      refine ⟨1236715588950659485936039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1648954118600879314581385 1236715588950659485936039)
                      ·
                        rfl

theorem cell23_2408495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 4, 2].length) (baseStart_2408495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408495 prefixEnd_2408495 := by exact prefixLift 2408495
  have htrace : WordTrace (prefixWord ++ tailWord_2408495) baseStart_2408495 baseEnd_2408495 := by
    simpa [prefixWord, tailWord_2408495, baseEnd_2408495] using wordTrace_append hprefix tailTrace_2408495
  have hstable : (prefixWord ++ tailWord_2408495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408495).length < 2 ^ (prefixWord ++ tailWord_2408495).sum := by decide
  have hdescent : baseEnd_2408495 < baseStart_2408495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408585 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 4]
def baseStart_2408585 : Nat := 118140960795 + 2408585 * 2 ^ 59
def prefixEnd_2408585 : Nat := 4983230072969 + 3 ^ 40 * 2408585 * 2
def baseEnd_2408585 : Nat := 1236761802209564133810625

theorem tailTrace_2408585 : CollatzResearch.WordTrace tailWord_2408585 prefixEnd_2408585 1236761802209564133810625 := by
  unfold tailWord_2408585
  simp only [CollatzResearch.WordTrace]
  refine ⟨87848311979115373413579209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58565541319410248942386139 87848311979115373413579209)
  ·
    refine ⟨65886233984336530060184407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87848311979115373413579209 65886233984336530060184407)
    ·
      refine ⟨98829350976504795090276611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65886233984336530060184407 98829350976504795090276611)
      ·
        refine ⟨148244026464757192635414917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98829350976504795090276611 148244026464757192635414917)
        ·
          refine ⟨27795754962141973619140297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148244026464757192635414917 27795754962141973619140297)
          ·
            refine ⟨20846816221606480214355223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27795754962141973619140297 20846816221606480214355223)
            ·
              refine ⟨31270224332409720321532835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20846816221606480214355223 31270224332409720321532835)
              ·
                refine ⟨46905336498614580482299253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31270224332409720321532835 46905336498614580482299253)
                ·
                  refine ⟨4397375296745116920215555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46905336498614580482299253 4397375296745116920215555)
                  ·
                    refine ⟨6596062945117675380323333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4397375296745116920215555 6596062945117675380323333)
                    ·
                      refine ⟨1236761802209564133810625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6596062945117675380323333 1236761802209564133810625)
                      ·
                        rfl

theorem cell23_2408585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_2408585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408585 prefixEnd_2408585 := by exact prefixLift 2408585
  have htrace : WordTrace (prefixWord ++ tailWord_2408585) baseStart_2408585 baseEnd_2408585 := by
    simpa [prefixWord, tailWord_2408585, baseEnd_2408585] using wordTrace_append hprefix tailTrace_2408585
  have hstable : (prefixWord ++ tailWord_2408585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408585).length < 2 ^ (prefixWord ++ tailWord_2408585).sum := by decide
  have hdescent : baseEnd_2408585 < baseStart_2408585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408595 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 6, 4]
def baseStart_2408595 : Nat := 118140960795 + 2408595 * 2 ^ 59
def prefixEnd_2408595 : Nat := 4983230072969 + 3 ^ 40 * 2408595 * 2
def baseEnd_2408595 : Nat := 412255645672036364895193

theorem tailTrace_2408595 : CollatzResearch.WordTrace tailWord_2408595 prefixEnd_2408595 412255645672036364895193 := by
  unfold tailWord_2408595
  simp only [CollatzResearch.WordTrace]
  refine ⟨87848676709079145121443239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58565784472719430080962159 87848676709079145121443239)
  ·
    refine ⟨131773015063618717682164859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87848676709079145121443239 131773015063618717682164859)
    ·
      refine ⟨197659522595428076523247289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131773015063618717682164859 197659522595428076523247289)
      ·
        refine ⟨148244641946571057392435467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197659522595428076523247289 148244641946571057392435467)
        ·
          refine ⟨222366962919856586088653201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148244641946571057392435467 222366962919856586088653201)
          ·
            refine ⟨166775222189892439566489901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222366962919856586088653201 166775222189892439566489901)
            ·
              refine ⟨62540708321209664837433713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 166775222189892439566489901 62540708321209664837433713)
              ·
                refine ⟨46905531240907248628075285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62540708321209664837433713 46905531240907248628075285)
                ·
                  refine ⟨2198696776917527279441029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46905531240907248628075285 2198696776917527279441029)
                  ·
                    refine ⟨412255645672036364895193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2198696776917527279441029 412255645672036364895193)
                    ·
                      rfl

theorem cell23_2408595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 4].length) (baseStart_2408595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408595 prefixEnd_2408595 := by exact prefixLift 2408595
  have htrace : WordTrace (prefixWord ++ tailWord_2408595) baseStart_2408595 baseEnd_2408595 := by
    simpa [prefixWord, tailWord_2408595, baseEnd_2408595] using wordTrace_append hprefix tailTrace_2408595
  have hstable : (prefixWord ++ tailWord_2408595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408595).length < 2 ^ (prefixWord ++ tailWord_2408595).sum := by decide
  have hdescent : baseEnd_2408595 < baseStart_2408595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408606 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_2408606 : Nat := 118140960795 + 2408606 * 2 ^ 59
def prefixEnd_2408606 : Nat := 4983230072969 + 3 ^ 40 * 2408606 * 2
def baseEnd_2408606 : Nat := 1236772585303308551648029

theorem tailTrace_2408606 : CollatzResearch.WordTrace tailWord_2408606 prefixEnd_2408606 1236772585303308551648029 := by
  unfold tailWord_2408606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10981134739004911750011709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58566051941359529333395781 10981134739004911750011709)
  ·
    refine ⟨4117925527126841906254391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10981134739004911750011709 4117925527126841906254391)
    ·
      refine ⟨6176888290690262859381587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4117925527126841906254391 6176888290690262859381587)
      ·
        refine ⟨9265332436035394289072381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6176888290690262859381587 9265332436035394289072381)
        ·
          refine ⟨3474499663513272858402143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9265332436035394289072381 3474499663513272858402143)
          ·
            refine ⟨5211749495269909287603215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3474499663513272858402143 5211749495269909287603215)
            ·
              refine ⟨7817624242904863931404823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5211749495269909287603215 7817624242904863931404823)
              ·
                refine ⟨11726436364357295897107235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7817624242904863931404823 11726436364357295897107235)
                ·
                  refine ⟨17589654546535943845660853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11726436364357295897107235 17589654546535943845660853)
                  ·
                    refine ⟨1649030113737744735530705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17589654546535943845660853 1649030113737744735530705)
                    ·
                      refine ⟨1236772585303308551648029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649030113737744735530705 1236772585303308551648029)
                      ·
                        rfl

theorem cell23_2408606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_2408606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408606 prefixEnd_2408606 := by exact prefixLift 2408606
  have htrace : WordTrace (prefixWord ++ tailWord_2408606) baseStart_2408606 baseEnd_2408606 := by
    simpa [prefixWord, tailWord_2408606, baseEnd_2408606] using wordTrace_append hprefix tailTrace_2408606
  have hstable : (prefixWord ++ tailWord_2408606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408606).length < 2 ^ (prefixWord ++ tailWord_2408606).sum := by decide
  have hdescent : baseEnd_2408606 < baseStart_2408606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408665 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_2408665 : Nat := 118140960795 + 2408665 * 2 ^ 59
def prefixEnd_2408665 : Nat := 4983230072969 + 3 ^ 40 * 2408665 * 2
def baseEnd_2408665 : Nat := 1236802880661923820810257

theorem tailTrace_2408665 : CollatzResearch.WordTrace tailWord_2408665 prefixEnd_2408665 1236802880661923820810257 := by
  unfold tailWord_2408665
  simp only [CollatzResearch.WordTrace]
  refine ⟨87851229818825547076491449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58567486545883698050994299 87851229818825547076491449)
  ·
    refine ⟨65888422364119160307368587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87851229818825547076491449 65888422364119160307368587)
    ·
      refine ⟨98832633546178740461052881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65888422364119160307368587 98832633546178740461052881)
      ·
        refine ⟨74124475159634055345789661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98832633546178740461052881 74124475159634055345789661)
        ·
          refine ⟨27796678184862770754671123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74124475159634055345789661 27796678184862770754671123)
          ·
            refine ⟨41695017277294156132006685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27796678184862770754671123 41695017277294156132006685)
            ·
              refine ⟨15635631478985308549502507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41695017277294156132006685 15635631478985308549502507)
              ·
                refine ⟨23453447218477962824253761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15635631478985308549502507 23453447218477962824253761)
                ·
                  refine ⟨17590085413858472118190321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23453447218477962824253761 17590085413858472118190321)
                  ·
                    refine ⟨13192564060393854088642741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17590085413858472118190321 13192564060393854088642741)
                    ·
                      refine ⟨1236802880661923820810257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13192564060393854088642741 1236802880661923820810257)
                      ·
                        rfl

theorem cell23_2408665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_2408665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408665 prefixEnd_2408665 := by exact prefixLift 2408665
  have htrace : WordTrace (prefixWord ++ tailWord_2408665) baseStart_2408665 baseEnd_2408665 := by
    simpa [prefixWord, tailWord_2408665, baseEnd_2408665] using wordTrace_append hprefix tailTrace_2408665
  have hstable : (prefixWord ++ tailWord_2408665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408665).length < 2 ^ (prefixWord ++ tailWord_2408665).sum := by decide
  have hdescent : baseEnd_2408665 < baseStart_2408665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408695 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_2408695 : Nat := 118140960795 + 2408695 * 2 ^ 59
def prefixEnd_2408695 : Nat := 4983230072969 + 3 ^ 40 * 2408695 * 2
def baseEnd_2408695 : Nat := 1236818285081558703435119

theorem tailTrace_2408695 : CollatzResearch.WordTrace tailWord_2408695 prefixEnd_2408695 1236818285081558703435119 := by
  unfold tailWord_2408695
  simp only [CollatzResearch.WordTrace]
  refine ⟨87852324008716862200083539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58568216005811241466722359 87852324008716862200083539)
  ·
    refine ⟨131778486013075293300125309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87852324008716862200083539 131778486013075293300125309)
    ·
      refine ⟨49416932254903234987546991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131778486013075293300125309 49416932254903234987546991)
      ·
        refine ⟨74125398382354852481320487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49416932254903234987546991 74125398382354852481320487)
        ·
          refine ⟨111188097573532278721980731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74125398382354852481320487 111188097573532278721980731)
          ·
            refine ⟨166782146360298418082971097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111188097573532278721980731 166782146360298418082971097)
            ·
              refine ⟨125086609770223813562228323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166782146360298418082971097 125086609770223813562228323)
              ·
                refine ⟨187629914655335720343342485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125086609770223813562228323 187629914655335720343342485)
                ·
                  refine ⟨8795152249468861891094179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 187629914655335720343342485 8795152249468861891094179)
                  ·
                    refine ⟨13192728374203292836641269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8795152249468861891094179 13192728374203292836641269)
                    ·
                      refine ⟨1236818285081558703435119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13192728374203292836641269 1236818285081558703435119)
                      ·
                        rfl

theorem cell23_2408695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_2408695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408695 prefixEnd_2408695 := by exact prefixLift 2408695
  have htrace : WordTrace (prefixWord ++ tailWord_2408695) baseStart_2408695 baseEnd_2408695 := by
    simpa [prefixWord, tailWord_2408695, baseEnd_2408695] using wordTrace_append hprefix tailTrace_2408695
  have hstable : (prefixWord ++ tailWord_2408695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408695).length < 2 ^ (prefixWord ++ tailWord_2408695).sum := by decide
  have hdescent : baseEnd_2408695 < baseStart_2408695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408702 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2408702 : Nat := 118140960795 + 2408702 * 2 ^ 59
def prefixEnd_2408702 : Nat := 4983230072969 + 3 ^ 40 * 2408702 * 2
def baseEnd_2408702 : Nat := 412273959815380058682529

theorem tailTrace_2408702 : CollatzResearch.WordTrace tailWord_2408702 prefixEnd_2408702 412273959815380058682529 := by
  unfold tailWord_2408702
  simp only [CollatzResearch.WordTrace]
  refine ⟨10981572414961437799448545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58568386213127668263725573 10981572414961437799448545)
  ·
    refine ⟨8236179311221078349586409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10981572414961437799448545 8236179311221078349586409)
    ·
      refine ⟨6177134483415808762189807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8236179311221078349586409 6177134483415808762189807)
      ·
        refine ⟨9265701725123713143284711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6177134483415808762189807 9265701725123713143284711)
        ·
          refine ⟨13898552587685569714927067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9265701725123713143284711 13898552587685569714927067)
          ·
            refine ⟨20847828881528354572390601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13898552587685569714927067 20847828881528354572390601)
            ·
              refine ⟨15635871661146265929292951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20847828881528354572390601 15635871661146265929292951)
              ·
                refine ⟨23453807491719398893939427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15635871661146265929292951 23453807491719398893939427)
                ·
                  refine ⟨35180711237579098340909141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23453807491719398893939427 35180711237579098340909141)
                  ·
                    refine ⟨412273959815380058682529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35180711237579098340909141 412273959815380058682529)
                    ·
                      rfl

theorem cell23_2408702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2408702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408702 prefixEnd_2408702 := by exact prefixLift 2408702
  have htrace : WordTrace (prefixWord ++ tailWord_2408702) baseStart_2408702 baseEnd_2408702 := by
    simpa [prefixWord, tailWord_2408702, baseEnd_2408702] using wordTrace_append hprefix tailTrace_2408702
  have hstable : (prefixWord ++ tailWord_2408702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408702).length < 2 ^ (prefixWord ++ tailWord_2408702).sum := by decide
  have hdescent : baseEnd_2408702 < baseStart_2408702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408709 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 6, 2, 2]
def baseStart_2408709 : Nat := 118140960795 + 2408709 * 2 ^ 59
def prefixEnd_2408709 : Nat := 4983230072969 + 3 ^ 40 * 2408709 * 2
def baseEnd_2408709 : Nat := 1236825473810721648660055

theorem tailTrace_2408709 : CollatzResearch.WordTrace tailWord_2408709 prefixEnd_2408709 1236825473810721648660055 := by
  unfold tailWord_2408709
  simp only [CollatzResearch.WordTrace]
  refine ⟨87852834630666142591093181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58568556420444095060728787 87852834630666142591093181)
  ·
    refine ⟨32944812986499803471659943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87852834630666142591093181 32944812986499803471659943)
    ·
      refine ⟨49417219479749705207489915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32944812986499803471659943 49417219479749705207489915)
      ·
        refine ⟨74125829219624557811234873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49417219479749705207489915 74125829219624557811234873)
        ·
          refine ⟨55594371914718418358426155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74125829219624557811234873 55594371914718418358426155)
          ·
            refine ⟨83391557872077627537639233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55594371914718418358426155 83391557872077627537639233)
            ·
              refine ⟨62543668404058220653229425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83391557872077627537639233 62543668404058220653229425)
              ·
                refine ⟨46907751303043665489922069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62543668404058220653229425 46907751303043665489922069)
                ·
                  refine ⟨2198800842330171819840097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46907751303043665489922069 2198800842330171819840097)
                  ·
                    refine ⟨1649100631747628864880073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2198800842330171819840097 1649100631747628864880073)
                    ·
                      refine ⟨1236825473810721648660055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649100631747628864880073 1236825473810721648660055)
                      ·
                        rfl

theorem cell23_2408709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 6, 2, 2].length) (baseStart_2408709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408709 prefixEnd_2408709 := by exact prefixLift 2408709
  have htrace : WordTrace (prefixWord ++ tailWord_2408709) baseStart_2408709 baseEnd_2408709 := by
    simpa [prefixWord, tailWord_2408709, baseEnd_2408709] using wordTrace_append hprefix tailTrace_2408709
  have hstable : (prefixWord ++ tailWord_2408709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408709).length < 2 ^ (prefixWord ++ tailWord_2408709).sum := by decide
  have hdescent : baseEnd_2408709 < baseStart_2408709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408712 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2408712 : Nat := 118140960795 + 2408712 * 2 ^ 59
def prefixEnd_2408712 : Nat := 4983230072969 + 3 ^ 40 * 2408712 * 2
def baseEnd_2408712 : Nat := 1236827014252685136922541

theorem tailTrace_2408712 : CollatzResearch.WordTrace tailWord_2408712 prefixEnd_2408712 1236827014252685136922541 := by
  unfold tailWord_2408712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43926472024827637051726195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58568629366436849402301593 43926472024827637051726195)
  ·
    refine ⟨65889708037241455577589293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43926472024827637051726195 65889708037241455577589293)
    ·
      refine ⟨24708640513965545841595985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65889708037241455577589293 24708640513965545841595985)
      ·
        refine ⟨18531480385474159381196989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24708640513965545841595985 18531480385474159381196989)
        ·
          refine ⟨6949305144552809767948871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18531480385474159381196989 6949305144552809767948871)
          ·
            refine ⟨10423957716829214651923307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6949305144552809767948871 10423957716829214651923307)
            ·
              refine ⟨15635936575243821977884961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10423957716829214651923307 15635936575243821977884961)
              ·
                refine ⟨11726952431432866483413721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15635936575243821977884961 11726952431432866483413721)
                ·
                  refine ⟨8795214323574649862560291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11726952431432866483413721 8795214323574649862560291)
                  ·
                    refine ⟨13192821485361974793840437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8795214323574649862560291 13192821485361974793840437)
                    ·
                      refine ⟨1236827014252685136922541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13192821485361974793840437 1236827014252685136922541)
                      ·
                        rfl

theorem cell23_2408712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2408712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408712 prefixEnd_2408712 := by exact prefixLift 2408712
  have htrace : WordTrace (prefixWord ++ tailWord_2408712) baseStart_2408712 baseEnd_2408712 := by
    simpa [prefixWord, tailWord_2408712, baseEnd_2408712] using wordTrace_append hprefix tailTrace_2408712
  have hstable : (prefixWord ++ tailWord_2408712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408712).length < 2 ^ (prefixWord ++ tailWord_2408712).sum := by decide
  have hdescent : baseEnd_2408712 < baseStart_2408712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408715 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 9]
def baseStart_2408715 : Nat := 118140960795 + 2408715 * 2 ^ 59
def prefixEnd_2408715 : Nat := 4983230072969 + 3 ^ 40 * 2408715 * 2
def baseEnd_2408715 : Nat := 137425394966072069465003

theorem tailTrace_2408715 : CollatzResearch.WordTrace tailWord_2408715 prefixEnd_2408715 137425394966072069465003 := by
  unfold tailWord_2408715
  simp only [CollatzResearch.WordTrace]
  refine ⟨87853053468644405615811599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58568702312429603743874399 87853053468644405615811599)
  ·
    refine ⟨131779580202966608423717399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87853053468644405615811599 131779580202966608423717399)
    ·
      refine ⟨197669370304449912635576099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131779580202966608423717399 197669370304449912635576099)
      ·
        refine ⟨296504055456674868953364149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197669370304449912635576099 296504055456674868953364149)
        ·
          refine ⟨27797255199063268964377889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 296504055456674868953364149 27797255199063268964377889)
          ·
            refine ⟨20847941399297451723283417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27797255199063268964377889 20847941399297451723283417)
            ·
              refine ⟨15635956049473088792462563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20847941399297451723283417 15635956049473088792462563)
              ·
                refine ⟨23453934074209633188693845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15635956049473088792462563 23453934074209633188693845)
                ·
                  refine ⟨137425394966072069465003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23453934074209633188693845 137425394966072069465003)
                  ·
                    rfl

theorem cell23_2408715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 9].length) (baseStart_2408715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408715 prefixEnd_2408715 := by exact prefixLift 2408715
  have htrace : WordTrace (prefixWord ++ tailWord_2408715) baseStart_2408715 baseEnd_2408715 := by
    simpa [prefixWord, tailWord_2408715, baseEnd_2408715] using wordTrace_append hprefix tailTrace_2408715
  have hstable : (prefixWord ++ tailWord_2408715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408715).length < 2 ^ (prefixWord ++ tailWord_2408715).sum := by decide
  have hdescent : baseEnd_2408715 < baseStart_2408715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408799 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 2, 4, 2]
def baseStart_2408799 : Nat := 118140960795 + 2408799 * 2 ^ 59
def prefixEnd_2408799 : Nat := 4983230072969 + 3 ^ 40 * 2408799 * 2
def baseEnd_2408799 : Nat := 1236871687069626296534641

theorem tailTrace_2408799 : CollatzResearch.WordTrace tailWord_2408799 prefixEnd_2408799 1236871687069626296534641 := by
  unfold tailWord_2408799
  simp only [CollatzResearch.WordTrace]
  refine ⟨87856117200340087961869451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58570744800226725307912967 87856117200340087961869451)
  ·
    refine ⟨131784175800510131942804177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87856117200340087961869451 131784175800510131942804177)
    ·
      refine ⟨98838131850382598957103133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131784175800510131942804177 98838131850382598957103133)
      ·
        refine ⟨37064299443893474608913675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98838131850382598957103133 37064299443893474608913675)
        ·
          refine ⟨55596449165840211913370513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37064299443893474608913675 55596449165840211913370513)
          ·
            refine ⟨41697336874380158935027885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55596449165840211913370513 41697336874380158935027885)
            ·
              refine ⟨15636501327892559600635457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41697336874380158935027885 15636501327892559600635457)
              ·
                refine ⟨11727375995919419700476593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15636501327892559600635457 11727375995919419700476593)
                ·
                  refine ⟨8795531996939564775357445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11727375995919419700476593 8795531996939564775357445)
                  ·
                    refine ⟨1649162249426168395379521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8795531996939564775357445 1649162249426168395379521)
                    ·
                      refine ⟨1236871687069626296534641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649162249426168395379521 1236871687069626296534641)
                      ·
                        rfl

theorem cell23_2408799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_2408799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408799 prefixEnd_2408799 := by exact prefixLift 2408799
  have htrace : WordTrace (prefixWord ++ tailWord_2408799) baseStart_2408799 baseEnd_2408799 := by
    simpa [prefixWord, tailWord_2408799, baseEnd_2408799] using wordTrace_append hprefix tailTrace_2408799
  have hstable : (prefixWord ++ tailWord_2408799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408799).length < 2 ^ (prefixWord ++ tailWord_2408799).sum := by decide
  have hdescent : baseEnd_2408799 < baseStart_2408799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408809 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 3, 4]
def baseStart_2408809 : Nat := 118140960795 + 2408809 * 2 ^ 59
def prefixEnd_2408809 : Nat := 4983230072969 + 3 ^ 40 * 2408809 * 2
def baseEnd_2408809 : Nat := 412292273958723752469865

theorem tailTrace_2408809 : CollatzResearch.WordTrace tailWord_2408809 prefixEnd_2408809 412292273958723752469865 := by
  unfold tailWord_2408809
  simp only [CollatzResearch.WordTrace]
  refine ⟨87856481930303859669733481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58570987953535906446488987 87856481930303859669733481)
  ·
    refine ⟨65892361447727894752300111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87856481930303859669733481 65892361447727894752300111)
    ·
      refine ⟨98838542171591842128450167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65892361447727894752300111 98838542171591842128450167)
      ·
        refine ⟨148257813257387763192675251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98838542171591842128450167 148257813257387763192675251)
        ·
          refine ⟨222386719886081644789012877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148257813257387763192675251 222386719886081644789012877)
          ·
            refine ⟨83395019957280616795879829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222386719886081644789012877 83395019957280616795879829)
            ·
              refine ⟨3909141560497528912306867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83395019957280616795879829 3909141560497528912306867)
              ·
                refine ⟨5863712340746293368460301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909141560497528912306867 5863712340746293368460301)
                ·
                  refine ⟨2198892127779860013172613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5863712340746293368460301 2198892127779860013172613)
                  ·
                    refine ⟨412292273958723752469865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2198892127779860013172613 412292273958723752469865)
                    ·
                      rfl

theorem cell23_2408809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 4].length) (baseStart_2408809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408809 prefixEnd_2408809 := by exact prefixLift 2408809
  have htrace : WordTrace (prefixWord ++ tailWord_2408809) baseStart_2408809 baseEnd_2408809 := by
    simpa [prefixWord, tailWord_2408809, baseEnd_2408809] using wordTrace_append hprefix tailTrace_2408809
  have hstable : (prefixWord ++ tailWord_2408809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408809).length < 2 ^ (prefixWord ++ tailWord_2408809).sum := by decide
  have hdescent : baseEnd_2408809 < baseStart_2408809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408843 : List Nat := [1, 1, 1, 1, 4, 6, 1, 3, 1, 4]
def baseStart_2408843 : Nat := 118140960795 + 2408843 * 2 ^ 59
def prefixEnd_2408843 : Nat := 4983230072969 + 3 ^ 40 * 2408843 * 2
def baseEnd_2408843 : Nat := 412298093406141374794813

theorem tailTrace_2408843 : CollatzResearch.WordTrace tailWord_2408843 prefixEnd_2408843 412298093406141374794813 := by
  unfold tailWord_2408843
  simp only [CollatzResearch.WordTrace]
  refine ⟨87857722012180683476471183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58571814674787122317647455 87857722012180683476471183)
  ·
    refine ⟨131786583018271025214706775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87857722012180683476471183 131786583018271025214706775)
    ·
      refine ⟨197679874527406537822060163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131786583018271025214706775 197679874527406537822060163)
      ·
        refine ⟨296519811791109806733090245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197679874527406537822060163 296519811791109806733090245)
        ·
          refine ⟨55597464710833088762454421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296519811791109806733090245 55597464710833088762454421)
          ·
            refine ⟨2606131158320301035740051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55597464710833088762454421 2606131158320301035740051)
            ·
              refine ⟨3909196737480451553610077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2606131158320301035740051 3909196737480451553610077)
              ·
                refine ⟨1465948776555169332603779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3909196737480451553610077 1465948776555169332603779)
                ·
                  refine ⟨2198923164832753998905669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1465948776555169332603779 2198923164832753998905669)
                  ·
                    refine ⟨412298093406141374794813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2198923164832753998905669 412298093406141374794813)
                    ·
                      rfl

theorem cell23_2408843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 1, 4].length) (baseStart_2408843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408843 prefixEnd_2408843 := by exact prefixLift 2408843
  have htrace : WordTrace (prefixWord ++ tailWord_2408843) baseStart_2408843 baseEnd_2408843 := by
    simpa [prefixWord, tailWord_2408843, baseEnd_2408843] using wordTrace_append hprefix tailTrace_2408843
  have hstable : (prefixWord ++ tailWord_2408843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408843).length < 2 ^ (prefixWord ++ tailWord_2408843).sum := by decide
  have hdescent : baseEnd_2408843 < baseStart_2408843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408893 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 2, 3, 2]
def baseStart_2408893 : Nat := 118140960795 + 2408893 * 2 ^ 59
def prefixEnd_2408893 : Nat := 4983230072969 + 3 ^ 40 * 2408893 * 2
def baseEnd_2408893 : Nat := 1236919954251148928759209

theorem tailTrace_2408893 : CollatzResearch.WordTrace tailWord_2408893 prefixEnd_2408893 1236919954251148928759209 := by
  unfold tailWord_2408893
  simp only [CollatzResearch.WordTrace]
  refine ⟨87859545661999542015791333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58573030441333028010527555 87859545661999542015791333)
  ·
    refine ⟨16473664811624914127960875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87859545661999542015791333 16473664811624914127960875)
    ·
      refine ⟨24710497217437371191941313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16473664811624914127960875 24710497217437371191941313)
      ·
        refine ⟨18532872913078028393955985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24710497217437371191941313 18532872913078028393955985)
        ·
          refine ⟨13899654684808521295466989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18532872913078028393955985 13899654684808521295466989)
          ·
            refine ⟨5212370506803195485800121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13899654684808521295466989 5212370506803195485800121)
            ·
              refine ⟨3909277880102396614350091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5212370506803195485800121 3909277880102396614350091)
              ·
                refine ⟨5863916820153594921525137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909277880102396614350091 5863916820153594921525137)
                ·
                  refine ⟨4397937615115196191143853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5863916820153594921525137 4397937615115196191143853)
                  ·
                    refine ⟨1649226605668198571678945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4397937615115196191143853 1649226605668198571678945)
                    ·
                      refine ⟨1236919954251148928759209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649226605668198571678945 1236919954251148928759209)
                      ·
                        rfl

theorem cell23_2408893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_2408893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408893 prefixEnd_2408893 := by exact prefixLift 2408893
  have htrace : WordTrace (prefixWord ++ tailWord_2408893) baseStart_2408893 baseEnd_2408893 := by
    simpa [prefixWord, tailWord_2408893, baseEnd_2408893] using wordTrace_append hprefix tailTrace_2408893
  have hstable : (prefixWord ++ tailWord_2408893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408893).length < 2 ^ (prefixWord ++ tailWord_2408893).sum := by decide
  have hdescent : baseEnd_2408893 < baseStart_2408893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408917 : List Nat := [1, 3, 2, 3, 1, 4, 2, 2, 1, 1, 3]
def baseStart_2408917 : Nat := 118140960795 + 2408917 * 2 ^ 59
def prefixEnd_2408917 : Nat := 4983230072969 + 3 ^ 40 * 2408917 * 2
def baseEnd_2408917 : Nat := 1236932277786856834859099

theorem tailTrace_2408917 : CollatzResearch.WordTrace tailWord_2408917 prefixEnd_2408917 1236932277786856834859099 := by
  unfold tailWord_2408917
  simp only [CollatzResearch.WordTrace]
  refine ⟨87860421013912594114665005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58573614009275062743110003 87860421013912594114665005)
  ·
    refine ⟨32947657880217222792999377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87860421013912594114665005 32947657880217222792999377)
    ·
      refine ⟨24710743410162917094749533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32947657880217222792999377 24710743410162917094749533)
      ·
        refine ⟨9266528778811093910531075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24710743410162917094749533 9266528778811093910531075)
        ·
          refine ⟨13899793168216640865796613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9266528778811093910531075 13899793168216640865796613)
          ·
            refine ⟨2606211219040620162336865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13899793168216640865796613 2606211219040620162336865)
            ·
              refine ⟨1954658414280465121752649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2606211219040620162336865 1954658414280465121752649)
              ·
                refine ⟨1465993810710348841314487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1954658414280465121752649 1465993810710348841314487)
                ·
                  refine ⟨2198990716065523261971731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1465993810710348841314487 2198990716065523261971731)
                  ·
                    refine ⟨3298486074098284892957597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2198990716065523261971731 3298486074098284892957597)
                    ·
                      refine ⟨1236932277786856834859099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3298486074098284892957597 1236932277786856834859099)
                      ·
                        rfl

theorem cell23_2408917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_2408917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408917 prefixEnd_2408917 := by exact prefixLift 2408917
  have htrace : WordTrace (prefixWord ++ tailWord_2408917) baseStart_2408917 baseEnd_2408917 := by
    simpa [prefixWord, tailWord_2408917, baseEnd_2408917] using wordTrace_append hprefix tailTrace_2408917
  have hstable : (prefixWord ++ tailWord_2408917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408917).length < 2 ^ (prefixWord ++ tailWord_2408917).sum := by decide
  have hdescent : baseEnd_2408917 < baseStart_2408917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408936 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_2408936 : Nat := 118140960795 + 2408936 * 2 ^ 59
def prefixEnd_2408936 : Nat := 4983230072969 + 3 ^ 40 * 2408936 * 2
def baseEnd_2408936 : Nat := 1236942033919292260521511

theorem tailTrace_2408936 : CollatzResearch.WordTrace tailWord_2408936 prefixEnd_2408936 1236942033919292260521511 := by
  unfold tailWord_2408936
  simp only [CollatzResearch.WordTrace]
  refine ⟨43930557000421880179803331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58574076000562506906404441 43930557000421880179803331)
  ·
    refine ⟨65895835500632820269704997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43930557000421880179803331 65895835500632820269704997)
    ·
      refine ⟨12355469156368653800569687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65895835500632820269704997 12355469156368653800569687)
      ·
        refine ⟨18533203734552980700854531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12355469156368653800569687 18533203734552980700854531)
        ·
          refine ⟨27799805601829471051281797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18533203734552980700854531 27799805601829471051281797)
          ·
            refine ⟨5212463550343025822115337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27799805601829471051281797 5212463550343025822115337)
            ·
              refine ⟨3909347662757269366586503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5212463550343025822115337 3909347662757269366586503)
              ·
                refine ⟨5864021494135904049879755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909347662757269366586503 5864021494135904049879755)
                ·
                  refine ⟨8796032241203856074819633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5864021494135904049879755 8796032241203856074819633)
                  ·
                    refine ⟨6597024180902892056114725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8796032241203856074819633 6597024180902892056114725)
                    ·
                      refine ⟨1236942033919292260521511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6597024180902892056114725 1236942033919292260521511)
                      ·
                        rfl

theorem cell23_2408936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_2408936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408936 prefixEnd_2408936 := by exact prefixLift 2408936
  have htrace : WordTrace (prefixWord ++ tailWord_2408936) baseStart_2408936 baseEnd_2408936 := by
    simpa [prefixWord, tailWord_2408936, baseEnd_2408936] using wordTrace_append hprefix tailTrace_2408936
  have hstable : (prefixWord ++ tailWord_2408936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408936).length < 2 ^ (prefixWord ++ tailWord_2408936).sum := by decide
  have hdescent : baseEnd_2408936 < baseStart_2408936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2408956 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_2408956 : Nat := 118140960795 + 2408956 * 2 ^ 59
def prefixEnd_2408956 : Nat := 4983230072969 + 3 ^ 40 * 2408956 * 2
def baseEnd_2408956 : Nat := 1236952303532382182271419

theorem tailTrace_2408956 : CollatzResearch.WordTrace tailWord_2408956 prefixEnd_2408956 1236952303532382182271419 := by
  unfold tailWord_2408956
  simp only [CollatzResearch.WordTrace]
  refine ⟨43930921730385651887667361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58574562307180869183556481 43930921730385651887667361)
  ·
    refine ⟨32948191297789238915750521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43930921730385651887667361 32948191297789238915750521)
    ·
      refine ⟨24711143473341929186812891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32948191297789238915750521 24711143473341929186812891)
      ·
        refine ⟨37066715210012893780219337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24711143473341929186812891 37066715210012893780219337)
        ·
          refine ⟨27800036407509670335164503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37066715210012893780219337 27800036407509670335164503)
          ·
            refine ⟨41700054611264505502746755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27800036407509670335164503 41700054611264505502746755)
            ·
              refine ⟨62550081916896758254120133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41700054611264505502746755 62550081916896758254120133)
              ·
                refine ⟨11728140359418142172647525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62550081916896758254120133 11728140359418142172647525)
                ·
                  refine ⟨2199026317390901657371411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11728140359418142172647525 2199026317390901657371411)
                  ·
                    refine ⟨3298539476086352486057117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2199026317390901657371411 3298539476086352486057117)
                    ·
                      refine ⟨1236952303532382182271419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3298539476086352486057117 1236952303532382182271419)
                      ·
                        rfl

theorem cell23_2408956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_2408956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2408956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2408956 prefixEnd_2408956 := by exact prefixLift 2408956
  have htrace : WordTrace (prefixWord ++ tailWord_2408956) baseStart_2408956 baseEnd_2408956 := by
    simpa [prefixWord, tailWord_2408956, baseEnd_2408956] using wordTrace_append hprefix tailTrace_2408956
  have hstable : (prefixWord ++ tailWord_2408956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2408956).length < 2 ^ (prefixWord ++ tailWord_2408956).sum := by decide
  have hdescent : baseEnd_2408956 < baseStart_2408956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2408956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409000 : List Nat := [2, 1, 5, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_2409000 : Nat := 118140960795 + 2409000 * 2 ^ 59
def prefixEnd_2409000 : Nat := 4983230072969 + 3 ^ 40 * 2409000 * 2
def baseEnd_2409000 : Nat := 1236974896681180010121217

theorem tailTrace_2409000 : CollatzResearch.WordTrace tailWord_2409000 prefixEnd_2409000 1236974896681180010121217 := by
  unfold tailWord_2409000
  simp only [CollatzResearch.WordTrace]
  refine ⟨43931724136305949644968227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58575632181741266193290969 43931724136305949644968227)
  ·
    refine ⟨65897586204458924467452341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43931724136305949644968227 65897586204458924467452341)
    ·
      refine ⟨6177898706668024168823657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65897586204458924467452341 6177898706668024168823657)
      ·
        refine ⟨4633424030001018126617743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6177898706668024168823657 4633424030001018126617743)
        ·
          refine ⟨6950136045001527189926615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4633424030001018126617743 6950136045001527189926615)
          ·
            refine ⟨10425204067502290784889923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6950136045001527189926615 10425204067502290784889923)
            ·
              refine ⟨15637806101253436177334885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10425204067502290784889923 15637806101253436177334885)
              ·
                refine ⟨2932088643985019283250291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15637806101253436177334885 2932088643985019283250291)
                ·
                  refine ⟨4398132965977528924875437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932088643985019283250291 4398132965977528924875437)
                  ·
                    refine ⟨1649299862241573346828289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4398132965977528924875437 1649299862241573346828289)
                    ·
                      refine ⟨1236974896681180010121217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649299862241573346828289 1236974896681180010121217)
                      ·
                        rfl

theorem cell23_2409000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_2409000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409000 prefixEnd_2409000 := by exact prefixLift 2409000
  have htrace : WordTrace (prefixWord ++ tailWord_2409000) baseStart_2409000 baseEnd_2409000 := by
    simpa [prefixWord, tailWord_2409000, baseEnd_2409000] using wordTrace_append hprefix tailTrace_2409000
  have hstable : (prefixWord ++ tailWord_2409000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409000).length < 2 ^ (prefixWord ++ tailWord_2409000).sum := by decide
  have hdescent : baseEnd_2409000 < baseStart_2409000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409009 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2409009 : Nat := 118140960795 + 2409009 * 2 ^ 59
def prefixEnd_2409009 : Nat := 4983230072969 + 3 ^ 40 * 2409009 * 2
def baseEnd_2409009 : Nat := 1236979518007070474908675

theorem tailTrace_2409009 : CollatzResearch.WordTrace tailWord_2409009 prefixEnd_2409009 1236979518007070474908675 := by
  unfold tailWord_2409009
  simp only [CollatzResearch.WordTrace]
  refine ⟨87863776529579293827014081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58575851019719529218009387 87863776529579293827014081)
  ·
    refine ⟨65897832397184470370260561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87863776529579293827014081 65897832397184470370260561)
    ·
      refine ⟨49423374297888352777695421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65897832397184470370260561 49423374297888352777695421)
      ·
        refine ⟨18533765361708132291635783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49423374297888352777695421 18533765361708132291635783)
        ·
          refine ⟨27800648042562198437453675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18533765361708132291635783 27800648042562198437453675)
          ·
            refine ⟨41700972063843297656180513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27800648042562198437453675 41700972063843297656180513)
            ·
              refine ⟨31275729047882473242135385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41700972063843297656180513 31275729047882473242135385)
              ·
                refine ⟨23456796785911854931601539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31275729047882473242135385 23456796785911854931601539)
                ·
                  refine ⟨35185195178867782397402309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23456796785911854931601539 35185195178867782397402309)
                  ·
                    refine ⟨6597224096037709199512933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35185195178867782397402309 6597224096037709199512933)
                    ·
                      refine ⟨1236979518007070474908675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6597224096037709199512933 1236979518007070474908675)
                      ·
                        rfl

theorem cell23_2409009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2409009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409009 prefixEnd_2409009 := by exact prefixLift 2409009
  have htrace : WordTrace (prefixWord ++ tailWord_2409009) baseStart_2409009 baseEnd_2409009 := by
    simpa [prefixWord, tailWord_2409009, baseEnd_2409009] using wordTrace_append hprefix tailTrace_2409009
  have hstable : (prefixWord ++ tailWord_2409009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409009).length < 2 ^ (prefixWord ++ tailWord_2409009).sum := by decide
  have hdescent : baseEnd_2409009 < baseStart_2409009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409013 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_2409013 : Nat := 118140960795 + 2409013 * 2 ^ 59
def prefixEnd_2409013 : Nat := 4983230072969 + 3 ^ 40 * 2409013 * 2
def baseEnd_2409013 : Nat := 1236981571929688459258657

theorem tailTrace_2409013 : CollatzResearch.WordTrace tailWord_2409013 prefixEnd_2409013 1236981571929688459258657 := by
  unfold tailWord_2409013
  simp only [CollatzResearch.WordTrace]
  refine ⟨87863922421564802510159693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58575948281043201673439795 87863922421564802510159693)
  ·
    refine ⟨32948970908086800941309885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87863922421564802510159693 32948970908086800941309885)
    ·
      refine ⟨12355864090532550352991207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32948970908086800941309885 12355864090532550352991207)
      ·
        refine ⟨18533796135798825529486811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12355864090532550352991207 18533796135798825529486811)
        ·
          refine ⟨27800694203698238294230217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18533796135798825529486811 27800694203698238294230217)
          ·
            refine ⟨20850520652773678720672663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27800694203698238294230217 20850520652773678720672663)
            ·
              refine ⟨31275780979160518081008995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20850520652773678720672663 31275780979160518081008995)
              ·
                refine ⟨46913671468740777121513493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31275780979160518081008995 46913671468740777121513493)
                ·
                  refine ⟨2199078350097223927570945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46913671468740777121513493 2199078350097223927570945)
                  ·
                    refine ⟨1649308762572917945678209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2199078350097223927570945 1649308762572917945678209)
                    ·
                      refine ⟨1236981571929688459258657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649308762572917945678209 1236981571929688459258657)
                      ·
                        rfl

theorem cell23_2409013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_2409013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409013 prefixEnd_2409013 := by exact prefixLift 2409013
  have htrace : WordTrace (prefixWord ++ tailWord_2409013) baseStart_2409013 baseEnd_2409013 := by
    simpa [prefixWord, tailWord_2409013, baseEnd_2409013] using wordTrace_append hprefix tailTrace_2409013
  have hstable : (prefixWord ++ tailWord_2409013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409013).length < 2 ^ (prefixWord ++ tailWord_2409013).sum := by decide
  have hdescent : baseEnd_2409013 < baseStart_2409013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409059 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 7]
def baseStart_2409059 : Nat := 118140960795 + 2409059 * 2 ^ 59
def prefixEnd_2409059 : Nat := 4983230072969 + 3 ^ 40 * 2409059 * 2
def baseEnd_2409059 : Nat := 1237005192039795279283445

theorem tailTrace_2409059 : CollatzResearch.WordTrace tailWord_2409059 prefixEnd_2409059 1237005192039795279283445 := by
  unfold tailWord_2409059
  simp only [CollatzResearch.WordTrace]
  refine ⟨87865600179398152366334231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58577066786265434910889487 87865600179398152366334231)
  ·
    refine ⟨131798400269097228549501347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87865600179398152366334231 131798400269097228549501347)
    ·
      refine ⟨197697600403645842824252021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131798400269097228549501347 197697600403645842824252021)
      ·
        refine ⟨18534150037841797764773627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197697600403645842824252021 18534150037841797764773627)
        ·
          refine ⟨27801225056762696647160441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18534150037841797764773627 27801225056762696647160441)
          ·
            refine ⟨20850918792572022485370331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27801225056762696647160441 20850918792572022485370331)
            ·
              refine ⟨31276378188858033728055497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20850918792572022485370331 31276378188858033728055497)
              ·
                refine ⟨23457283641643525296041623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31276378188858033728055497 23457283641643525296041623)
                ·
                  refine ⟨35185925462465287944062435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23457283641643525296041623 35185925462465287944062435)
                  ·
                    refine ⟨52778888193697931916093653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35185925462465287944062435 52778888193697931916093653)
                    ·
                      refine ⟨1237005192039795279283445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52778888193697931916093653 1237005192039795279283445)
                      ·
                        rfl

theorem cell23_2409059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_2409059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409059 prefixEnd_2409059 := by exact prefixLift 2409059
  have htrace : WordTrace (prefixWord ++ tailWord_2409059) baseStart_2409059 baseEnd_2409059 := by
    simpa [prefixWord, tailWord_2409059, baseEnd_2409059] using wordTrace_append hprefix tailTrace_2409059
  have hstable : (prefixWord ++ tailWord_2409059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409059).length < 2 ^ (prefixWord ++ tailWord_2409059).sum := by decide
  have hdescent : baseEnd_2409059 < baseStart_2409059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409099 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 6]
def baseStart_2409099 : Nat := 118140960795 + 2409099 * 2 ^ 59
def prefixEnd_2409099 : Nat := 4983230072969 + 3 ^ 40 * 2409099 * 2
def baseEnd_2409099 : Nat := 1237025731265975122783261

theorem tailTrace_2409099 : CollatzResearch.WordTrace tailWord_2409099 prefixEnd_2409099 1237025731265975122783261 := by
  unfold tailWord_2409099
  simp only [CollatzResearch.WordTrace]
  refine ⟨87867059099253239197790351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58578039399502159465193567 87867059099253239197790351)
  ·
    refine ⟨131800588648879858796685527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87867059099253239197790351 131800588648879858796685527)
    ·
      refine ⟨197700882973319788195028291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131800588648879858796685527 197700882973319788195028291)
      ·
        refine ⟨296551324459979682292542437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197700882973319788195028291 296551324459979682292542437)
        ·
          refine ⟨55603373336246190429851707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 296551324459979682292542437 55603373336246190429851707)
          ·
            refine ⟨83405060004369285644777561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55603373336246190429851707 83405060004369285644777561)
            ·
              refine ⟨62553795003276964233583171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83405060004369285644777561 62553795003276964233583171)
              ·
                refine ⟨93830692504915446350374757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62553795003276964233583171 93830692504915446350374757)
                ·
                  refine ⟨17593254844671646190695267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93830692504915446350374757 17593254844671646190695267)
                  ·
                    refine ⟨26389882267007469286042901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17593254844671646190695267 26389882267007469286042901)
                    ·
                      refine ⟨1237025731265975122783261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26389882267007469286042901 1237025731265975122783261)
                      ·
                        rfl

theorem cell23_2409099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 6].length) (baseStart_2409099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409099 prefixEnd_2409099 := by exact prefixLift 2409099
  have htrace : WordTrace (prefixWord ++ tailWord_2409099) baseStart_2409099 baseEnd_2409099 := by
    simpa [prefixWord, tailWord_2409099, baseEnd_2409099] using wordTrace_append hprefix tailTrace_2409099
  have hstable : (prefixWord ++ tailWord_2409099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409099).length < 2 ^ (prefixWord ++ tailWord_2409099).sum := by decide
  have hdescent : baseEnd_2409099 < baseStart_2409099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409109 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 12]
def baseStart_2409109 : Nat := 118140960795 + 2409109 * 2 ^ 59
def prefixEnd_2409109 : Nat := 4983230072969 + 3 ^ 40 * 2409109 * 2
def baseEnd_2409109 : Nat := 137447874008057787073135

theorem tailTrace_2409109 : CollatzResearch.WordTrace tailWord_2409109 prefixEnd_2409109 137447874008057787073135 := by
  unfold tailWord_2409109
  simp only [CollatzResearch.WordTrace]
  refine ⟨87867423829217010905654381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58578282552811340603769587 87867423829217010905654381)
  ·
    refine ⟨32950283935956379089620393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87867423829217010905654381 32950283935956379089620393)
    ·
      refine ⟨24712712951967284317215295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32950283935956379089620393 24712712951967284317215295)
      ·
        refine ⟨37069069427950926475822943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24712712951967284317215295 37069069427950926475822943)
        ·
          refine ⟨55603604141926389713734415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37069069427950926475822943 55603604141926389713734415)
          ·
            refine ⟨83405406212889584570601623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55603604141926389713734415 83405406212889584570601623)
            ·
              refine ⟨125108109319334376855902435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83405406212889584570601623 125108109319334376855902435)
              ·
                refine ⟨187662163979001565283853653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125108109319334376855902435 187662163979001565283853653)
                ·
                  refine ⟨137447874008057787073135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 187662163979001565283853653 137447874008057787073135)
                  ·
                    rfl

theorem cell23_2409109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_2409109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409109 prefixEnd_2409109 := by exact prefixLift 2409109
  have htrace : WordTrace (prefixWord ++ tailWord_2409109) baseStart_2409109 baseEnd_2409109 := by
    simpa [prefixWord, tailWord_2409109, baseEnd_2409109] using wordTrace_append hprefix tailTrace_2409109
  have hstable : (prefixWord ++ tailWord_2409109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409109).length < 2 ^ (prefixWord ++ tailWord_2409109).sum := by decide
  have hdescent : baseEnd_2409109 < baseStart_2409109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409120 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 4]
def baseStart_2409120 : Nat := 118140960795 + 2409120 * 2 ^ 59
def prefixEnd_2409120 : Nat := 4983230072969 + 3 ^ 40 * 2409120 * 2
def baseEnd_2409120 : Nat := 1237036514359719540620665

theorem tailTrace_2409120 : CollatzResearch.WordTrace tailWord_2409120 prefixEnd_2409120 1237036514359719540620665 := by
  unfold tailWord_2409120
  simp only [CollatzResearch.WordTrace]
  refine ⟨43933912516088579892152407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58578550021451439856203209 43933912516088579892152407)
  ·
    refine ⟨65900868774132869838228611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43933912516088579892152407 65900868774132869838228611)
    ·
      refine ⟨98851303161199304757342917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65900868774132869838228611 98851303161199304757342917)
      ·
        refine ⟨18534619342724869642001797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98851303161199304757342917 18534619342724869642001797)
        ·
          refine ⟨3475241126760913057875337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18534619342724869642001797 3475241126760913057875337)
          ·
            refine ⟨2606430845070684793406503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3475241126760913057875337 2606430845070684793406503)
            ·
              refine ⟨3909646267606027190109755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2606430845070684793406503 3909646267606027190109755)
              ·
                refine ⟨5864469401409040785164633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909646267606027190109755 5864469401409040785164633)
                ·
                  refine ⟨4398352051056780588873475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5864469401409040785164633 4398352051056780588873475)
                  ·
                    refine ⟨6597528076585170883310213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4398352051056780588873475 6597528076585170883310213)
                    ·
                      refine ⟨1237036514359719540620665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6597528076585170883310213 1237036514359719540620665)
                      ·
                        rfl

theorem cell23_2409120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_2409120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409120 prefixEnd_2409120 := by exact prefixLift 2409120
  have htrace : WordTrace (prefixWord ++ tailWord_2409120) baseStart_2409120 baseEnd_2409120 := by
    simpa [prefixWord, tailWord_2409120, baseEnd_2409120] using wordTrace_append hprefix tailTrace_2409120
  have hstable : (prefixWord ++ tailWord_2409120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409120).length < 2 ^ (prefixWord ++ tailWord_2409120).sum := by decide
  have hdescent : baseEnd_2409120 < baseStart_2409120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409129 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_2409129 : Nat := 118140960795 + 2409129 * 2 ^ 59
def prefixEnd_2409129 : Nat := 4983230072969 + 3 ^ 40 * 2409129 * 2
def baseEnd_2409129 : Nat := 1237041135685610005408123

theorem tailTrace_2409129 : CollatzResearch.WordTrace tailWord_2409129 prefixEnd_2409129 1237041135685610005408123 := by
  unfold tailWord_2409129
  simp only [CollatzResearch.WordTrace]
  refine ⟨87868153289144554321382441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58578768859429702880921627 87868153289144554321382441)
  ·
    refine ⟨65901114966858415741036831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87868153289144554321382441 65901114966858415741036831)
    ·
      refine ⟨98851672450287623611555247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65901114966858415741036831 98851672450287623611555247)
      ·
        refine ⟨148277508675431435417332871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98851672450287623611555247 148277508675431435417332871)
        ·
          refine ⟨222416263013147153125999307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148277508675431435417332871 222416263013147153125999307)
          ·
            refine ⟨333624394519720729688998961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222416263013147153125999307 333624394519720729688998961)
            ·
              refine ⟨250218295889790547266749221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333624394519720729688998961 250218295889790547266749221)
              ·
                refine ⟨46915930479335727612515479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250218295889790547266749221 46915930479335727612515479)
                ·
                  refine ⟨70373895719003591418773219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46915930479335727612515479 70373895719003591418773219)
                  ·
                    refine ⟨105560843578505387128159829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70373895719003591418773219 105560843578505387128159829)
                    ·
                      refine ⟨1237041135685610005408123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 105560843578505387128159829 1237041135685610005408123)
                      ·
                        rfl

theorem cell23_2409129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_2409129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409129 prefixEnd_2409129 := by exact prefixLift 2409129
  have htrace : WordTrace (prefixWord ++ tailWord_2409129) baseStart_2409129 baseEnd_2409129 := by
    simpa [prefixWord, tailWord_2409129, baseEnd_2409129] using wordTrace_append hprefix tailTrace_2409129
  have hstable : (prefixWord ++ tailWord_2409129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409129).length < 2 ^ (prefixWord ++ tailWord_2409129).sum := by decide
  have hdescent : baseEnd_2409129 < baseStart_2409129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409193 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 4]
def baseStart_2409193 : Nat := 118140960795 + 2409193 * 2 ^ 59
def prefixEnd_2409193 : Nat := 4983230072969 + 3 ^ 40 * 2409193 * 2
def baseEnd_2409193 : Nat := 1237073998447497755007829

theorem tailTrace_2409193 : CollatzResearch.WordTrace tailWord_2409193 prefixEnd_2409193 1237073998447497755007829 := by
  unfold tailWord_2409193
  simp only [CollatzResearch.WordTrace]
  refine ⟨87870487560912693251712233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58580325040608462167808155 87870487560912693251712233)
  ·
    refine ⟨65902865670684519938784175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87870487560912693251712233 65902865670684519938784175)
    ·
      refine ⟨98854298506026779908176263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65902865670684519938784175 98854298506026779908176263)
      ·
        refine ⟨148281447759040169862264395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98854298506026779908176263 148281447759040169862264395)
        ·
          refine ⟨222422171638560254793396593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148281447759040169862264395 222422171638560254793396593)
          ·
            refine ⟨166816628728920191095047445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222422171638560254793396593 166816628728920191095047445)
            ·
              refine ⟨7819529471668133957580349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 166816628728920191095047445 7819529471668133957580349)
              ·
                refine ⟨2932323551875550234092631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7819529471668133957580349 2932323551875550234092631)
                ·
                  refine ⟨4398485327813325351138947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932323551875550234092631 4398485327813325351138947)
                  ·
                    refine ⟨6597727991719988026708421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4398485327813325351138947 6597727991719988026708421)
                    ·
                      refine ⟨1237073998447497755007829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6597727991719988026708421 1237073998447497755007829)
                      ·
                        rfl

theorem cell23_2409193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 1, 4].length) (baseStart_2409193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409193 prefixEnd_2409193 := by exact prefixLift 2409193
  have htrace : WordTrace (prefixWord ++ tailWord_2409193) baseStart_2409193 baseEnd_2409193 := by
    simpa [prefixWord, tailWord_2409193, baseEnd_2409193] using wordTrace_append hprefix tailTrace_2409193
  have hstable : (prefixWord ++ tailWord_2409193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409193).length < 2 ^ (prefixWord ++ tailWord_2409193).sum := by decide
  have hdescent : baseEnd_2409193 < baseStart_2409193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409203 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 2, 4]
def baseStart_2409203 : Nat := 118140960795 + 2409203 * 2 ^ 59
def prefixEnd_2409203 : Nat := 4983230072969 + 3 ^ 40 * 2409203 * 2
def baseEnd_2409203 : Nat := 412359711084680905294261

theorem tailTrace_2409203 : CollatzResearch.WordTrace tailWord_2409203 prefixEnd_2409203 412359711084680905294261 := by
  unfold tailWord_2409203
  simp only [CollatzResearch.WordTrace]
  refine ⟨87870852290876464959576263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58580568193917643306384175 87870852290876464959576263)
  ·
    refine ⟨131806278436314697439364395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87870852290876464959576263 131806278436314697439364395)
    ·
      refine ⟨197709417654472046159046593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131806278436314697439364395 197709417654472046159046593)
      ·
        refine ⟨148282063240854034619284945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197709417654472046159046593 148282063240854034619284945)
        ·
          refine ⟨111211547430640525964463709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148282063240854034619284945 111211547430640525964463709)
          ·
            refine ⟨41704330286490197236673891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111211547430640525964463709 41704330286490197236673891)
            ·
              refine ⟨62556495429735295855010837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41704330286490197236673891 62556495429735295855010837)
              ·
                refine ⟨2932335723268841993203633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62556495429735295855010837 2932335723268841993203633)
                ·
                  refine ⟨2199251792451631494902725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2932335723268841993203633 2199251792451631494902725)
                  ·
                    refine ⟨412359711084680905294261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2199251792451631494902725 412359711084680905294261)
                    ·
                      rfl

theorem cell23_2409203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 4].length) (baseStart_2409203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409203 prefixEnd_2409203 := by exact prefixLift 2409203
  have htrace : WordTrace (prefixWord ++ tailWord_2409203) baseStart_2409203 baseEnd_2409203 := by
    simpa [prefixWord, tailWord_2409203, baseEnd_2409203] using wordTrace_append hprefix tailTrace_2409203
  have hstable : (prefixWord ++ tailWord_2409203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409203).length < 2 ^ (prefixWord ++ tailWord_2409203).sum := by decide
  have hdescent : baseEnd_2409203 < baseStart_2409203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409213 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_2409213 : Nat := 118140960795 + 2409213 * 2 ^ 59
def prefixEnd_2409213 : Nat := 4983230072969 + 3 ^ 40 * 2409213 * 2
def baseEnd_2409213 : Nat := 1237084268060587676757737

theorem tailTrace_2409213 : CollatzResearch.WordTrace tailWord_2409213 prefixEnd_2409213 1237084268060587676757737 := by
  unfold tailWord_2409213
  simp only [CollatzResearch.WordTrace]
  refine ⟨87871217020840236667440293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58580811347226824444960195 87871217020840236667440293)
  ·
    refine ⟨16475853191407544375145055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87871217020840236667440293 16475853191407544375145055)
    ·
      refine ⟨24713779787111316562717583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16475853191407544375145055 24713779787111316562717583)
      ·
        refine ⟨37070669680666974844076375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24713779787111316562717583 37070669680666974844076375)
        ·
          refine ⟨55606004521000462266114563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37070669680666974844076375 55606004521000462266114563)
          ·
            refine ⟨83409006781500693399171845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55606004521000462266114563 83409006781500693399171845)
            ·
              refine ⟨15639188771531380012344721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83409006781500693399171845 15639188771531380012344721)
              ·
                refine ⟨11729391578648535009258541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15639188771531380012344721 11729391578648535009258541)
                ·
                  refine ⟨4398521841993200628471953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11729391578648535009258541 4398521841993200628471953)
                  ·
                    refine ⟨3298891381494900471353965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4398521841993200628471953 3298891381494900471353965)
                    ·
                      refine ⟨1237084268060587676757737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3298891381494900471353965 1237084268060587676757737)
                      ·
                        rfl

theorem cell23_2409213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_2409213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409213 prefixEnd_2409213 := by exact prefixLift 2409213
  have htrace : WordTrace (prefixWord ++ tailWord_2409213) baseStart_2409213 baseEnd_2409213 := by
    simpa [prefixWord, tailWord_2409213, baseEnd_2409213] using wordTrace_append hprefix tailTrace_2409213
  have hstable : (prefixWord ++ tailWord_2409213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409213).length < 2 ^ (prefixWord ++ tailWord_2409213).sum := by decide
  have hdescent : baseEnd_2409213 < baseStart_2409213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409220 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_2409220 : Nat := 118140960795 + 2409220 * 2 ^ 59
def prefixEnd_2409220 : Nat := 4983230072969 + 3 ^ 40 * 2409220 * 2
def baseEnd_2409220 : Nat := 412362620808389716456735

theorem tailTrace_2409220 : CollatzResearch.WordTrace tailWord_2409220 prefixEnd_2409220 412362620808389716456735 := by
  unfold tailWord_2409220
  simp only [CollatzResearch.WordTrace]
  refine ⟨43935736165907438431472557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58580981554543251241963409 43935736165907438431472557)
  ·
    refine ⟨16475901062215289411802209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43935736165907438431472557 16475901062215289411802209)
    ·
      refine ⟨12356925796661467058851657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16475901062215289411802209 12356925796661467058851657)
      ·
        refine ⟨9267694347496100294138743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12356925796661467058851657 9267694347496100294138743)
        ·
          refine ⟨13901541521244150441208115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9267694347496100294138743 13901541521244150441208115)
          ·
            refine ⟨20852312281866225661812173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13901541521244150441208115 20852312281866225661812173)
            ·
              refine ⟨7819617105699834623179565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20852312281866225661812173 7819617105699834623179565)
              ·
                refine ⟨2932356414637437983692337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7819617105699834623179565 2932356414637437983692337)
                ·
                  refine ⟨2199267310978078487769253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2932356414637437983692337 2199267310978078487769253)
                  ·
                    refine ⟨412362620808389716456735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2199267310978078487769253 412362620808389716456735)
                    ·
                      rfl

theorem cell23_2409220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_2409220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409220 prefixEnd_2409220 := by exact prefixLift 2409220
  have htrace : WordTrace (prefixWord ++ tailWord_2409220) baseStart_2409220 baseEnd_2409220 := by
    simpa [prefixWord, tailWord_2409220, baseEnd_2409220] using wordTrace_append hprefix tailTrace_2409220
  have hstable : (prefixWord ++ tailWord_2409220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409220).length < 2 ^ (prefixWord ++ tailWord_2409220).sum := by decide
  have hdescent : baseEnd_2409220 < baseStart_2409220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409223 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_2409223 : Nat := 118140960795 + 2409223 * 2 ^ 59
def prefixEnd_2409223 : Nat := 4983230072969 + 3 ^ 40 * 2409223 * 2
def baseEnd_2409223 : Nat := 1237089402867132637632691

theorem tailTrace_2409223 : CollatzResearch.WordTrace tailWord_2409223 prefixEnd_2409223 1237089402867132637632691 := by
  unfold tailWord_2409223
  simp only [CollatzResearch.WordTrace]
  refine ⟨87871581750804008375304323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58581054500536005583536215 87871581750804008375304323)
  ·
    refine ⟨131807372626206012562956485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87871581750804008375304323 131807372626206012562956485)
    ·
      refine ⟨24713882367413627355554341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131807372626206012562956485 24713882367413627355554341)
      ·
        refine ⟨4633852943890055129166439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24713882367413627355554341 4633852943890055129166439)
        ·
          refine ⟨6950779415835082693749659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4633852943890055129166439 6950779415835082693749659)
          ·
            refine ⟨10426169123752624040624489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6950779415835082693749659 10426169123752624040624489)
            ·
              refine ⟨7819626842814468030468367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10426169123752624040624489 7819626842814468030468367)
              ·
                refine ⟨11729440264221702045702551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7819626842814468030468367 11729440264221702045702551)
                ·
                  refine ⟨17594160396332553068553827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11729440264221702045702551 17594160396332553068553827)
                  ·
                    refine ⟨26391240594498829602830741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17594160396332553068553827 26391240594498829602830741)
                    ·
                      refine ⟨1237089402867132637632691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26391240594498829602830741 1237089402867132637632691)
                      ·
                        rfl

theorem cell23_2409223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_2409223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409223 prefixEnd_2409223 := by exact prefixLift 2409223
  have htrace : WordTrace (prefixWord ++ tailWord_2409223) baseStart_2409223 baseEnd_2409223 := by
    simpa [prefixWord, tailWord_2409223, baseEnd_2409223] using wordTrace_append hprefix tailTrace_2409223
  have hstable : (prefixWord ++ tailWord_2409223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409223).length < 2 ^ (prefixWord ++ tailWord_2409223).sum := by decide
  have hdescent : baseEnd_2409223 < baseStart_2409223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409247 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 1, 2, 3]
def baseStart_2409247 : Nat := 118140960795 + 2409247 * 2 ^ 59
def prefixEnd_2409247 : Nat := 4983230072969 + 3 ^ 40 * 2409247 * 2
def baseEnd_2409247 : Nat := 1237101726402840543732581

theorem tailTrace_2409247 : CollatzResearch.WordTrace tailWord_2409247 prefixEnd_2409247 1237101726402840543732581 := by
  unfold tailWord_2409247
  simp only [CollatzResearch.WordTrace]
  refine ⟨87872457102717060474177995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58581638068478040316118663 87872457102717060474177995)
  ·
    refine ⟨131808685654075590711266993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87872457102717060474177995 131808685654075590711266993)
    ·
      refine ⟨98856514240556693033450245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131808685654075590711266993 98856514240556693033450245)
      ·
        refine ⟨18535596420104379943771921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98856514240556693033450245 18535596420104379943771921)
        ·
          refine ⟨13901697315078284957828941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18535596420104379943771921 13901697315078284957828941)
          ·
            refine ⟨5213136493154356859185853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13901697315078284957828941 5213136493154356859185853)
            ·
              refine ⟨1954926184932883822194695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5213136493154356859185853 1954926184932883822194695)
              ·
                refine ⟨2932389277399325733292043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954926184932883822194695 2932389277399325733292043)
                ·
                  refine ⟨4398583916098988599938065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932389277399325733292043 4398583916098988599938065)
                  ·
                    refine ⟨3298937937074241449953549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4398583916098988599938065 3298937937074241449953549)
                    ·
                      refine ⟨1237101726402840543732581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3298937937074241449953549 1237101726402840543732581)
                      ·
                        rfl

theorem cell23_2409247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_2409247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409247 prefixEnd_2409247 := by exact prefixLift 2409247
  have htrace : WordTrace (prefixWord ++ tailWord_2409247) baseStart_2409247 baseEnd_2409247 := by
    simpa [prefixWord, tailWord_2409247, baseEnd_2409247] using wordTrace_append hprefix tailTrace_2409247
  have hstable : (prefixWord ++ tailWord_2409247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409247).length < 2 ^ (prefixWord ++ tailWord_2409247).sum := by decide
  have hdescent : baseEnd_2409247 < baseStart_2409247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409277 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2409277 : Nat := 118140960795 + 2409277 * 2 ^ 59
def prefixEnd_2409277 : Nat := 4983230072969 + 3 ^ 40 * 2409277 * 2
def baseEnd_2409277 : Nat := 1237117130822475426357443

theorem tailTrace_2409277 : CollatzResearch.WordTrace tailWord_2409277 prefixEnd_2409277 1237117130822475426357443 := by
  unfold tailWord_2409277
  simp only [CollatzResearch.WordTrace]
  refine ⟨87873551292608375597770085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58582367528405583731846723 87873551292608375597770085)
  ·
    refine ⟨16476290867364070424581891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87873551292608375597770085 16476290867364070424581891)
    ·
      refine ⟨24714436301046105636872837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16476290867364070424581891 24714436301046105636872837)
      ·
        refine ⟨4633956806446144806913657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24714436301046105636872837 4633956806446144806913657)
        ·
          refine ⟨3475467604834608605185243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4633956806446144806913657 3475467604834608605185243)
          ·
            refine ⟨5213201407251912907777865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475467604834608605185243 5213201407251912907777865)
            ·
              refine ⟨3909901055438934680833399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5213201407251912907777865 3909901055438934680833399)
              ·
                refine ⟨5864851583158402021250099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909901055438934680833399 5864851583158402021250099)
                ·
                  refine ⟨8797277374737603031875149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5864851583158402021250099 8797277374737603031875149)
                  ·
                    refine ⟨3298979015526601136953181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8797277374737603031875149 3298979015526601136953181)
                    ·
                      refine ⟨1237117130822475426357443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3298979015526601136953181 1237117130822475426357443)
                      ·
                        rfl

theorem cell23_2409277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2409277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409277 prefixEnd_2409277 := by exact prefixLift 2409277
  have htrace : WordTrace (prefixWord ++ tailWord_2409277) baseStart_2409277 baseEnd_2409277 := by
    simpa [prefixWord, tailWord_2409277, baseEnd_2409277] using wordTrace_append hprefix tailTrace_2409277
  have hstable : (prefixWord ++ tailWord_2409277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409277).length < 2 ^ (prefixWord ++ tailWord_2409277).sum := by decide
  have hdescent : baseEnd_2409277 < baseStart_2409277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409334 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_2409334 : Nat := 118140960795 + 2409334 * 2 ^ 59
def prefixEnd_2409334 : Nat := 4983230072969 + 3 ^ 40 * 2409334 * 2
def baseEnd_2409334 : Nat := 1237146399219781703344681

theorem tailTrace_2409334 : CollatzResearch.WordTrace tailWord_2409334 prefixEnd_2409334 1237146399219781703344681 := by
  unfold tailWord_2409334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5492226890837617145787191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58583753502267916221730037 5492226890837617145787191)
  ·
    refine ⟨8238340336256425718680787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5492226890837617145787191 8238340336256425718680787)
    ·
      refine ⟨12357510504384638578021181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8238340336256425718680787 12357510504384638578021181)
      ·
        refine ⟨4634066439144239466757943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12357510504384638578021181 4634066439144239466757943)
        ·
          refine ⟨6951099658716359200136915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634066439144239466757943 6951099658716359200136915)
          ·
            refine ⟨10426649488074538800205373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6951099658716359200136915 10426649488074538800205373)
            ·
              refine ⟨3909993558027952050077015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10426649488074538800205373 3909993558027952050077015)
              ·
                refine ⟨5864990337041928075115523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3909993558027952050077015 5864990337041928075115523)
                ·
                  refine ⟨8797485505562892112673285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5864990337041928075115523 8797485505562892112673285)
                  ·
                    refine ⟨1649528532293042271126241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8797485505562892112673285 1649528532293042271126241)
                    ·
                      refine ⟨1237146399219781703344681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649528532293042271126241 1237146399219781703344681)
                      ·
                        rfl

theorem cell23_2409334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_2409334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409334 prefixEnd_2409334 := by exact prefixLift 2409334
  have htrace : WordTrace (prefixWord ++ tailWord_2409334) baseStart_2409334 baseEnd_2409334 := by
    simpa [prefixWord, tailWord_2409334, baseEnd_2409334] using wordTrace_append hprefix tailTrace_2409334
  have hstable : (prefixWord ++ tailWord_2409334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409334).length < 2 ^ (prefixWord ++ tailWord_2409334).sum := by decide
  have hdescent : baseEnd_2409334 < baseStart_2409334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409353 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 1, 7]
def baseStart_2409353 : Nat := 118140960795 + 2409353 * 2 ^ 59
def prefixEnd_2409353 : Nat := 4983230072969 + 3 ^ 40 * 2409353 * 2
def baseEnd_2409353 : Nat := 412385385117405709669031

theorem tailTrace_2409353 : CollatzResearch.WordTrace tailWord_2409353 prefixEnd_2409353 412385385117405709669031 := by
  unfold tailWord_2409353
  simp only [CollatzResearch.WordTrace]
  refine ⟨87876323240333040577536713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58584215493555360385024475 87876323240333040577536713)
  ·
    refine ⟨65907242430249780433152535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87876323240333040577536713 65907242430249780433152535)
    ·
      refine ⟨98860863645374670649728803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65907242430249780433152535 98860863645374670649728803)
      ·
        refine ⟨148291295468062005974593205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98860863645374670649728803 148291295468062005974593205)
        ·
          refine ⟨13902308950130813060118113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148291295468062005974593205 13902308950130813060118113)
          ·
            refine ⟨10426731712598109795088585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13902308950130813060118113 10426731712598109795088585)
            ·
              refine ⟨7820048784448582346316439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10426731712598109795088585 7820048784448582346316439)
              ·
                refine ⟨11730073176672873519474659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7820048784448582346316439 11730073176672873519474659)
                ·
                  refine ⟨17595109765009310279211989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11730073176672873519474659 17595109765009310279211989)
                  ·
                    refine ⟨412385385117405709669031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17595109765009310279211989 412385385117405709669031)
                    ·
                      rfl

theorem cell23_2409353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_2409353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409353 prefixEnd_2409353 := by exact prefixLift 2409353
  have htrace : WordTrace (prefixWord ++ tailWord_2409353) baseStart_2409353 baseEnd_2409353 := by
    simpa [prefixWord, tailWord_2409353, baseEnd_2409353] using wordTrace_append hprefix tailTrace_2409353
  have hstable : (prefixWord ++ tailWord_2409353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409353).length < 2 ^ (prefixWord ++ tailWord_2409353).sum := by decide
  have hdescent : baseEnd_2409353 < baseStart_2409353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409434 : List Nat := [3, 1, 1, 2, 4, 2, 1, 4, 1, 4]
def baseStart_2409434 : Nat := 118140960795 + 2409434 * 2 ^ 59
def prefixEnd_2409434 : Nat := 4983230072969 + 3 ^ 40 * 2409434 * 2
def baseEnd_2409434 : Nat := 412399249095077104031407

theorem tailTrace_2409434 : CollatzResearch.WordTrace tailWord_2409434 prefixEnd_2409434 412399249095077104031407 := by
  unfold tailWord_2409434
  simp only [CollatzResearch.WordTrace]
  refine ⟨21969819388259897852808839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58586185035359727607490237 21969819388259897852808839)
  ·
    refine ⟨32954729082389846779213259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21969819388259897852808839 32954729082389846779213259)
    ·
      refine ⟨49432093623584770168819889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32954729082389846779213259 49432093623584770168819889)
      ·
        refine ⟨37074070217688577626614917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49432093623584770168819889 37074070217688577626614917)
        ·
          refine ⟨6951388165816608304990297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37074070217688577626614917 6951388165816608304990297)
          ·
            refine ⟨5213541124362456228742723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6951388165816608304990297 5213541124362456228742723)
            ·
              refine ⟨7820311686543684343114085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5213541124362456228742723 7820311686543684343114085)
              ·
                refine ⟨1466308441226940814333891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7820311686543684343114085 1466308441226940814333891)
                ·
                  refine ⟨2199462661840411221500837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466308441226940814333891 2199462661840411221500837)
                  ·
                    refine ⟨412399249095077104031407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2199462661840411221500837 412399249095077104031407)
                    ·
                      rfl

theorem cell23_2409434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_2409434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409434 prefixEnd_2409434 := by exact prefixLift 2409434
  have htrace : WordTrace (prefixWord ++ tailWord_2409434) baseStart_2409434 baseEnd_2409434 := by
    simpa [prefixWord, tailWord_2409434, baseEnd_2409434] using wordTrace_append hprefix tailTrace_2409434
  have hstable : (prefixWord ++ tailWord_2409434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409434).length < 2 ^ (prefixWord ++ tailWord_2409434).sum := by decide
  have hdescent : baseEnd_2409434 < baseStart_2409434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409457 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 5, 1, 3]
def baseStart_2409457 : Nat := 118140960795 + 2409457 * 2 ^ 59
def prefixEnd_2409457 : Nat := 4983230072969 + 3 ^ 40 * 2409457 * 2
def baseEnd_2409457 : Nat := 1237209557340284722106615

theorem tailTrace_2409457 : CollatzResearch.WordTrace tailWord_2409457 prefixEnd_2409457 1237209557340284722106615 := by
  unfold tailWord_2409457
  simp only [CollatzResearch.WordTrace]
  refine ⟨87880116431956266339322625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58586744287970844226215083 87880116431956266339322625)
  ·
    refine ⟨65910087323967199754491969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87880116431956266339322625 65910087323967199754491969)
    ·
      refine ⟨49432565492975399815868977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65910087323967199754491969 49432565492975399815868977)
      ·
        refine ⟨37074424119731549861901733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49432565492975399815868977 37074424119731549861901733)
        ·
          refine ⟨6951454522449665599106575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37074424119731549861901733 6951454522449665599106575)
          ·
            refine ⟨10427181783674498398659863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6951454522449665599106575 10427181783674498398659863)
            ·
              refine ⟨15640772675511747597989795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10427181783674498398659863 15640772675511747597989795)
              ·
                refine ⟨23461159013267621396984693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15640772675511747597989795 23461159013267621396984693)
                ·
                  refine ⟨2199483657493839505967315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23461159013267621396984693 2199483657493839505967315)
                  ·
                    refine ⟨3299225486240759258950973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2199483657493839505967315 3299225486240759258950973)
                    ·
                      refine ⟨1237209557340284722106615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3299225486240759258950973 1237209557340284722106615)
                      ·
                        rfl

theorem cell23_2409457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_2409457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409457 prefixEnd_2409457 := by exact prefixLift 2409457
  have htrace : WordTrace (prefixWord ++ tailWord_2409457) baseStart_2409457 baseEnd_2409457 := by
    simpa [prefixWord, tailWord_2409457, baseEnd_2409457] using wordTrace_append hprefix tailTrace_2409457
  have hstable : (prefixWord ++ tailWord_2409457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409457).length < 2 ^ (prefixWord ++ tailWord_2409457).sum := by decide
  have hdescent : baseEnd_2409457 < baseStart_2409457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409507 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 1, 6]
def baseStart_2409507 : Nat := 118140960795 + 2409507 * 2 ^ 59
def prefixEnd_2409507 : Nat := 4983230072969 + 3 ^ 40 * 2409507 * 2
def baseEnd_2409507 : Nat := 412411743791003175493795

theorem tailTrace_2409507 : CollatzResearch.WordTrace tailWord_2409507 prefixEnd_2409507 412411743791003175493795 := by
  unfold tailWord_2409507
  simp only [CollatzResearch.WordTrace]
  refine ⟨87881940081775124878642775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58587960054516749919095183 87881940081775124878642775)
  ·
    refine ⟨131822910122662687317964163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87881940081775124878642775 131822910122662687317964163)
    ·
      refine ⟨197734365183994030976946245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131822910122662687317964163 197734365183994030976946245)
      ·
        refine ⟨37075193471998880808177421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197734365183994030976946245 37075193471998880808177421)
        ·
          refine ⟨13903197551999580303066533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37075193471998880808177421 13903197551999580303066533)
          ·
            refine ⟨2606849540999921306824975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13903197551999580303066533 2606849540999921306824975)
            ·
              refine ⟨3910274311499881960237463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2606849540999921306824975 3910274311499881960237463)
              ·
                refine ⟨5865411467249822940356195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3910274311499881960237463 5865411467249822940356195)
                ·
                  refine ⟨8798117200874734410534293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5865411467249822940356195 8798117200874734410534293)
                  ·
                    refine ⟨412411743791003175493795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8798117200874734410534293 412411743791003175493795)
                    ·
                      rfl

theorem cell23_2409507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 6].length) (baseStart_2409507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409507 prefixEnd_2409507 := by exact prefixLift 2409507
  have htrace : WordTrace (prefixWord ++ tailWord_2409507) baseStart_2409507 baseEnd_2409507 := by
    simpa [prefixWord, tailWord_2409507, baseEnd_2409507] using wordTrace_append hprefix tailTrace_2409507
  have hstable : (prefixWord ++ tailWord_2409507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409507).length < 2 ^ (prefixWord ++ tailWord_2409507).sum := by decide
  have hdescent : baseEnd_2409507 < baseStart_2409507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409513 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_2409513 : Nat := 118140960795 + 2409513 * 2 ^ 59
def prefixEnd_2409513 : Nat := 4983230072969 + 3 ^ 40 * 2409513 * 2
def baseEnd_2409513 : Nat := 1237238312256936503006357

theorem tailTrace_2409513 : CollatzResearch.WordTrace tailWord_2409513 prefixEnd_2409513 1237238312256936503006357 := by
  unfold tailWord_2409513
  simp only [CollatzResearch.WordTrace]
  refine ⟨87882158919753387903361193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58588105946502258602240795 87882158919753387903361193)
  ·
    refine ⟨65911619189815040927520895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87882158919753387903361193 65911619189815040927520895)
    ·
      refine ⟨98867428784722561391281343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65911619189815040927520895 98867428784722561391281343)
      ·
        refine ⟨148301143177083842086922015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98867428784722561391281343 148301143177083842086922015)
        ·
          refine ⟨222451714765625763130383023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148301143177083842086922015 222451714765625763130383023)
          ·
            refine ⟨333677572148438644695574535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222451714765625763130383023 333677572148438644695574535)
            ·
              refine ⟨500516358222657967043361803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333677572148438644695574535 500516358222657967043361803)
              ·
                refine ⟨750774537333986950565042705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500516358222657967043361803 750774537333986950565042705)
                ·
                  refine ⟨563080903000490212923782029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 750774537333986950565042705 563080903000490212923782029)
                  ·
                    refine ⟨211155338625183829846418261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 563080903000490212923782029 211155338625183829846418261)
                    ·
                      refine ⟨1237238312256936503006357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 211155338625183829846418261 1237238312256936503006357)
                      ·
                        rfl

theorem cell23_2409513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_2409513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409513 prefixEnd_2409513 := by exact prefixLift 2409513
  have htrace : WordTrace (prefixWord ++ tailWord_2409513) baseStart_2409513 baseEnd_2409513 := by
    simpa [prefixWord, tailWord_2409513, baseEnd_2409513] using wordTrace_append hprefix tailTrace_2409513
  have hstable : (prefixWord ++ tailWord_2409513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409513).length < 2 ^ (prefixWord ++ tailWord_2409513).sum := by decide
  have hdescent : baseEnd_2409513 < baseStart_2409513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409524 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_2409524 : Nat := 118140960795 + 2409524 * 2 ^ 59
def prefixEnd_2409524 : Nat := 4983230072969 + 3 ^ 40 * 2409524 * 2
def baseEnd_2409524 : Nat := 412414653514711986656269

theorem tailTrace_2409524 : CollatzResearch.WordTrace tailWord_2409524 prefixEnd_2409524 412414653514711986656269 := by
  unfold tailWord_2409524
  simp only [CollatzResearch.WordTrace]
  refine ⟨43941280061356768391005813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58588373415142357854674417 43941280061356768391005813)
  ·
    refine ⟨4119495005752197036656795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43941280061356768391005813 4119495005752197036656795)
    ·
      refine ⟨6179242508628295554985193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4119495005752197036656795 6179242508628295554985193)
      ·
        refine ⟨4634431881471221666238895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6179242508628295554985193 4634431881471221666238895)
        ·
          refine ⟨6951647822206832499358343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634431881471221666238895 6951647822206832499358343)
          ·
            refine ⟨10427471733310248749037515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6951647822206832499358343 10427471733310248749037515)
            ·
              refine ⟨15641207599965373123556273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10427471733310248749037515 15641207599965373123556273)
              ·
                refine ⟨11730905699974029842667205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15641207599965373123556273 11730905699974029842667205)
                ·
                  refine ⟨2199544818745130595500101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11730905699974029842667205 2199544818745130595500101)
                  ·
                    refine ⟨412414653514711986656269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2199544818745130595500101 412414653514711986656269)
                    ·
                      rfl

theorem cell23_2409524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_2409524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409524 prefixEnd_2409524 := by exact prefixLift 2409524
  have htrace : WordTrace (prefixWord ++ tailWord_2409524) baseStart_2409524 baseEnd_2409524 := by
    simpa [prefixWord, tailWord_2409524, baseEnd_2409524] using wordTrace_append hprefix tailTrace_2409524
  have hstable : (prefixWord ++ tailWord_2409524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409524).length < 2 ^ (prefixWord ++ tailWord_2409524).sum := by decide
  have hdescent : baseEnd_2409524 < baseStart_2409524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409534 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_2409534 : Nat := 118140960795 + 2409534 * 2 ^ 59
def prefixEnd_2409534 : Nat := 4983230072969 + 3 ^ 40 * 2409534 * 2
def baseEnd_2409534 : Nat := 1237249095350680920843761

theorem tailTrace_2409534 : CollatzResearch.WordTrace tailWord_2409534 prefixEnd_2409534 1237249095350680920843761 := by
  unfold tailWord_2409534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10985365606584663561234457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58588616568451538993250437 10985365606584663561234457)
  ·
    refine ⟨8239024204938497670925843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10985365606584663561234457 8239024204938497670925843)
    ·
      refine ⟨12358536307407746506388765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8239024204938497670925843 12358536307407746506388765)
      ·
        refine ⟨4634451115277904939895787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12358536307407746506388765 4634451115277904939895787)
        ·
          refine ⟨6951676672916857409843681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634451115277904939895787 6951676672916857409843681)
          ·
            refine ⟨5213757504687643057382761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6951676672916857409843681 5213757504687643057382761)
            ·
              refine ⟨3910318128515732293037071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5213757504687643057382761 3910318128515732293037071)
              ·
                refine ⟨5865477192773598439555607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3910318128515732293037071 5865477192773598439555607)
                ·
                  refine ⟨8798215789160397659333411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5865477192773598439555607 8798215789160397659333411)
                  ·
                    refine ⟨13197323683740596489000117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8798215789160397659333411 13197323683740596489000117)
                    ·
                      refine ⟨1237249095350680920843761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13197323683740596489000117 1237249095350680920843761)
                      ·
                        rfl

theorem cell23_2409534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_2409534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409534 prefixEnd_2409534 := by exact prefixLift 2409534
  have htrace : WordTrace (prefixWord ++ tailWord_2409534) baseStart_2409534 baseEnd_2409534 := by
    simpa [prefixWord, tailWord_2409534, baseEnd_2409534] using wordTrace_append hprefix tailTrace_2409534
  have hstable : (prefixWord ++ tailWord_2409534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409534).length < 2 ^ (prefixWord ++ tailWord_2409534).sum := by decide
  have hdescent : baseEnd_2409534 < baseStart_2409534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409537 : List Nat := [1, 2, 5, 1, 3, 2, 9]
def baseStart_2409537 : Nat := 118140960795 + 2409537 * 2 ^ 59
def prefixEnd_2409537 : Nat := 4983230072969 + 3 ^ 40 * 2409537 * 2
def baseEnd_2409537 : Nat := 15274699207316597643287

theorem tailTrace_2409537 : CollatzResearch.WordTrace tailWord_2409537 prefixEnd_2409537 15274699207316597643287 := by
  unfold tailWord_2409537
  simp only [CollatzResearch.WordTrace]
  refine ⟨87883034271666440002234865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58588689514444293334823243 87883034271666440002234865)
  ·
    refine ⟨65912275703749830001676149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87883034271666440002234865 65912275703749830001676149)
    ·
      refine ⟨6179275847226546562657139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65912275703749830001676149 6179275847226546562657139)
      ·
        refine ⟨9268913770839819843985709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6179275847226546562657139 9268913770839819843985709)
        ·
          refine ⟨3475842664064932441494641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9268913770839819843985709 3475842664064932441494641)
          ·
            refine ⟨2606881998048699331120981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3475842664064932441494641 2606881998048699331120981)
            ·
              refine ⟨15274699207316597643287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2606881998048699331120981 15274699207316597643287)
              ·
                rfl

theorem cell23_2409537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 9].length) (baseStart_2409537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409537 prefixEnd_2409537 := by exact prefixLift 2409537
  have htrace : WordTrace (prefixWord ++ tailWord_2409537) baseStart_2409537 baseEnd_2409537 := by
    simpa [prefixWord, tailWord_2409537, baseEnd_2409537] using wordTrace_append hprefix tailTrace_2409537
  have hstable : (prefixWord ++ tailWord_2409537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409537).length < 2 ^ (prefixWord ++ tailWord_2409537).sum := by decide
  have hdescent : baseEnd_2409537 < baseStart_2409537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409550 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_2409550 : Nat := 118140960795 + 2409550 * 2 ^ 59
def prefixEnd_2409550 : Nat := 4983230072969 + 3 ^ 40 * 2409550 * 2
def baseEnd_2409550 : Nat := 412419103680384286081229

theorem tailTrace_2409550 : CollatzResearch.WordTrace tailWord_2409550 prefixEnd_2409550 412419103680384286081229 := by
  unfold tailWord_2409550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10985438552577417902807263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58589005613746228814972069 10985438552577417902807263)
  ·
    refine ⟨16478157828866126854210895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10985438552577417902807263 16478157828866126854210895)
    ·
      refine ⟨24717236743299190281316343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16478157828866126854210895 24717236743299190281316343)
      ·
        refine ⟨37075855114948785421974515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24717236743299190281316343 37075855114948785421974515)
        ·
          refine ⟨55613782672423178132961773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37075855114948785421974515 55613782672423178132961773)
          ·
            refine ⟨20855168502158691799860665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55613782672423178132961773 20855168502158691799860665)
            ·
              refine ⟨15641376376619018849895499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20855168502158691799860665 15641376376619018849895499)
              ·
                refine ⟨23462064564928528274843249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15641376376619018849895499 23462064564928528274843249)
                ·
                  refine ⟨17596548423696396206132437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23462064564928528274843249 17596548423696396206132437)
                  ·
                    refine ⟨412419103680384286081229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17596548423696396206132437 412419103680384286081229)
                    ·
                      rfl

theorem cell23_2409550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_2409550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409550 prefixEnd_2409550 := by exact prefixLift 2409550
  have htrace : WordTrace (prefixWord ++ tailWord_2409550) baseStart_2409550 baseEnd_2409550 := by
    simpa [prefixWord, tailWord_2409550, baseEnd_2409550] using wordTrace_append hprefix tailTrace_2409550
  have hstable : (prefixWord ++ tailWord_2409550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409550).length < 2 ^ (prefixWord ++ tailWord_2409550).sum := by decide
  have hdescent : baseEnd_2409550 < baseStart_2409550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409558 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2409558 : Nat := 118140960795 + 2409558 * 2 ^ 59
def prefixEnd_2409558 : Nat := 4983230072969 + 3 ^ 40 * 2409558 * 2
def baseEnd_2409558 : Nat := 412420472962129608981217

theorem tailTrace_2409558 : CollatzResearch.WordTrace tailWord_2409558 prefixEnd_2409558 412420472962129608981217 := by
  unfold tailWord_2409558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5492737512786897536796833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58589200136393573725832885 5492737512786897536796833)
  ·
    refine ⟨4119553134590173152597625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5492737512786897536796833 4119553134590173152597625)
    ·
      refine ⟨3089664850942629864448219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4119553134590173152597625 3089664850942629864448219)
      ·
        refine ⟨4634497276413944796672329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3089664850942629864448219 4634497276413944796672329)
        ·
          refine ⟨3475872957310458597504247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4634497276413944796672329 3475872957310458597504247)
          ·
            refine ⟨5213809435965687896256371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475872957310458597504247 5213809435965687896256371)
            ·
              refine ⟨7820714153948531844384557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5213809435965687896256371 7820714153948531844384557)
              ·
                refine ⟨2932767807730699441644209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7820714153948531844384557 2932767807730699441644209)
                ·
                  refine ⟨2199575855798024581233157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2932767807730699441644209 2199575855798024581233157)
                  ·
                    refine ⟨412420472962129608981217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2199575855798024581233157 412420472962129608981217)
                    ·
                      rfl

theorem cell23_2409558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2409558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409558 prefixEnd_2409558 := by exact prefixLift 2409558
  have htrace : WordTrace (prefixWord ++ tailWord_2409558) baseStart_2409558 baseEnd_2409558 := by
    simpa [prefixWord, tailWord_2409558, baseEnd_2409558] using wordTrace_append hprefix tailTrace_2409558
  have hstable : (prefixWord ++ tailWord_2409558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409558).length < 2 ^ (prefixWord ++ tailWord_2409558).sum := by decide
  have hdescent : baseEnd_2409558 < baseStart_2409558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409591 : List Nat := [1, 1, 3, 1, 1, 4, 5, 1, 1, 3, 2]
def baseStart_2409591 : Nat := 118140960795 + 2409591 * 2 ^ 59
def prefixEnd_2409591 : Nat := 4983230072969 + 3 ^ 40 * 2409591 * 2
def baseEnd_2409591 : Nat := 1237278363747987197830999

theorem tailTrace_2409591 : CollatzResearch.WordTrace tailWord_2409591 prefixEnd_2409591 1237278363747987197830999 := by
  unfold tailWord_2409591
  simp only [CollatzResearch.WordTrace]
  refine ⟨87885003813470807224700627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58590002542313871483133751 87885003813470807224700627)
  ·
    refine ⟨131827505720206210837050941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87885003813470807224700627 131827505720206210837050941)
    ·
      refine ⟨49435314645077329063894103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131827505720206210837050941 49435314645077329063894103)
      ·
        refine ⟨74152971967615993595841155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49435314645077329063894103 74152971967615993595841155)
        ·
          refine ⟨111229457951423990393761733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74152971967615993595841155 111229457951423990393761733)
          ·
            refine ⟨20855523365891998198830325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111229457951423990393761733 20855523365891998198830325)
            ·
              refine ⟨1955205315552374831140343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20855523365891998198830325 1955205315552374831140343)
              ·
                refine ⟨2932807973328562246710515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955205315552374831140343 2932807973328562246710515)
                ·
                  refine ⟨4399211959992843370065773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932807973328562246710515 4399211959992843370065773)
                  ·
                    refine ⟨1649704484997316263774665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4399211959992843370065773 1649704484997316263774665)
                    ·
                      refine ⟨1237278363747987197830999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649704484997316263774665 1237278363747987197830999)
                      ·
                        rfl

theorem cell23_2409591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 1, 3, 2].length) (baseStart_2409591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409591 prefixEnd_2409591 := by exact prefixLift 2409591
  have htrace : WordTrace (prefixWord ++ tailWord_2409591) baseStart_2409591 baseEnd_2409591 := by
    simpa [prefixWord, tailWord_2409591, baseEnd_2409591] using wordTrace_append hprefix tailTrace_2409591
  have hstable : (prefixWord ++ tailWord_2409591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409591).length < 2 ^ (prefixWord ++ tailWord_2409591).sum := by decide
  have hdescent : baseEnd_2409591 < baseStart_2409591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409784 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 2, 6, 2]
def baseStart_2409784 : Nat := 118140960795 + 2409784 * 2 ^ 59
def prefixEnd_2409784 : Nat := 4983230072969 + 3 ^ 40 * 2409784 * 2
def baseEnd_2409784 : Nat := 1237377465514304942717611

theorem tailTrace_2409784 : CollatzResearch.WordTrace tailWord_2409784 prefixEnd_2409784 1237377465514304942717611 := by
  unfold tailWord_2409784
  simp only [CollatzResearch.WordTrace]
  refine ⟨43946021550885800593238203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58594695401181067457650937 43946021550885800593238203)
  ·
    refine ⟨65919032326328700889857305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43946021550885800593238203 65919032326328700889857305)
    ·
      refine ⟨49439274244746525667392979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65919032326328700889857305 49439274244746525667392979)
      ·
        refine ⟨74158911367119788501089469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49439274244746525667392979 74158911367119788501089469)
        ·
          refine ⟨27809591762669920687908551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74158911367119788501089469 27809591762669920687908551)
          ·
            refine ⟨41714387644004881031862827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27809591762669920687908551 41714387644004881031862827)
            ·
              refine ⟨62571581466007321547794241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41714387644004881031862827 62571581466007321547794241)
              ·
                refine ⟨46928686099505491160845681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62571581466007321547794241 46928686099505491160845681)
                ·
                  refine ⟨35196514574629118370634261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46928686099505491160845681 35196514574629118370634261)
                  ·
                    refine ⟨1649836620685739923623481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35196514574629118370634261 1649836620685739923623481)
                    ·
                      refine ⟨1237377465514304942717611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649836620685739923623481 1237377465514304942717611)
                      ·
                        rfl

theorem cell23_2409784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 6, 2].length) (baseStart_2409784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409784 prefixEnd_2409784 := by exact prefixLift 2409784
  have htrace : WordTrace (prefixWord ++ tailWord_2409784) baseStart_2409784 baseEnd_2409784 := by
    simpa [prefixWord, tailWord_2409784, baseEnd_2409784] using wordTrace_append hprefix tailTrace_2409784
  have hstable : (prefixWord ++ tailWord_2409784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409784).length < 2 ^ (prefixWord ++ tailWord_2409784).sum := by decide
  have hdescent : baseEnd_2409784 < baseStart_2409784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409797 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_2409797 : Nat := 118140960795 + 2409797 * 2 ^ 59
def prefixEnd_2409797 : Nat := 4983230072969 + 3 ^ 40 * 2409797 * 2
def baseEnd_2409797 : Nat := 1237384140762813391855051

theorem tailTrace_2409797 : CollatzResearch.WordTrace tailWord_2409797 prefixEnd_2409797 1237384140762813391855051 := by
  unfold tailWord_2409797
  simp only [CollatzResearch.WordTrace]
  refine ⟨87892517250724504406699645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58595011500483002937799763 87892517250724504406699645)
  ·
    refine ⟨32959693969021689152512367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87892517250724504406699645 32959693969021689152512367)
    ·
      refine ⟨49439540953532533728768551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32959693969021689152512367 49439540953532533728768551)
      ·
        refine ⟨74159311430298800593152827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49439540953532533728768551 74159311430298800593152827)
        ·
          refine ⟨111238967145448200889729241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74159311430298800593152827 111238967145448200889729241)
          ·
            refine ⟨83429225359086150667296931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111238967145448200889729241 83429225359086150667296931)
            ·
              refine ⟨125143838038629226000945397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83429225359086150667296931 125143838038629226000945397)
              ·
                refine ⟨11732234816121489937588631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125143838038629226000945397 11732234816121489937588631)
                ·
                  refine ⟨17598352224182234906382947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11732234816121489937588631 17598352224182234906382947)
                  ·
                    refine ⟨26397528336273352359574421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17598352224182234906382947 26397528336273352359574421)
                    ·
                      refine ⟨1237384140762813391855051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26397528336273352359574421 1237384140762813391855051)
                      ·
                        rfl

theorem cell23_2409797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_2409797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409797 prefixEnd_2409797 := by exact prefixLift 2409797
  have htrace : WordTrace (prefixWord ++ tailWord_2409797) baseStart_2409797 baseEnd_2409797 := by
    simpa [prefixWord, tailWord_2409797, baseEnd_2409797] using wordTrace_append hprefix tailTrace_2409797
  have hstable : (prefixWord ++ tailWord_2409797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409797).length < 2 ^ (prefixWord ++ tailWord_2409797).sum := by decide
  have hdescent : baseEnd_2409797 < baseStart_2409797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409801 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 5, 2, 2]
def baseStart_2409801 : Nat := 118140960795 + 2409801 * 2 ^ 59
def prefixEnd_2409801 : Nat := 4983230072969 + 3 ^ 40 * 2409801 * 2
def baseEnd_2409801 : Nat := 1237386194685431376205033

theorem tailTrace_2409801 : CollatzResearch.WordTrace tailWord_2409801 prefixEnd_2409801 1237386194685431376205033 := by
  unfold tailWord_2409801
  simp only [CollatzResearch.WordTrace]
  refine ⟨87892663142710013089845257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58595108761806675393230171 87892663142710013089845257)
  ·
    refine ⟨65919497357032509817383943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87892663142710013089845257 65919497357032509817383943)
    ·
      refine ⟨98879246035548764726075915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65919497357032509817383943 98879246035548764726075915)
      ·
        refine ⟨148318869053323147089113873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98879246035548764726075915 148318869053323147089113873)
        ·
          refine ⟨111239151789992360316835405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148318869053323147089113873 111239151789992360316835405)
          ·
            refine ⟨41714681921247135118813277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111239151789992360316835405 41714681921247135118813277)
            ·
              refine ⟨15643005720467675669554979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41714681921247135118813277 15643005720467675669554979)
              ·
                refine ⟨23464508580701513504332469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15643005720467675669554979 23464508580701513504332469)
                ·
                  refine ⟨2199797679440766891031169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23464508580701513504332469 2199797679440766891031169)
                  ·
                    refine ⟨1649848259580575168273377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2199797679440766891031169 1649848259580575168273377)
                    ·
                      refine ⟨1237386194685431376205033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649848259580575168273377 1237386194685431376205033)
                      ·
                        rfl

theorem cell23_2409801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 2, 2].length) (baseStart_2409801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409801 prefixEnd_2409801 := by exact prefixLift 2409801
  have htrace : WordTrace (prefixWord ++ tailWord_2409801) baseStart_2409801 baseEnd_2409801 := by
    simpa [prefixWord, tailWord_2409801, baseEnd_2409801] using wordTrace_append hprefix tailTrace_2409801
  have hstable : (prefixWord ++ tailWord_2409801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409801).length < 2 ^ (prefixWord ++ tailWord_2409801).sum := by decide
  have hdescent : baseEnd_2409801 < baseStart_2409801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409805 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_2409805 : Nat := 118140960795 + 2409805 * 2 ^ 59
def prefixEnd_2409805 : Nat := 4983230072969 + 3 ^ 40 * 2409805 * 2
def baseEnd_2409805 : Nat := 1237388248608049360555015

theorem tailTrace_2409805 : CollatzResearch.WordTrace tailWord_2409805 prefixEnd_2409805 1237388248608049360555015 := by
  unfold tailWord_2409805
  simp only [CollatzResearch.WordTrace]
  refine ⟨87892809034695521772990869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58595206023130347848660579 87892809034695521772990869)
  ·
    refine ⟨4119975423501352583108947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87892809034695521772990869 4119975423501352583108947)
    ·
      refine ⟨6179963135252028874663421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4119975423501352583108947 6179963135252028874663421)
      ·
        refine ⟨2317486175719510827998783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6179963135252028874663421 2317486175719510827998783)
        ·
          refine ⟨3476229263579266241998175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2317486175719510827998783 3476229263579266241998175)
          ·
            refine ⟨5214343895368899362997263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3476229263579266241998175 5214343895368899362997263)
            ·
              refine ⟨7821515843053349044495895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5214343895368899362997263 7821515843053349044495895)
              ·
                refine ⟨11732273764580023566743843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7821515843053349044495895 11732273764580023566743843)
                ·
                  refine ⟨17598410646870035350115765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11732273764580023566743843 17598410646870035350115765)
                  ·
                    refine ⟨1649850998144065814073353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17598410646870035350115765 1649850998144065814073353)
                    ·
                      refine ⟨1237388248608049360555015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649850998144065814073353 1237388248608049360555015)
                      ·
                        rfl

theorem cell23_2409805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_2409805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409805 prefixEnd_2409805 := by exact prefixLift 2409805
  have htrace : WordTrace (prefixWord ++ tailWord_2409805) baseStart_2409805 baseEnd_2409805 := by
    simpa [prefixWord, tailWord_2409805, baseEnd_2409805] using wordTrace_append hprefix tailTrace_2409805
  have hstable : (prefixWord ++ tailWord_2409805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409805).length < 2 ^ (prefixWord ++ tailWord_2409805).sum := by decide
  have hdescent : baseEnd_2409805 < baseStart_2409805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409828 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_2409828 : Nat := 118140960795 + 2409828 * 2 ^ 59
def prefixEnd_2409828 : Nat := 4983230072969 + 3 ^ 40 * 2409828 * 2
def baseEnd_2409828 : Nat := 412466686221034256855803

theorem tailTrace_2409828 : CollatzResearch.WordTrace tailWord_2409828 prefixEnd_2409828 412466686221034256855803 := by
  unfold tailWord_2409828
  simp only [CollatzResearch.WordTrace]
  refine ⟨43946823956806098350539069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58595765275741464467385425 43946823956806098350539069)
  ·
    refine ⟨16480058983802286881452151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43946823956806098350539069 16480058983802286881452151)
    ·
      refine ⟨24720088475703430322178227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16480058983802286881452151 24720088475703430322178227)
      ·
        refine ⟨37080132713555145483267341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24720088475703430322178227 37080132713555145483267341)
        ·
          refine ⟨13905049767583179556225253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37080132713555145483267341 13905049767583179556225253)
          ·
            refine ⟨2607196831421846166792235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13905049767583179556225253 2607196831421846166792235)
            ·
              refine ⟨3910795247132769250188353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607196831421846166792235 3910795247132769250188353)
              ·
                refine ⟨2933096435349576937641265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3910795247132769250188353 2933096435349576937641265)
                ·
                  refine ⟨2199822326512182703230949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2933096435349576937641265 2199822326512182703230949)
                  ·
                    refine ⟨412466686221034256855803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2199822326512182703230949 412466686221034256855803)
                    ·
                      rfl

theorem cell23_2409828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_2409828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409828 prefixEnd_2409828 := by exact prefixLift 2409828
  have htrace : WordTrace (prefixWord ++ tailWord_2409828) baseStart_2409828 baseEnd_2409828 := by
    simpa [prefixWord, tailWord_2409828, baseEnd_2409828] using wordTrace_append hprefix tailTrace_2409828
  have hstable : (prefixWord ++ tailWord_2409828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409828).length < 2 ^ (prefixWord ++ tailWord_2409828).sum := by decide
  have hdescent : baseEnd_2409828 < baseStart_2409828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409838 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2409838 : Nat := 118140960795 + 2409838 * 2 ^ 59
def prefixEnd_2409838 : Nat := 4983230072969 + 3 ^ 40 * 2409838 * 2
def baseEnd_2409838 : Nat := 1237405193469647731442363

theorem tailTrace_2409838 : CollatzResearch.WordTrace tailWord_2409838 prefixEnd_2409838 1237405193469647731442363 := by
  unfold tailWord_2409838
  simp only [CollatzResearch.WordTrace]
  refine ⟨10986751580446996051117771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58596008429050645605961445 10986751580446996051117771)
  ·
    refine ⟨16480127370670494076676657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10986751580446996051117771 16480127370670494076676657)
    ·
      refine ⟨12360095528002870557507493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16480127370670494076676657 12360095528002870557507493)
      ·
        refine ⟨2317517911500538229532655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12360095528002870557507493 2317517911500538229532655)
        ·
          refine ⟨3476276867250807344298983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2317517911500538229532655 3476276867250807344298983)
          ·
            refine ⟨5214415300876211016448475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3476276867250807344298983 5214415300876211016448475)
            ·
              refine ⟨7821622951314316524672713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5214415300876211016448475 7821622951314316524672713)
              ·
                refine ⟨5866217213485737393504535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7821622951314316524672713 5866217213485737393504535)
                ·
                  refine ⟨8799325820228606090256803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5866217213485737393504535 8799325820228606090256803)
                  ·
                    refine ⟨13198988730342909135385205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8799325820228606090256803 13198988730342909135385205)
                    ·
                      refine ⟨1237405193469647731442363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13198988730342909135385205 1237405193469647731442363)
                      ·
                        rfl

theorem cell23_2409838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2409838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409838 prefixEnd_2409838 := by exact prefixLift 2409838
  have htrace : WordTrace (prefixWord ++ tailWord_2409838) baseStart_2409838 baseEnd_2409838 := by
    simpa [prefixWord, tailWord_2409838, baseEnd_2409838] using wordTrace_append hprefix tailTrace_2409838
  have hstable : (prefixWord ++ tailWord_2409838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409838).length < 2 ^ (prefixWord ++ tailWord_2409838).sum := by decide
  have hdescent : baseEnd_2409838 < baseStart_2409838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409845 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2409845 : Nat := 118140960795 + 2409845 * 2 ^ 59
def prefixEnd_2409845 : Nat := 4983230072969 + 3 ^ 40 * 2409845 * 2
def baseEnd_2409845 : Nat := 412469595944743068018277

theorem tailTrace_2409845 : CollatzResearch.WordTrace tailWord_2409845 prefixEnd_2409845 412469595944743068018277 := by
  unfold tailWord_2409845
  simp only [CollatzResearch.WordTrace]
  refine ⟨87894267954550608604446989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58596178636367072402964659 87894267954550608604446989)
  ·
    refine ⟨32960350482956478226667621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87894267954550608604446989 32960350482956478226667621)
    ·
      refine ⟨6180065715554339667500179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32960350482956478226667621 6180065715554339667500179)
      ·
        refine ⟨9270098573331509501250269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6180065715554339667500179 9270098573331509501250269)
        ·
          refine ⟨3476286964999316062968851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9270098573331509501250269 3476286964999316062968851)
          ·
            refine ⟨5214430447498974094453277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3476286964999316062968851 5214430447498974094453277)
            ·
              refine ⟨1955411417812115285419979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5214430447498974094453277 1955411417812115285419979)
              ·
                refine ⟨2933117126718172928129969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955411417812115285419979 2933117126718172928129969)
                ·
                  refine ⟨2199837845038629696097477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2933117126718172928129969 2199837845038629696097477)
                  ·
                    refine ⟨412469595944743068018277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2199837845038629696097477 412469595944743068018277)
                    ·
                      rfl

theorem cell23_2409845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2409845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409845 prefixEnd_2409845 := by exact prefixLift 2409845
  have htrace : WordTrace (prefixWord ++ tailWord_2409845) baseStart_2409845 baseEnd_2409845 := by
    simpa [prefixWord, tailWord_2409845, baseEnd_2409845] using wordTrace_append hprefix tailTrace_2409845
  have hstable : (prefixWord ++ tailWord_2409845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409845).length < 2 ^ (prefixWord ++ tailWord_2409845).sum := by decide
  have hdescent : baseEnd_2409845 < baseStart_2409845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409858 : List Nat := [3, 4, 2, 1, 1, 1, 4, 7]
def baseStart_2409858 : Nat := 118140960795 + 2409858 * 2 ^ 59
def prefixEnd_2409858 : Nat := 4983230072969 + 3 ^ 40 * 2409858 * 2
def baseEnd_2409858 : Nat := 45830202336397690858973

theorem tailTrace_2409858 : CollatzResearch.WordTrace tailWord_2409858 prefixEnd_2409858 45830202336397690858973 := by
  unfold tailWord_2409858
  simp only [CollatzResearch.WordTrace]
  refine ⟨21973685525875877956167557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58596494735669007883113485 21973685525875877956167557)
  ·
    refine ⟨4120066036101727116781417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21973685525875877956167557 4120066036101727116781417)
    ·
      refine ⟨3090049527076295337586063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4120066036101727116781417 3090049527076295337586063)
      ·
        refine ⟨4635074290614443006379095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3090049527076295337586063 4635074290614443006379095)
        ·
          refine ⟨6952611435921664509568643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4635074290614443006379095 6952611435921664509568643)
          ·
            refine ⟨10428917153882496764352965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6952611435921664509568643 10428917153882496764352965)
            ·
              refine ⟨1955421966352968143316181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10428917153882496764352965 1955421966352968143316181)
              ·
                refine ⟨45830202336397690858973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1955421966352968143316181 45830202336397690858973)
                ·
                  rfl

theorem cell23_2409858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 7].length) (baseStart_2409858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409858 prefixEnd_2409858 := by exact prefixLift 2409858
  have htrace : WordTrace (prefixWord ++ tailWord_2409858) baseStart_2409858 baseEnd_2409858 := by
    simpa [prefixWord, tailWord_2409858, baseEnd_2409858] using wordTrace_append hprefix tailTrace_2409858
  have hstable : (prefixWord ++ tailWord_2409858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409858).length < 2 ^ (prefixWord ++ tailWord_2409858).sum := by decide
  have hdescent : baseEnd_2409858 < baseStart_2409858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409861 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 3, 3, 2]
def baseStart_2409861 : Nat := 118140960795 + 2409861 * 2 ^ 59
def prefixEnd_2409861 : Nat := 4983230072969 + 3 ^ 40 * 2409861 * 2
def baseEnd_2409861 : Nat := 1237417003524701141454757

theorem tailTrace_2409861 : CollatzResearch.WordTrace tailWord_2409861 prefixEnd_2409861 1237417003524701141454757 := by
  unfold tailWord_2409861
  simp only [CollatzResearch.WordTrace]
  refine ⟨87894851522492643337029437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58596567681661762224686291 87894851522492643337029437)
  ·
    refine ⟨32960569320934741251386039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87894851522492643337029437 32960569320934741251386039)
    ·
      refine ⟨49440853981402111877079059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32960569320934741251386039 49440853981402111877079059)
      ·
        refine ⟨74161280972103167815618589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49440853981402111877079059 74161280972103167815618589)
        ·
          refine ⟨27810480364538687930856971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74161280972103167815618589 27810480364538687930856971)
          ·
            refine ⟨41715720546808031896285457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27810480364538687930856971 41715720546808031896285457)
            ·
              refine ⟨31286790410106023922214093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41715720546808031896285457 31286790410106023922214093)
              ·
                refine ⟨11732546403789758970830285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31286790410106023922214093 11732546403789758970830285)
                ·
                  refine ⟨4399704901421159614061357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11732546403789758970830285 4399704901421159614061357)
                  ·
                    refine ⟨1649889338032934855273009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4399704901421159614061357 1649889338032934855273009)
                    ·
                      refine ⟨1237417003524701141454757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649889338032934855273009 1237417003524701141454757)
                      ·
                        rfl

theorem cell23_2409861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 3, 2].length) (baseStart_2409861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409861 prefixEnd_2409861 := by exact prefixLift 2409861
  have htrace : WordTrace (prefixWord ++ tailWord_2409861) baseStart_2409861 baseEnd_2409861 := by
    simpa [prefixWord, tailWord_2409861, baseEnd_2409861] using wordTrace_append hprefix tailTrace_2409861
  have hstable : (prefixWord ++ tailWord_2409861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409861).length < 2 ^ (prefixWord ++ tailWord_2409861).sum := by decide
  have hdescent : baseEnd_2409861 < baseStart_2409861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409864 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2409864 : Nat := 118140960795 + 2409864 * 2 ^ 59
def prefixEnd_2409864 : Nat := 4983230072969 + 3 ^ 40 * 2409864 * 2
def baseEnd_2409864 : Nat := 1237418543966664629717243

theorem tailTrace_2409864 : CollatzResearch.WordTrace tailWord_2409864 prefixEnd_2409864 1237418543966664629717243 := by
  unfold tailWord_2409864
  simp only [CollatzResearch.WordTrace]
  refine ⟨43947480470740887424694323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58596640627654516566259097 43947480470740887424694323)
  ·
    refine ⟨65921220706111331137041485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43947480470740887424694323 65921220706111331137041485)
    ·
      refine ⟨24720457764791749176390557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65921220706111331137041485 24720457764791749176390557)
      ·
        refine ⟨9270171661796905941146459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24720457764791749176390557 9270171661796905941146459)
        ·
          refine ⟨13905257492695358911719689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9270171661796905941146459 13905257492695358911719689)
          ·
            refine ⟨10428943119521519183789767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13905257492695358911719689 10428943119521519183789767)
            ·
              refine ⟨15643414679282278775684651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10428943119521519183789767 15643414679282278775684651)
              ·
                refine ⟨23465122018923418163526977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15643414679282278775684651 23465122018923418163526977)
                ·
                  refine ⟨17598841514192563622645233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23465122018923418163526977 17598841514192563622645233)
                  ·
                    refine ⟨13199131135644422716983925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17598841514192563622645233 13199131135644422716983925)
                    ·
                      refine ⟨1237418543966664629717243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13199131135644422716983925 1237418543966664629717243)
                      ·
                        rfl

theorem cell23_2409864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2409864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409864 prefixEnd_2409864 := by exact prefixLift 2409864
  have htrace : WordTrace (prefixWord ++ tailWord_2409864) baseStart_2409864 baseEnd_2409864 := by
    simpa [prefixWord, tailWord_2409864, baseEnd_2409864] using wordTrace_append hprefix tailTrace_2409864
  have hstable : (prefixWord ++ tailWord_2409864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409864).length < 2 ^ (prefixWord ++ tailWord_2409864).sum := by decide
  have hdescent : baseEnd_2409864 < baseStart_2409864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409886 : List Nat := [4, 3, 1, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_2409886 : Nat := 118140960795 + 2409886 * 2 ^ 59
def prefixEnd_2409886 : Nat := 4983230072969 + 3 ^ 40 * 2409886 * 2
def baseEnd_2409886 : Nat := 1237429840541063543642143

theorem tailTrace_2409886 : CollatzResearch.WordTrace tailWord_2409886 prefixEnd_2409886 1237429840541063543642143 := by
  unfold tailWord_2409886
  simp only [CollatzResearch.WordTrace]
  refine ⟨10986970418425259075836189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58597175564934715071126341 10986970418425259075836189)
  ·
    refine ⟨4120113906909472153438571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10986970418425259075836189 4120113906909472153438571)
    ·
      refine ⟨6180170860364208230157857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4120113906909472153438571 6180170860364208230157857)
      ·
        refine ⟨4635128145273156172618393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6180170860364208230157857 4635128145273156172618393)
        ·
          refine ⟨3476346108954867129463795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4635128145273156172618393 3476346108954867129463795)
          ·
            refine ⟨5214519163432300694195693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3476346108954867129463795 5214519163432300694195693)
            ·
              refine ⟨1955444686287112760323385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5214519163432300694195693 1955444686287112760323385)
              ·
                refine ⟨1466583514715334570242539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1955444686287112760323385 1466583514715334570242539)
                ·
                  refine ⟨2199875272073001855363809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466583514715334570242539 2199875272073001855363809)
                  ·
                    refine ⟨1649906454054751391522857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2199875272073001855363809 1649906454054751391522857)
                    ·
                      refine ⟨1237429840541063543642143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649906454054751391522857 1237429840541063543642143)
                      ·
                        rfl

theorem cell23_2409886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_2409886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409886 prefixEnd_2409886 := by exact prefixLift 2409886
  have htrace : WordTrace (prefixWord ++ tailWord_2409886) baseStart_2409886 baseEnd_2409886 := by
    simpa [prefixWord, tailWord_2409886, baseEnd_2409886] using wordTrace_append hprefix tailTrace_2409886
  have hstable : (prefixWord ++ tailWord_2409886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409886).length < 2 ^ (prefixWord ++ tailWord_2409886).sum := by decide
  have hdescent : baseEnd_2409886 < baseStart_2409886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409941 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2409941 : Nat := 118140960795 + 2409941 * 2 ^ 59
def prefixEnd_2409941 : Nat := 4983230072969 + 3 ^ 40 * 2409941 * 2
def baseEnd_2409941 : Nat := 1237458081977060828454389

theorem tailTrace_2409941 : CollatzResearch.WordTrace tailWord_2409941 prefixEnd_2409941 1237458081977060828454389 := by
  unfold tailWord_2409941
  simp only [CollatzResearch.WordTrace]
  refine ⟨87897769362202816999941677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58598512908135211333294451 87897769362202816999941677)
  ·
    refine ⟨32961663510826056374978129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87897769362202816999941677 32961663510826056374978129)
    ·
      refine ⟨24721247633119542281233597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32961663510826056374978129 24721247633119542281233597)
      ·
        refine ⟨9270467862419828355462599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24721247633119542281233597 9270467862419828355462599)
        ·
          refine ⟨13905701793629742533193899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9270467862419828355462599 13905701793629742533193899)
          ·
            refine ⟨20858552690444613799790849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13905701793629742533193899 20858552690444613799790849)
            ·
              refine ⟨15643914517833460349843137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20858552690444613799790849 15643914517833460349843137)
              ·
                refine ⟨11732935888375095262382353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15643914517833460349843137 11732935888375095262382353)
                ·
                  refine ⟨8799701916281321446786765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11732935888375095262382353 8799701916281321446786765)
                  ·
                    refine ⟨3299888218605495542545037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8799701916281321446786765 3299888218605495542545037)
                    ·
                      refine ⟨1237458081977060828454389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3299888218605495542545037 1237458081977060828454389)
                      ·
                        rfl

theorem cell23_2409941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2409941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409941 prefixEnd_2409941 := by exact prefixLift 2409941
  have htrace : WordTrace (prefixWord ++ tailWord_2409941) baseStart_2409941 baseEnd_2409941 := by
    simpa [prefixWord, tailWord_2409941, baseEnd_2409941] using wordTrace_append hprefix tailTrace_2409941
  have hstable : (prefixWord ++ tailWord_2409941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409941).length < 2 ^ (prefixWord ++ tailWord_2409941).sum := by decide
  have hdescent : baseEnd_2409941 < baseStart_2409941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409942 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_2409942 : Nat := 118140960795 + 2409942 * 2 ^ 59
def prefixEnd_2409942 : Nat := 4983230072969 + 3 ^ 40 * 2409942 * 2
def baseEnd_2409942 : Nat := 1237458595457715324541885

theorem tailTrace_2409942 : CollatzResearch.WordTrace tailWord_2409942 prefixEnd_2409942 1237458595457715324541885 := by
  unfold tailWord_2409942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5493612864699949635670505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58598537223466129447152053 5493612864699949635670505)
  ·
    refine ⟨4120209648524962226752879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5493612864699949635670505 4120209648524962226752879)
    ·
      refine ⟨6180314472787443340129319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4120209648524962226752879 6180314472787443340129319)
      ·
        refine ⟨9270471709181165010193979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6180314472787443340129319 9270471709181165010193979)
        ·
          refine ⟨13905707563771747515290969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9270471709181165010193979 13905707563771747515290969)
          ·
            refine ⟨10429280672828810636468227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13905707563771747515290969 10429280672828810636468227)
            ·
              refine ⟨15643921009243215954702341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10429280672828810636468227 15643921009243215954702341)
              ·
                refine ⟨2933235189233102991506689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15643921009243215954702341 2933235189233102991506689)
                ·
                  refine ⟨2199926391924827243630017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2933235189233102991506689 2199926391924827243630017)
                  ·
                    refine ⟨1649944793943620432722513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2199926391924827243630017 1649944793943620432722513)
                    ·
                      refine ⟨1237458595457715324541885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649944793943620432722513 1237458595457715324541885)
                      ·
                        rfl

theorem cell23_2409942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_2409942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409942 prefixEnd_2409942 := by exact prefixLift 2409942
  have htrace : WordTrace (prefixWord ++ tailWord_2409942) baseStart_2409942 baseEnd_2409942 := by
    simpa [prefixWord, tailWord_2409942, baseEnd_2409942] using wordTrace_append hprefix tailTrace_2409942
  have hstable : (prefixWord ++ tailWord_2409942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409942).length < 2 ^ (prefixWord ++ tailWord_2409942).sum := by decide
  have hdescent : baseEnd_2409942 < baseStart_2409942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409951 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 1, 7, 2]
def baseStart_2409951 : Nat := 118140960795 + 2409951 * 2 ^ 59
def prefixEnd_2409951 : Nat := 4983230072969 + 3 ^ 40 * 2409951 * 2
def baseEnd_2409951 : Nat := 1237463216783605789329343

theorem tailTrace_2409951 : CollatzResearch.WordTrace tailWord_2409951 prefixEnd_2409951 1237463216783605789329343 := by
  unfold tailWord_2409951
  simp only [CollatzResearch.WordTrace]
  refine ⟨87898134092166588707805707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58598756061444392471870471 87898134092166588707805707)
  ·
    refine ⟨131847201138249883061708561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87898134092166588707805707 131847201138249883061708561)
    ·
      refine ⟨98885400853687412296281421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131847201138249883061708561 98885400853687412296281421)
      ·
        refine ⟨37082025320132779611105533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98885400853687412296281421 37082025320132779611105533)
        ·
          refine ⟨13905759495049792354164575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37082025320132779611105533 13905759495049792354164575)
          ·
            refine ⟨20858639242574688531246863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13905759495049792354164575 20858639242574688531246863)
            ·
              refine ⟨31287958863862032796870295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20858639242574688531246863 31287958863862032796870295)
              ·
                refine ⟨46931938295793049195305443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31287958863862032796870295 46931938295793049195305443)
                ·
                  refine ⟨70397907443689573792958165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46931938295793049195305443 70397907443689573792958165)
                  ·
                    refine ⟨1649950955711474385772457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 70397907443689573792958165 1649950955711474385772457)
                    ·
                      refine ⟨1237463216783605789329343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1649950955711474385772457 1237463216783605789329343)
                      ·
                        rfl

theorem cell23_2409951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_2409951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409951 prefixEnd_2409951 := by exact prefixLift 2409951
  have htrace : WordTrace (prefixWord ++ tailWord_2409951) baseStart_2409951 baseEnd_2409951 := by
    simpa [prefixWord, tailWord_2409951, baseEnd_2409951] using wordTrace_append hprefix tailTrace_2409951
  have hstable : (prefixWord ++ tailWord_2409951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409951).length < 2 ^ (prefixWord ++ tailWord_2409951).sum := by decide
  have hdescent : baseEnd_2409951 < baseStart_2409951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409981 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_2409981 : Nat := 118140960795 + 2409981 * 2 ^ 59
def prefixEnd_2409981 : Nat := 4983230072969 + 3 ^ 40 * 2409981 * 2
def baseEnd_2409981 : Nat := 1237478621203240671954205

theorem tailTrace_2409981 : CollatzResearch.WordTrace tailWord_2409981 prefixEnd_2409981 1237478621203240671954205 := by
  unfold tailWord_2409981
  simp only [CollatzResearch.WordTrace]
  refine ⟨87899228282057903831397797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58599485521371935887598531 87899228282057903831397797)
  ·
    refine ⟨16481105302885856968387087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87899228282057903831397797 16481105302885856968387087)
    ·
      refine ⟨24721657954328785452580631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16481105302885856968387087 24721657954328785452580631)
      ·
        refine ⟨37082486931493178178870947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24721657954328785452580631 37082486931493178178870947)
        ·
          refine ⟨55623730397239767268306421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37082486931493178178870947 55623730397239767268306421)
          ·
            refine ⟨5214724724741228181403727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55623730397239767268306421 5214724724741228181403727)
            ·
              refine ⟨7822087087111842272105591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5214724724741228181403727 7822087087111842272105591)
              ·
                refine ⟨11733130630667763408158387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7822087087111842272105591 11733130630667763408158387)
                ·
                  refine ⟨17599695946001645112237581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11733130630667763408158387 17599695946001645112237581)
                  ·
                    refine ⟨6599885979750616917089093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17599695946001645112237581 6599885979750616917089093)
                    ·
                      refine ⟨1237478621203240671954205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6599885979750616917089093 1237478621203240671954205)
                      ·
                        rfl

theorem cell23_2409981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_2409981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409981 prefixEnd_2409981 := by exact prefixLift 2409981
  have htrace : WordTrace (prefixWord ++ tailWord_2409981) baseStart_2409981 baseEnd_2409981 := by
    simpa [prefixWord, tailWord_2409981, baseEnd_2409981] using wordTrace_append hprefix tailTrace_2409981
  have hstable : (prefixWord ++ tailWord_2409981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409981).length < 2 ^ (prefixWord ++ tailWord_2409981).sum := by decide
  have hdescent : baseEnd_2409981 < baseStart_2409981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2409982 : List Nat := [4, 2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_2409982 : Nat := 118140960795 + 2409982 * 2 ^ 59
def prefixEnd_2409982 : Nat := 4983230072969 + 3 ^ 40 * 2409982 * 2
def baseEnd_2409982 : Nat := 137497681631543907560189

theorem tailTrace_2409982 : CollatzResearch.WordTrace tailWord_2409982 prefixEnd_2409982 137497681631543907560189 := by
  unfold tailWord_2409982
  simp only [CollatzResearch.WordTrace]
  refine ⟨10987408094381785125273025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58599509836702854001456133 10987408094381785125273025)
  ·
    refine ⟨8240556070786338843954769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10987408094381785125273025 8240556070786338843954769)
    ·
      refine ⟨6180417053089754132966077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8240556070786338843954769 6180417053089754132966077)
      ·
        refine ⟨2317656394908657799862279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6180417053089754132966077 2317656394908657799862279)
        ·
          refine ⟨3476484592362986699793419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2317656394908657799862279 3476484592362986699793419)
          ·
            refine ⟨5214726888544480049690129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3476484592362986699793419 5214726888544480049690129)
            ·
              refine ⟨3911045166408360037267597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5214726888544480049690129 3911045166408360037267597)
              ·
                refine ⟨1466641937403135013975349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3911045166408360037267597 1466641937403135013975349)
                ·
                  refine ⟨137497681631543907560189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1466641937403135013975349 137497681631543907560189)
                  ·
                    rfl

theorem cell23_2409982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_2409982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2409982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2409982 prefixEnd_2409982 := by exact prefixLift 2409982
  have htrace : WordTrace (prefixWord ++ tailWord_2409982) baseStart_2409982 baseEnd_2409982 := by
    simpa [prefixWord, tailWord_2409982, baseEnd_2409982] using wordTrace_append hprefix tailTrace_2409982
  have hstable : (prefixWord ++ tailWord_2409982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2409982).length < 2 ^ (prefixWord ++ tailWord_2409982).sum := by decide
  have hdescent : baseEnd_2409982 < baseStart_2409982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2409982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410001 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 3]
def baseStart_2410001 : Nat := 118140960795 + 2410001 * 2 ^ 59
def prefixEnd_2410001 : Nat := 4983230072969 + 3 ^ 40 * 2410001 * 2
def baseEnd_2410001 : Nat := 1237488890816330593704113

theorem tailTrace_2410001 : CollatzResearch.WordTrace tailWord_2410001 prefixEnd_2410001 1237488890816330593704113 := by
  unfold tailWord_2410001
  simp only [CollatzResearch.WordTrace]
  refine ⟨87899957741985447247125857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58599971827990298164750571 87899957741985447247125857)
  ·
    refine ⟨65924968306489085435344393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87899957741985447247125857 65924968306489085435344393)
    ·
      refine ⟨49443726229866814076508295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65924968306489085435344393 49443726229866814076508295)
      ·
        refine ⟨74165589344800221114762443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49443726229866814076508295 74165589344800221114762443)
        ·
          refine ⟨111248384017200331672143665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74165589344800221114762443 111248384017200331672143665)
          ·
            refine ⟨83436288012900248754107749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111248384017200331672143665 83436288012900248754107749)
            ·
              refine ⟨15644304002418796641395203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83436288012900248754107749 15644304002418796641395203)
              ·
                refine ⟨23466456003628194962092805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15644304002418796641395203 23466456003628194962092805)
                ·
                  refine ⟨4399960500680286555392401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23466456003628194962092805 4399960500680286555392401)
                  ·
                    refine ⟨3299970375510214916544301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4399960500680286555392401 3299970375510214916544301)
                    ·
                      refine ⟨1237488890816330593704113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3299970375510214916544301 1237488890816330593704113)
                      ·
                        rfl

theorem cell23_2410001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_2410001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410001 prefixEnd_2410001 := by exact prefixLift 2410001
  have htrace : WordTrace (prefixWord ++ tailWord_2410001) baseStart_2410001 baseEnd_2410001 := by
    simpa [prefixWord, tailWord_2410001, baseEnd_2410001] using wordTrace_append hprefix tailTrace_2410001
  have hstable : (prefixWord ++ tailWord_2410001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410001).length < 2 ^ (prefixWord ++ tailWord_2410001).sum := by decide
  have hdescent : baseEnd_2410001 < baseStart_2410001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410081 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 1, 6]
def baseStart_2410081 : Nat := 118140960795 + 2410081 * 2 ^ 59
def prefixEnd_2410081 : Nat := 4983230072969 + 3 ^ 40 * 2410081 * 2
def baseEnd_2410081 : Nat := 412509989756230093567915

theorem tailTrace_2410081 : CollatzResearch.WordTrace tailWord_2410081 prefixEnd_2410081 412509989756230093567915 := by
  unfold tailWord_2410081
  simp only [CollatzResearch.WordTrace]
  refine ⟨87902875581695620910038097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58601917054463747273358731 87902875581695620910038097)
  ·
    refine ⟨65927156686271715682528573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87902875581695620910038097 65927156686271715682528573)
    ·
      refine ⟨24722683757351893380948215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65927156686271715682528573 24722683757351893380948215)
      ·
        refine ⟨37084025636027840071422323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24722683757351893380948215 37084025636027840071422323)
        ·
          refine ⟨55626038454041760107133485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37084025636027840071422323 55626038454041760107133485)
          ·
            refine ⟨20859764420265660040175057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55626038454041760107133485 20859764420265660040175057)
            ·
              refine ⟨15644823315199245030131293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20859764420265660040175057 15644823315199245030131293)
              ·
                refine ⟨5866808743199716886299235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15644823315199245030131293 5866808743199716886299235)
                ·
                  refine ⟨8800213114799575329448853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5866808743199716886299235 8800213114799575329448853)
                  ·
                    refine ⟨412509989756230093567915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8800213114799575329448853 412509989756230093567915)
                    ·
                      rfl

theorem cell23_2410081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_2410081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410081 prefixEnd_2410081 := by exact prefixLift 2410081
  have htrace : WordTrace (prefixWord ++ tailWord_2410081) baseStart_2410081 baseEnd_2410081 := by
    simpa [prefixWord, tailWord_2410081, baseEnd_2410081] using wordTrace_append hprefix tailTrace_2410081
  have hstable : (prefixWord ++ tailWord_2410081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410081).length < 2 ^ (prefixWord ++ tailWord_2410081).sum := by decide
  have hdescent : baseEnd_2410081 < baseStart_2410081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410085 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 1, 5]
def baseStart_2410085 : Nat := 118140960795 + 2410085 * 2 ^ 59
def prefixEnd_2410085 : Nat := 4983230072969 + 3 ^ 40 * 2410085 * 2
def baseEnd_2410085 : Nat := 412510674397102755017909

theorem tailTrace_2410085 : CollatzResearch.WordTrace tailWord_2410085 prefixEnd_2410085 412510674397102755017909 := by
  unfold tailWord_2410085
  simp only [CollatzResearch.WordTrace]
  refine ⟨87903021473681129593183709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58602014315787419728789139 87903021473681129593183709)
  ·
    refine ⟨32963633052630423597443891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87903021473681129593183709 32963633052630423597443891)
    ·
      refine ⟨49445449578945635396165837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32963633052630423597443891 49445449578945635396165837)
      ·
        refine ⟨18542043592104613273562189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49445449578945635396165837 18542043592104613273562189)
        ·
          refine ⟨6953266347039229977585821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18542043592104613273562189 6953266347039229977585821)
          ·
            refine ⟨2607474880139711241594683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6953266347039229977585821 2607474880139711241594683)
            ·
              refine ⟨3911212320209566862392025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607474880139711241594683 3911212320209566862392025)
              ·
                refine ⟨2933409240157175146794019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3911212320209566862392025 2933409240157175146794019)
                ·
                  refine ⟨4400113860235762720191029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933409240157175146794019 4400113860235762720191029)
                  ·
                    refine ⟨412510674397102755017909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4400113860235762720191029 412510674397102755017909)
                    ·
                      rfl

theorem cell23_2410085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_2410085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410085 prefixEnd_2410085 := by exact prefixLift 2410085
  have htrace : WordTrace (prefixWord ++ tailWord_2410085) baseStart_2410085 baseEnd_2410085 := by
    simpa [prefixWord, tailWord_2410085, baseEnd_2410085] using wordTrace_append hprefix tailTrace_2410085
  have hstable : (prefixWord ++ tailWord_2410085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410085).length < 2 ^ (prefixWord ++ tailWord_2410085).sum := by decide
  have hdescent : baseEnd_2410085 < baseStart_2410085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410098 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_2410098 : Nat := 118140960795 + 2410098 * 2 ^ 59
def prefixEnd_2410098 : Nat := 4983230072969 + 3 ^ 40 * 2410098 * 2
def baseEnd_2410098 : Nat := 412512899479938904730389

theorem tailTrace_2410098 : CollatzResearch.WordTrace tailWord_2410098 prefixEnd_2410098 412512899479938904730389 := by
  unfold tailWord_2410098
  simp only [CollatzResearch.WordTrace]
  refine ⟨21975873905658508203351737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58602330415089355208937965 21975873905658508203351737)
  ·
    refine ⟨16481905429243881152513803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21975873905658508203351737 16481905429243881152513803)
    ·
      refine ⟨24722858143865821728770705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16481905429243881152513803 24722858143865821728770705)
      ·
        refine ⟨18542143607899366296578029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24722858143865821728770705 18542143607899366296578029)
        ·
          refine ⟨6953303852962262361216761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18542143607899366296578029 6953303852962262361216761)
          ·
            refine ⟨5214977889721696770912571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6953303852962262361216761 5214977889721696770912571)
            ·
              refine ⟨7822466834582545156368857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5214977889721696770912571 7822466834582545156368857)
              ·
                refine ⟨5866850125936908867276643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7822466834582545156368857 5866850125936908867276643)
                ·
                  refine ⟨8800275188905363300914965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5866850125936908867276643 8800275188905363300914965)
                  ·
                    refine ⟨412512899479938904730389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8800275188905363300914965 412512899479938904730389)
                    ·
                      rfl

theorem cell23_2410098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_2410098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410098 prefixEnd_2410098 := by exact prefixLift 2410098
  have htrace : WordTrace (prefixWord ++ tailWord_2410098) baseStart_2410098 baseEnd_2410098 := by
    simpa [prefixWord, tailWord_2410098, baseEnd_2410098] using wordTrace_append hprefix tailTrace_2410098
  have hstable : (prefixWord ++ tailWord_2410098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410098).length < 2 ^ (prefixWord ++ tailWord_2410098).sum := by decide
  have hdescent : baseEnd_2410098 < baseStart_2410098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410102 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_2410102 : Nat := 118140960795 + 2410102 * 2 ^ 59
def prefixEnd_2410102 : Nat := 4983230072969 + 3 ^ 40 * 2410102 * 2
def baseEnd_2410102 : Nat := 412513584120811566180383

theorem tailTrace_2410102 : CollatzResearch.WordTrace tailWord_2410102 prefixEnd_2410102 412513584120811566180383 := by
  unfold tailWord_2410102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5493977594663721343534535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58602427676413027664368373 5493977594663721343534535)
  ·
    refine ⟨8240966391995582015301803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5493977594663721343534535 8240966391995582015301803)
    ·
      refine ⟨12361449587993373022952705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8240966391995582015301803 12361449587993373022952705)
      ·
        refine ⟨9271087190995029767214529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12361449587993373022952705 9271087190995029767214529)
        ·
          refine ⟨6953315393246272325410897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9271087190995029767214529 6953315393246272325410897)
          ·
            refine ⟨5214986544934704244058173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6953315393246272325410897 5214986544934704244058173)
            ·
              refine ⟨1955619954350514091521815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5214986544934704244058173 1955619954350514091521815)
              ·
                refine ⟨2933429931525771137282723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955619954350514091521815 2933429931525771137282723)
                ·
                  refine ⟨4400144897288656705924085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933429931525771137282723 4400144897288656705924085)
                  ·
                    refine ⟨412513584120811566180383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4400144897288656705924085 412513584120811566180383)
                    ·
                      rfl

theorem cell23_2410102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_2410102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410102 prefixEnd_2410102 := by exact prefixLift 2410102
  have htrace : WordTrace (prefixWord ++ tailWord_2410102) baseStart_2410102 baseEnd_2410102 := by
    simpa [prefixWord, tailWord_2410102, baseEnd_2410102] using wordTrace_append hprefix tailTrace_2410102
  have hstable : (prefixWord ++ tailWord_2410102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410102).length < 2 ^ (prefixWord ++ tailWord_2410102).sum := by decide
  have hdescent : baseEnd_2410102 < baseStart_2410102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410105 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 1, 1, 4]
def baseStart_2410105 : Nat := 118140960795 + 2410105 * 2 ^ 59
def prefixEnd_2410105 : Nat := 4983230072969 + 3 ^ 40 * 2410105 * 2
def baseEnd_2410105 : Nat := 1237542292804398186803635

theorem tailTrace_2410105 : CollatzResearch.WordTrace tailWord_2410105 prefixEnd_2410105 1237542292804398186803635 := by
  unfold tailWord_2410105
  simp only [CollatzResearch.WordTrace]
  refine ⟨87903750933608673008911769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58602500622405782005941179 87903750933608673008911769)
  ·
    refine ⟨65927813200206504756683827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87903750933608673008911769 65927813200206504756683827)
    ·
      refine ⟨98891719800309757135025741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65927813200206504756683827 98891719800309757135025741)
      ·
        refine ⟨37084394925116158925634653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98891719800309757135025741 37084394925116158925634653)
        ·
          refine ⟨13906648096918559597112995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37084394925116158925634653 13906648096918559597112995)
          ·
            refine ⟨20859972145377839395669493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13906648096918559597112995 20859972145377839395669493)
            ·
              refine ⟨1955622388629172443344015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20859972145377839395669493 1955622388629172443344015)
              ·
                refine ⟨2933433582943758665016023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955622388629172443344015 2933433582943758665016023)
                ·
                  refine ⟨4400150374415637997524035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933433582943758665016023 4400150374415637997524035)
                  ·
                    refine ⟨6600225561623456996286053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4400150374415637997524035 6600225561623456996286053)
                    ·
                      refine ⟨1237542292804398186803635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6600225561623456996286053 1237542292804398186803635)
                      ·
                        rfl

theorem cell23_2410105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_2410105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410105 prefixEnd_2410105 := by exact prefixLift 2410105
  have htrace : WordTrace (prefixWord ++ tailWord_2410105) baseStart_2410105 baseEnd_2410105 := by
    simpa [prefixWord, tailWord_2410105, baseEnd_2410105] using wordTrace_append hprefix tailTrace_2410105
  have hstable : (prefixWord ++ tailWord_2410105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410105).length < 2 ^ (prefixWord ++ tailWord_2410105).sum := by decide
  have hdescent : baseEnd_2410105 < baseStart_2410105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410116 : List Nat := [2, 3, 2, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_2410116 : Nat := 118140960795 + 2410116 * 2 ^ 59
def prefixEnd_2410116 : Nat := 4983230072969 + 3 ^ 40 * 2410116 * 2
def baseEnd_2410116 : Nat := 1237547941091597643766085

theorem tailTrace_2410116 : CollatzResearch.WordTrace tailWord_2410116 prefixEnd_2410116 1237547941091597643766085 := by
  unfold tailWord_2410116
  simp only [CollatzResearch.WordTrace]
  refine ⟨43952076068284410943781101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58602768091045881258374801 43952076068284410943781101)
  ·
    refine ⟨16482028525606654103917913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43952076068284410943781101 16482028525606654103917913)
    ·
      refine ⟨12361521394204990577938435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16482028525606654103917913 12361521394204990577938435)
      ·
        refine ⟨18542282091307485866907653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12361521394204990577938435 18542282091307485866907653)
        ·
          refine ⟨3476677892120153600045185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18542282091307485866907653 3476677892120153600045185)
          ·
            refine ⟨2607508419090115200033889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3476677892120153600045185 2607508419090115200033889)
            ·
              refine ⟨1955631314317586400025417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2607508419090115200033889 1955631314317586400025417)
              ·
                refine ⟨1466723485738189800019063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1955631314317586400025417 1466723485738189800019063)
                ·
                  refine ⟨2200085228607284700028595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466723485738189800019063 2200085228607284700028595)
                  ·
                    refine ⟨3300127842910927050042893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2200085228607284700028595 3300127842910927050042893)
                    ·
                      refine ⟨1237547941091597643766085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3300127842910927050042893 1237547941091597643766085)
                      ·
                        rfl

theorem cell23_2410116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_2410116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410116 prefixEnd_2410116 := by exact prefixLift 2410116
  have htrace : WordTrace (prefixWord ++ tailWord_2410116) baseStart_2410116 baseEnd_2410116 := by
    simpa [prefixWord, tailWord_2410116, baseEnd_2410116] using wordTrace_append hprefix tailTrace_2410116
  have hstable : (prefixWord ++ tailWord_2410116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410116).length < 2 ^ (prefixWord ++ tailWord_2410116).sum := by decide
  have hdescent : baseEnd_2410116 < baseStart_2410116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410141 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_2410141 : Nat := 118140960795 + 2410141 * 2 ^ 59
def prefixEnd_2410141 : Nat := 4983230072969 + 3 ^ 40 * 2410141 * 2
def baseEnd_2410141 : Nat := 412520259369320015317823

theorem tailTrace_2410141 : CollatzResearch.WordTrace tailWord_2410141 prefixEnd_2410141 412520259369320015317823 := by
  unfold tailWord_2410141
  simp only [CollatzResearch.WordTrace]
  refine ⟨87905063961478251157222277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58603375974318834104814851 87905063961478251157222277)
  ·
    refine ⟨16482199492777172091979177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87905063961478251157222277 16482199492777172091979177)
    ·
      refine ⟨12361649619582879068984383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16482199492777172091979177 12361649619582879068984383)
      ·
        refine ⟨18542474429374318603476575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12361649619582879068984383 18542474429374318603476575)
        ·
          refine ⟨27813711644061477905214863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18542474429374318603476575 27813711644061477905214863)
          ·
            refine ⟨41720567466092216857822295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27813711644061477905214863 41720567466092216857822295)
            ·
              refine ⟨62580851199138325286733443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41720567466092216857822295 62580851199138325286733443)
              ·
                refine ⟨93871276798707487930100165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62580851199138325286733443 93871276798707487930100165)
                ·
                  refine ⟨17600864399757653986893781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93871276798707487930100165 17600864399757653986893781)
                  ·
                    refine ⟨412520259369320015317823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17600864399757653986893781 412520259369320015317823)
                    ·
                      rfl

theorem cell23_2410141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_2410141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410141 prefixEnd_2410141 := by exact prefixLift 2410141
  have htrace : WordTrace (prefixWord ++ tailWord_2410141) baseStart_2410141 baseEnd_2410141 := by
    simpa [prefixWord, tailWord_2410141, baseEnd_2410141] using wordTrace_append hprefix tailTrace_2410141
  have hstable : (prefixWord ++ tailWord_2410141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410141).length < 2 ^ (prefixWord ++ tailWord_2410141).sum := by decide
  have hdescent : baseEnd_2410141 < baseStart_2410141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410172 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_2410172 : Nat := 118140960795 + 2410172 * 2 ^ 59
def prefixEnd_2410172 : Nat := 4983230072969 + 3 ^ 40 * 2410172 * 2
def baseEnd_2410172 : Nat := 1237576696008249424665827

theorem tailTrace_2410172 : CollatzResearch.WordTrace tailWord_2410172 prefixEnd_2410172 1237576696008249424665827 := by
  unfold tailWord_2410172
  simp only [CollatzResearch.WordTrace]
  refine ⟨43953097312182971725800385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58604129749577295634400513 43953097312182971725800385)
  ·
    refine ⟨32964822984137228794350289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43953097312182971725800385 32964822984137228794350289)
    ·
      refine ⟨24723617238102921595762717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32964822984137228794350289 24723617238102921595762717)
      ·
        refine ⟨9271356464288595598411019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24723617238102921595762717 9271356464288595598411019)
        ·
          refine ⟨13907034696432893397616529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9271356464288595598411019 13907034696432893397616529)
          ·
            refine ⟨10430276022324670048212397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13907034696432893397616529 10430276022324670048212397)
            ·
              refine ⟨3911353508371751268079649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10430276022324670048212397 3911353508371751268079649)
              ·
                refine ⟨2933515131278813451059737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3911353508371751268079649 2933515131278813451059737)
                ·
                  refine ⟨2200136348459110088294803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2933515131278813451059737 2200136348459110088294803)
                  ·
                    refine ⟨3300204522688665132442205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2200136348459110088294803 3300204522688665132442205)
                    ·
                      refine ⟨1237576696008249424665827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3300204522688665132442205 1237576696008249424665827)
                      ·
                        rfl

theorem cell23_2410172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_2410172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410172 prefixEnd_2410172 := by exact prefixLift 2410172
  have htrace : WordTrace (prefixWord ++ tailWord_2410172) baseStart_2410172 baseEnd_2410172 := by
    simpa [prefixWord, tailWord_2410172, baseEnd_2410172] using wordTrace_append hprefix tailTrace_2410172
  have hstable : (prefixWord ++ tailWord_2410172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410172).length < 2 ^ (prefixWord ++ tailWord_2410172).sum := by decide
  have hdescent : baseEnd_2410172 < baseStart_2410172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410181 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_2410181 : Nat := 118140960795 + 2410181 * 2 ^ 59
def prefixEnd_2410181 : Nat := 4983230072969 + 3 ^ 40 * 2410181 * 2
def baseEnd_2410181 : Nat := 1237581317334139889453285

theorem tailTrace_2410181 : CollatzResearch.WordTrace tailWord_2410181 prefixEnd_2410181 1237581317334139889453285 := by
  unfold tailWord_2410181
  simp only [CollatzResearch.WordTrace]
  refine ⟨87906522881333337988678397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58604348587555558659118931 87906522881333337988678397)
  ·
    refine ⟨32964946080500001745754399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87906522881333337988678397 32964946080500001745754399)
    ·
      refine ⟨49447419120750002618631599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32964946080500001745754399 49447419120750002618631599)
      ·
        refine ⟨74171128681125003927947399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49447419120750002618631599 74171128681125003927947399)
        ·
          refine ⟨111256693021687505891921099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74171128681125003927947399 111256693021687505891921099)
          ·
            refine ⟨166885039532531258837881649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111256693021687505891921099 166885039532531258837881649)
            ·
              refine ⟨125163779649398444128411237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166885039532531258837881649 125163779649398444128411237)
              ·
                refine ⟨23468208684262208274077107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125163779649398444128411237 23468208684262208274077107)
                ·
                  refine ⟨35202313026393312411115661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23468208684262208274077107 35202313026393312411115661)
                  ·
                    refine ⟨13200867384897492154168373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35202313026393312411115661 13200867384897492154168373)
                    ·
                      refine ⟨1237581317334139889453285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13200867384897492154168373 1237581317334139889453285)
                      ·
                        rfl

theorem cell23_2410181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_2410181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410181 prefixEnd_2410181 := by exact prefixLift 2410181
  have htrace : WordTrace (prefixWord ++ tailWord_2410181) baseStart_2410181 baseEnd_2410181 := by
    simpa [prefixWord, tailWord_2410181, baseEnd_2410181] using wordTrace_append hprefix tailTrace_2410181
  have hstable : (prefixWord ++ tailWord_2410181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410181).length < 2 ^ (prefixWord ++ tailWord_2410181).sum := by decide
  have hdescent : baseEnd_2410181 < baseStart_2410181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410189 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_2410189 : Nat := 118140960795 + 2410189 * 2 ^ 59
def prefixEnd_2410189 : Nat := 4983230072969 + 3 ^ 40 * 2410189 * 2
def baseEnd_2410189 : Nat := 1237585425179375858153249

theorem tailTrace_2410189 : CollatzResearch.WordTrace tailWord_2410189 prefixEnd_2410189 1237585425179375858153249 := by
  unfold tailWord_2410189
  simp only [CollatzResearch.WordTrace]
  refine ⟨87906814665304355354969621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58604543110202903569979747 87906814665304355354969621)
  ·
    refine ⟨4120631937436141657264201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 87906814665304355354969621 4120631937436141657264201)
    ·
      refine ⟨3090473953077106242948151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4120631937436141657264201 3090473953077106242948151)
      ·
        refine ⟨4635710929615659364422227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3090473953077106242948151 4635710929615659364422227)
        ·
          refine ⟨6953566394423489046633341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4635710929615659364422227 6953566394423489046633341)
          ·
            refine ⟨2607587397908808392487503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6953566394423489046633341 2607587397908808392487503)
            ·
              refine ⟨3911381096863212588731255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607587397908808392487503 3911381096863212588731255)
              ·
                refine ⟨5867071645294818883096883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3911381096863212588731255 5867071645294818883096883)
                ·
                  refine ⟨8800607467942228324645325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5867071645294818883096883 8800607467942228324645325)
                  ·
                    refine ⟨3300227800478335621741997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8800607467942228324645325 3300227800478335621741997)
                    ·
                      refine ⟨1237585425179375858153249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3300227800478335621741997 1237585425179375858153249)
                      ·
                        rfl

theorem cell23_2410189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_2410189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410189 prefixEnd_2410189 := by exact prefixLift 2410189
  have htrace : WordTrace (prefixWord ++ tailWord_2410189) baseStart_2410189 baseEnd_2410189 := by
    simpa [prefixWord, tailWord_2410189, baseEnd_2410189] using wordTrace_append hprefix tailTrace_2410189
  have hstable : (prefixWord ++ tailWord_2410189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410189).length < 2 ^ (prefixWord ++ tailWord_2410189).sum := by decide
  have hdescent : baseEnd_2410189 < baseStart_2410189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410248 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 4, 5]
def baseStart_2410248 : Nat := 118140960795 + 2410248 * 2 ^ 59
def prefixEnd_2410248 : Nat := 4983230072969 + 3 ^ 40 * 2410248 * 2
def baseEnd_2410248 : Nat := 412538573512663709105159

theorem tailTrace_2410248 : CollatzResearch.WordTrace tailWord_2410248 prefixEnd_2410248 412538573512663709105159 := by
  unfold tailWord_2410248
  simp only [CollatzResearch.WordTrace]
  refine ⟨43954483286045304215683699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58605977714727072287578265 43954483286045304215683699)
  ·
    refine ⟨65931724929067956323525549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43954483286045304215683699 65931724929067956323525549)
    ·
      refine ⟨24724396848400483621322081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65931724929067956323525549 24724396848400483621322081)
      ·
        refine ⟨18543297636300362715991561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24724396848400483621322081 18543297636300362715991561)
        ·
          refine ⟨13907473227225272036993671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18543297636300362715991561 13907473227225272036993671)
          ·
            refine ⟨20861209840837908055490507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13907473227225272036993671 20861209840837908055490507)
            ·
              refine ⟨31291814761256862083235761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20861209840837908055490507 31291814761256862083235761)
              ·
                refine ⟨23468861070942646562426821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31291814761256862083235761 23468861070942646562426821)
                ·
                  refine ⟨4400411450801746230455029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23468861070942646562426821 4400411450801746230455029)
                  ·
                    refine ⟨412538573512663709105159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4400411450801746230455029 412538573512663709105159)
                    ·
                      rfl

theorem cell23_2410248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_2410248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410248 prefixEnd_2410248 := by exact prefixLift 2410248
  have htrace : WordTrace (prefixWord ++ tailWord_2410248) baseStart_2410248 baseEnd_2410248 := by
    simpa [prefixWord, tailWord_2410248, baseEnd_2410248] using wordTrace_append hprefix tailTrace_2410248
  have hstable : (prefixWord ++ tailWord_2410248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410248).length < 2 ^ (prefixWord ++ tailWord_2410248).sum := by decide
  have hdescent : baseEnd_2410248 < baseStart_2410248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410286 : List Nat := [4, 1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_2410286 : Nat := 118140960795 + 2410286 * 2 ^ 59
def prefixEnd_2410286 : Nat := 4983230072969 + 3 ^ 40 * 2410286 * 2
def baseEnd_2410286 : Nat := 137515025866984664293367

theorem tailTrace_2410286 : CollatzResearch.WordTrace tailWord_2410286 prefixEnd_2410286 137515025866984664293367 := by
  unfold tailWord_2410286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10988794068244117615156339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58606901697301960614167141 10988794068244117615156339)
  ·
    refine ⟨16483191102366176422734509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10988794068244117615156339 16483191102366176422734509)
    ·
      refine ⟨6181196663387316158525441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16483191102366176422734509 6181196663387316158525441)
      ·
        refine ⟨4635897497540487118894081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6181196663387316158525441 4635897497540487118894081)
        ·
          refine ⟨3476923123155365339170561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4635897497540487118894081 3476923123155365339170561)
          ·
            refine ⟨2607692342366524004377921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3476923123155365339170561 2607692342366524004377921)
            ·
              refine ⟨1955769256774893003283441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2607692342366524004377921 1955769256774893003283441)
              ·
                refine ⟨1466826942581169752462581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1955769256774893003283441 1466826942581169752462581)
                ·
                  refine ⟨137515025866984664293367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1466826942581169752462581 137515025866984664293367)
                  ·
                    rfl

theorem cell23_2410286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_2410286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410286 prefixEnd_2410286 := by exact prefixLift 2410286
  have htrace : WordTrace (prefixWord ++ tailWord_2410286) baseStart_2410286 baseEnd_2410286 := by
    simpa [prefixWord, tailWord_2410286, baseEnd_2410286] using wordTrace_append hprefix tailTrace_2410286
  have hstable : (prefixWord ++ tailWord_2410286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410286).length < 2 ^ (prefixWord ++ tailWord_2410286).sum := by decide
  have hdescent : baseEnd_2410286 < baseStart_2410286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410288 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 3]
def baseStart_2410288 : Nat := 118140960795 + 2410288 * 2 ^ 59
def prefixEnd_2410288 : Nat := 4983230072969 + 3 ^ 40 * 2410288 * 2
def baseEnd_2410288 : Nat := 1237636259764170970815293

theorem tailTrace_2410288 : CollatzResearch.WordTrace tailWord_2410288 prefixEnd_2410288 1237636259764170970815293 := by
  unfold tailWord_2410288
  simp only [CollatzResearch.WordTrace]
  refine ⟨43955212745972847631411759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58606950327963796841882345 43955212745972847631411759)
  ·
    refine ⟨65932819118959271447117639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43955212745972847631411759 65932819118959271447117639)
    ·
      refine ⟨98899228678438907170676459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65932819118959271447117639 98899228678438907170676459)
      ·
        refine ⟨148348843017658360756014689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98899228678438907170676459 148348843017658360756014689)
        ·
          refine ⟨111261632263243770567011017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148348843017658360756014689 111261632263243770567011017)
          ·
            refine ⟨83446224197432827925258263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111261632263243770567011017 83446224197432827925258263)
            ·
              refine ⟨125169336296149241887887395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83446224197432827925258263 125169336296149241887887395)
              ·
                refine ⟨187754004444223862831831093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125169336296149241887887395 187754004444223862831831093)
                ·
                  refine ⟨17601937916645987140484165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187754004444223862831831093 17601937916645987140484165)
                  ·
                    refine ⟨3300363359371122588840781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17601937916645987140484165 3300363359371122588840781)
                    ·
                      refine ⟨1237636259764170970815293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3300363359371122588840781 1237636259764170970815293)
                      ·
                        rfl

theorem cell23_2410288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 3].length) (baseStart_2410288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410288 prefixEnd_2410288 := by exact prefixLift 2410288
  have htrace : WordTrace (prefixWord ++ tailWord_2410288) baseStart_2410288 baseEnd_2410288 := by
    simpa [prefixWord, tailWord_2410288, baseEnd_2410288] using wordTrace_append hprefix tailTrace_2410288
  have hstable : (prefixWord ++ tailWord_2410288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410288).length < 2 ^ (prefixWord ++ tailWord_2410288).sum := by decide
  have hdescent : baseEnd_2410288 < baseStart_2410288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410302 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_2410302 : Nat := 118140960795 + 2410302 * 2 ^ 59
def prefixEnd_2410302 : Nat := 4983230072969 + 3 ^ 40 * 2410302 * 2
def baseEnd_2410302 : Nat := 1237643448493333916040229

theorem tailTrace_2410302 : CollatzResearch.WordTrace tailWord_2410302 prefixEnd_2410302 1237643448493333916040229 := by
  unfold tailWord_2410302
  simp only [CollatzResearch.WordTrace]
  refine ⟨10988867014236871956729145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58607290742596650435888773 10988867014236871956729145)
  ·
    refine ⟨8241650260677653967546859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10988867014236871956729145 8241650260677653967546859)
    ·
      refine ⟨12362475391016480951320289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8241650260677653967546859 12362475391016480951320289)
      ·
        refine ⟨9271856543262360713490217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12362475391016480951320289 9271856543262360713490217)
        ·
          refine ⟨6953892407446770535117663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9271856543262360713490217 6953892407446770535117663)
          ·
            refine ⟨10430838611170155802676495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6953892407446770535117663 10430838611170155802676495)
            ·
              refine ⟨15646257916755233704014743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10430838611170155802676495 15646257916755233704014743)
              ·
                refine ⟨23469386875132850556022115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15646257916755233704014743 23469386875132850556022115)
                ·
                  refine ⟨35204080312699275834033173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23469386875132850556022115 35204080312699275834033173)
                  ·
                    refine ⟨1650191264657778554720305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35204080312699275834033173 1650191264657778554720305)
                    ·
                      refine ⟨1237643448493333916040229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1650191264657778554720305 1237643448493333916040229)
                      ·
                        rfl

theorem cell23_2410302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_2410302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410302 prefixEnd_2410302 := by exact prefixLift 2410302
  have htrace : WordTrace (prefixWord ++ tailWord_2410302) baseStart_2410302 baseEnd_2410302 := by
    simpa [prefixWord, tailWord_2410302, baseEnd_2410302] using wordTrace_append hprefix tailTrace_2410302
  have hstable : (prefixWord ++ tailWord_2410302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410302).length < 2 ^ (prefixWord ++ tailWord_2410302).sum := by decide
  have hdescent : baseEnd_2410302 < baseStart_2410302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410322 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_2410322 : Nat := 118140960795 + 2410322 * 2 ^ 59
def prefixEnd_2410322 : Nat := 4983230072969 + 3 ^ 40 * 2410322 * 2
def baseEnd_2410322 : Nat := 1237653718106423837790137

theorem tailTrace_2410322 : CollatzResearch.WordTrace tailWord_2410322 prefixEnd_2410322 1237653718106423837790137 := by
  unfold tailWord_2410322
  simp only [CollatzResearch.WordTrace]
  refine ⟨21977916393455629767390305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58607777049215012713040813 21977916393455629767390305)
  ·
    refine ⟨16483437295091722325542729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21977916393455629767390305 16483437295091722325542729)
    ·
      refine ⟨12362577971318791744157047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16483437295091722325542729 12362577971318791744157047)
      ·
        refine ⟨18543866956978187616235571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12362577971318791744157047 18543866956978187616235571)
        ·
          refine ⟨27815800435467281424353357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18543866956978187616235571 27815800435467281424353357)
          ·
            refine ⟨10430925163300230534132509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27815800435467281424353357 10430925163300230534132509)
            ·
              refine ⟨3911596936237586450299691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10430925163300230534132509 3911596936237586450299691)
              ·
                refine ⟨5867395404356379675449537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3911596936237586450299691 5867395404356379675449537)
                ·
                  refine ⟨4400546553267284756587153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5867395404356379675449537 4400546553267284756587153)
                  ·
                    refine ⟨3300409914950463567440365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4400546553267284756587153 3300409914950463567440365)
                    ·
                      refine ⟨1237653718106423837790137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3300409914950463567440365 1237653718106423837790137)
                      ·
                        rfl

theorem cell23_2410322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_2410322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410322 prefixEnd_2410322 := by exact prefixLift 2410322
  have htrace : WordTrace (prefixWord ++ tailWord_2410322) baseStart_2410322 baseEnd_2410322 := by
    simpa [prefixWord, tailWord_2410322, baseEnd_2410322] using wordTrace_append hprefix tailTrace_2410322
  have hstable : (prefixWord ++ tailWord_2410322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410322).length < 2 ^ (prefixWord ++ tailWord_2410322).sum := by decide
  have hdescent : baseEnd_2410322 < baseStart_2410322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410385 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 4, 4]
def baseStart_2410385 : Nat := 118140960795 + 2410385 * 2 ^ 59
def prefixEnd_2410385 : Nat := 4983230072969 + 3 ^ 40 * 2410385 * 2
def baseEnd_2410385 : Nat := 412562022462552363767449

theorem tailTrace_2410385 : CollatzResearch.WordTrace tailWord_2410385 prefixEnd_2410385 412562022462552363767449 := by
  unfold tailWord_2410385
  simp only [CollatzResearch.WordTrace]
  refine ⟨87913963372594280829104609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58609308915062853886069739 87913963372594280829104609)
  ·
    refine ⟨65935472529445710621828457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87913963372594280829104609 65935472529445710621828457)
    ·
      refine ⟨49451604397084282966371343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65935472529445710621828457 49451604397084282966371343)
      ·
        refine ⟨74177406595626424449557015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49451604397084282966371343 74177406595626424449557015)
        ·
          refine ⟨111266109893439636674335523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74177406595626424449557015 111266109893439636674335523)
          ·
            refine ⟨166899164840159455011503285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111266109893439636674335523 166899164840159455011503285)
            ·
              refine ⟨15646796703764948907328433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166899164840159455011503285 15646796703764948907328433)
              ·
                refine ⟨11735097527823711680496325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15646796703764948907328433 11735097527823711680496325)
                ·
                  refine ⟨2200330786466945940093061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11735097527823711680496325 2200330786466945940093061)
                  ·
                    refine ⟨412562022462552363767449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2200330786466945940093061 412562022462552363767449)
                    ·
                      rfl

theorem cell23_2410385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_2410385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410385 prefixEnd_2410385 := by exact prefixLift 2410385
  have htrace : WordTrace (prefixWord ++ tailWord_2410385) baseStart_2410385 baseEnd_2410385 := by
    simpa [prefixWord, tailWord_2410385, baseEnd_2410385] using wordTrace_append hprefix tailTrace_2410385
  have hstable : (prefixWord ++ tailWord_2410385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410385).length < 2 ^ (prefixWord ++ tailWord_2410385).sum := by decide
  have hdescent : baseEnd_2410385 < baseStart_2410385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410429 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_2410429 : Nat := 118140960795 + 2410429 * 2 ^ 59
def prefixEnd_2410429 : Nat := 4983230072969 + 3 ^ 40 * 2410429 * 2
def baseEnd_2410429 : Nat := 1237708660536454919152145

theorem tailTrace_2410429 : CollatzResearch.WordTrace tailWord_2410429 prefixEnd_2410429 1237708660536454919152145 := by
  unfold tailWord_2410429
  simp only [CollatzResearch.WordTrace]
  refine ⟨87915568184434876343706341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58610378789623250895804227 87915568184434876343706341)
  ·
    refine ⟨16484169034581539314444939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87915568184434876343706341 16484169034581539314444939)
    ·
      refine ⟨24726253551872308971667409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16484169034581539314444939 24726253551872308971667409)
      ·
        refine ⟨18544690163904231728750557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24726253551872308971667409 18544690163904231728750557)
        ·
          refine ⟨6954258811464086898281459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18544690163904231728750557 6954258811464086898281459)
          ·
            refine ⟨10431388217196130347422189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6954258811464086898281459 10431388217196130347422189)
            ·
              refine ⟨3911770581448548880283321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10431388217196130347422189 3911770581448548880283321)
              ·
                refine ⟨2933827936086411660212491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3911770581448548880283321 2933827936086411660212491)
                ·
                  refine ⟨4400741904129617490318737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933827936086411660212491 4400741904129617490318737)
                  ·
                    refine ⟨3300556428097213117739053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4400741904129617490318737 3300556428097213117739053)
                    ·
                      refine ⟨1237708660536454919152145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3300556428097213117739053 1237708660536454919152145)
                      ·
                        rfl

theorem cell23_2410429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_2410429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410429 prefixEnd_2410429 := by exact prefixLift 2410429
  have htrace : WordTrace (prefixWord ++ tailWord_2410429) baseStart_2410429 baseEnd_2410429 := by
    simpa [prefixWord, tailWord_2410429, baseEnd_2410429] using wordTrace_append hprefix tailTrace_2410429
  have hstable : (prefixWord ++ tailWord_2410429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410429).length < 2 ^ (prefixWord ++ tailWord_2410429).sum := by decide
  have hdescent : baseEnd_2410429 < baseStart_2410429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410442 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_2410442 : Nat := 118140960795 + 2410442 * 2 ^ 59
def prefixEnd_2410442 : Nat := 4983230072969 + 3 ^ 40 * 2410442 * 2
def baseEnd_2410442 : Nat := 1237715335784963368289585

theorem tailTrace_2410442 : CollatzResearch.WordTrace tailWord_2410442 prefixEnd_2410442 1237715335784963368289585 := by
  unfold tailWord_2410442
  simp only [CollatzResearch.WordTrace]
  refine ⟨21979010583346944890982395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58610694888925186375953053 21979010583346944890982395)
  ·
    refine ⟨32968515875020417336473593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21979010583346944890982395 32968515875020417336473593)
    ·
      refine ⟨24726386906265313002355195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32968515875020417336473593 24726386906265313002355195)
      ·
        refine ⟨37089580359397969503532793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24726386906265313002355195 37089580359397969503532793)
        ·
          refine ⟨27817185269548477127649595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37089580359397969503532793 27817185269548477127649595)
          ·
            refine ⟨41725777904322715691474393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27817185269548477127649595 41725777904322715691474393)
            ·
              refine ⟨31294333428242036768605795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41725777904322715691474393 31294333428242036768605795)
              ·
                refine ⟨46941500142363055152908693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31294333428242036768605795 46941500142363055152908693)
                ·
                  refine ⟨2200382819173268210292595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46941500142363055152908693 2200382819173268210292595)
                  ·
                    refine ⟨3300574228759902315438893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2200382819173268210292595 3300574228759902315438893)
                    ·
                      refine ⟨1237715335784963368289585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3300574228759902315438893 1237715335784963368289585)
                      ·
                        rfl

theorem cell23_2410442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_2410442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410442 prefixEnd_2410442 := by exact prefixLift 2410442
  have htrace : WordTrace (prefixWord ++ tailWord_2410442) baseStart_2410442 baseEnd_2410442 := by
    simpa [prefixWord, tailWord_2410442, baseEnd_2410442] using wordTrace_append hprefix tailTrace_2410442
  have hstable : (prefixWord ++ tailWord_2410442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410442).length < 2 ^ (prefixWord ++ tailWord_2410442).sum := by decide
  have hdescent : baseEnd_2410442 < baseStart_2410442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410465 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_2410465 : Nat := 118140960795 + 2410465 * 2 ^ 59
def prefixEnd_2410465 : Nat := 4983230072969 + 3 ^ 40 * 2410465 * 2
def baseEnd_2410465 : Nat := 1237727145840016778301979

theorem tailTrace_2410465 : CollatzResearch.WordTrace tailWord_2410465 prefixEnd_2410465 1237727145840016778301979 := by
  unfold tailWord_2410465
  simp only [CollatzResearch.WordTrace]
  refine ⟨87916881212304454492016849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58611254141536302994677899 87916881212304454492016849)
  ·
    refine ⟨65937660909228340869012637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87916881212304454492016849 65937660909228340869012637)
    ·
      refine ⟨24726622840960627825879739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65937660909228340869012637 24726622840960627825879739)
      ·
        refine ⟨37089934261440941738819609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24726622840960627825879739 37089934261440941738819609)
        ·
          refine ⟨27817450696080706304114707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37089934261440941738819609 27817450696080706304114707)
          ·
            refine ⟨41726176044121059456172061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27817450696080706304114707 41726176044121059456172061)
            ·
              refine ⟨15647316016545397296064523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41726176044121059456172061 15647316016545397296064523)
              ·
                refine ⟨23470974024818095944096785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15647316016545397296064523 23470974024818095944096785)
                ·
                  refine ⟨17603230518613571958072589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23470974024818095944096785 17603230518613571958072589)
                  ·
                    refine ⟨6601211444480089484277221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17603230518613571958072589 6601211444480089484277221)
                    ·
                      refine ⟨1237727145840016778301979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6601211444480089484277221 1237727145840016778301979)
                      ·
                        rfl

theorem cell23_2410465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_2410465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410465 prefixEnd_2410465 := by exact prefixLift 2410465
  have htrace : WordTrace (prefixWord ++ tailWord_2410465) baseStart_2410465 baseEnd_2410465 := by
    simpa [prefixWord, tailWord_2410465, baseEnd_2410465] using wordTrace_append hprefix tailTrace_2410465
  have hstable : (prefixWord ++ tailWord_2410465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410465).length < 2 ^ (prefixWord ++ tailWord_2410465).sum := by decide
  have hdescent : baseEnd_2410465 < baseStart_2410465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410466 : List Nat := [3, 3, 3, 1, 3, 1, 1, 8]
def baseStart_2410466 : Nat := 118140960795 + 2410466 * 2 ^ 59
def prefixEnd_2410466 : Nat := 4983230072969 + 3 ^ 40 * 2410466 * 2
def baseEnd_2410466 : Nat := 45841765160024862014425

theorem tailTrace_2410466 : CollatzResearch.WordTrace tailWord_2410466 prefixEnd_2410466 45841765160024862014425 := by
  unfold tailWord_2410466
  simp only [CollatzResearch.WordTrace]
  refine ⟨21979229421325207915700813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58611278456867221108535501 21979229421325207915700813)
  ·
    refine ⟨8242211032996952968387805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21979229421325207915700813 8242211032996952968387805)
    ·
      refine ⟨3090829137373857363145427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8242211032996952968387805 3090829137373857363145427)
      ·
        refine ⟨4636243706060786044718141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3090829137373857363145427 4636243706060786044718141)
        ·
          refine ⟨1738591389772794766769303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4636243706060786044718141 1738591389772794766769303)
          ·
            refine ⟨2607887084659192150153955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738591389772794766769303 2607887084659192150153955)
            ·
              refine ⟨3911830626988788225230933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607887084659192150153955 3911830626988788225230933)
              ·
                refine ⟨45841765160024862014425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3911830626988788225230933 45841765160024862014425)
                ·
                  rfl

theorem cell23_2410466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 8].length) (baseStart_2410466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410466 prefixEnd_2410466 := by exact prefixLift 2410466
  have htrace : WordTrace (prefixWord ++ tailWord_2410466) baseStart_2410466 baseEnd_2410466 := by
    simpa [prefixWord, tailWord_2410466, baseEnd_2410466] using wordTrace_append hprefix tailTrace_2410466
  have hstable : (prefixWord ++ tailWord_2410466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410466).length < 2 ^ (prefixWord ++ tailWord_2410466).sum := by decide
  have hdescent : baseEnd_2410466 < baseStart_2410466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410503 : List Nat := [1, 1, 4, 3, 1, 4, 2, 1, 1, 3, 2]
def baseStart_2410503 : Nat := 118140960795 + 2410503 * 2 ^ 59
def prefixEnd_2410503 : Nat := 4983230072969 + 3 ^ 40 * 2410503 * 2
def baseEnd_2410503 : Nat := 1237746658104887629626805

theorem tailTrace_2410503 : CollatzResearch.WordTrace tailWord_2410503 prefixEnd_2410503 1237746658104887629626805 := by
  unfold tailWord_2410503
  simp only [CollatzResearch.WordTrace]
  refine ⟨87918267186166786981900163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58612178124111191321266775 87918267186166786981900163)
  ·
    refine ⟨131877400779250180472850245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87918267186166786981900163 131877400779250180472850245)
    ·
      refine ⟨24727012646109408838659421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131877400779250180472850245 24727012646109408838659421)
      ·
        refine ⟨9272629742291028314497283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24727012646109408838659421 9272629742291028314497283)
        ·
          refine ⟨13908944613436542471745925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9272629742291028314497283 13908944613436542471745925)
          ·
            refine ⟨2607927115019351713452361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13908944613436542471745925 2607927115019351713452361)
            ·
              refine ⟨1955945336264513785089271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2607927115019351713452361 1955945336264513785089271)
              ·
                refine ⟨2933918004396770677633907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955945336264513785089271 2933918004396770677633907)
                ·
                  refine ⟨4400877006595156016450861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933918004396770677633907 4400877006595156016450861)
                  ·
                    refine ⟨1650328877473183506169073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4400877006595156016450861 1650328877473183506169073)
                    ·
                      refine ⟨1237746658104887629626805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1650328877473183506169073 1237746658104887629626805)
                      ·
                        rfl

theorem cell23_2410503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_2410503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410503 prefixEnd_2410503 := by exact prefixLift 2410503
  have htrace : WordTrace (prefixWord ++ tailWord_2410503) baseStart_2410503 baseEnd_2410503 := by
    simpa [prefixWord, tailWord_2410503, baseEnd_2410503] using wordTrace_append hprefix tailTrace_2410503
  have hstable : (prefixWord ++ tailWord_2410503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410503).length < 2 ^ (prefixWord ++ tailWord_2410503).sum := by decide
  have hdescent : baseEnd_2410503 < baseStart_2410503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410522 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 7]
def baseStart_2410522 : Nat := 118140960795 + 2410522 * 2 ^ 59
def prefixEnd_2410522 : Nat := 4983230072969 + 3 ^ 40 * 2410522 * 2
def baseEnd_2410522 : Nat := 137528490470813672809913

theorem tailTrace_2410522 : CollatzResearch.WordTrace tailWord_2410522 prefixEnd_2410522 137528490470813672809913 := by
  unfold tailWord_2410522
  simp only [CollatzResearch.WordTrace]
  refine ⟨21979740043274488306710455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58612640115398635484561213 21979740043274488306710455)
  ·
    refine ⟨32969610064911732460065683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21979740043274488306710455 32969610064911732460065683)
    ·
      refine ⟨49454415097367598690098525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32969610064911732460065683 49454415097367598690098525)
      ·
        refine ⟨18545405661512849508786947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49454415097367598690098525 18545405661512849508786947)
        ·
          refine ⟨27818108492269274263180421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18545405661512849508786947 27818108492269274263180421)
          ·
            refine ⟨5215895342300488924346329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27818108492269274263180421 5215895342300488924346329)
            ·
              refine ⟨3911921506725366693259747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5215895342300488924346329 3911921506725366693259747)
              ·
                refine ⟨5867882260088050039889621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3911921506725366693259747 5867882260088050039889621)
                ·
                  refine ⟨137528490470813672809913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5867882260088050039889621 137528490470813672809913)
                  ·
                    rfl

theorem cell23_2410522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_2410522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410522 prefixEnd_2410522 := by exact prefixLift 2410522
  have htrace : WordTrace (prefixWord ++ tailWord_2410522) baseStart_2410522 baseEnd_2410522 := by
    simpa [prefixWord, tailWord_2410522, baseEnd_2410522] using wordTrace_append hprefix tailTrace_2410522
  have hstable : (prefixWord ++ tailWord_2410522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410522).length < 2 ^ (prefixWord ++ tailWord_2410522).sum := by decide
  have hdescent : baseEnd_2410522 < baseStart_2410522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410533 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 2, 2, 2]
def baseStart_2410533 : Nat := 118140960795 + 2410533 * 2 ^ 59
def prefixEnd_2410533 : Nat := 4983230072969 + 3 ^ 40 * 2410533 * 2
def baseEnd_2410533 : Nat := 1237762062524522512251667

theorem tailTrace_2410533 : CollatzResearch.WordTrace tailWord_2410533 prefixEnd_2410533 1237762062524522512251667 := by
  unfold tailWord_2410533
  simp only [CollatzResearch.WordTrace]
  refine ⟨87919361376058102105492253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58612907584038734736994835 87919361376058102105492253)
  ·
    refine ⟨32969760516021788289559595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87919361376058102105492253 32969760516021788289559595)
    ·
      refine ⟨49454640774032682434339393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32969760516021788289559595 49454640774032682434339393)
      ·
        refine ⟨37090980580524511825754545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49454640774032682434339393 37090980580524511825754545)
        ·
          refine ⟨27818235435393383869315909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37090980580524511825754545 27818235435393383869315909)
          ·
            refine ⟨5215919144136259475496733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27818235435393383869315909 5215919144136259475496733)
            ·
              refine ⟨1955969679051097303311275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5215919144136259475496733 1955969679051097303311275)
              ·
                refine ⟨2933954518576645954966913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955969679051097303311275 2933954518576645954966913)
                ·
                  refine ⟨2200465888932484466225185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2933954518576645954966913 2200465888932484466225185)
                  ·
                    refine ⟨1650349416699363349668889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2200465888932484466225185 1650349416699363349668889)
                    ·
                      refine ⟨1237762062524522512251667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1650349416699363349668889 1237762062524522512251667)
                      ·
                        rfl

theorem cell23_2410533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_2410533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410533 prefixEnd_2410533 := by exact prefixLift 2410533
  have htrace : WordTrace (prefixWord ++ tailWord_2410533) baseStart_2410533 baseEnd_2410533 := by
    simpa [prefixWord, tailWord_2410533, baseEnd_2410533] using wordTrace_append hprefix tailTrace_2410533
  have hstable : (prefixWord ++ tailWord_2410533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410533).length < 2 ^ (prefixWord ++ tailWord_2410533).sum := by decide
  have hdescent : baseEnd_2410533 < baseStart_2410533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410572 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2410572 : Nat := 118140960795 + 2410572 * 2 ^ 59
def prefixEnd_2410572 : Nat := 4983230072969 + 3 ^ 40 * 2410572 * 2
def baseEnd_2410572 : Nat := 1237782088270047859663987

theorem tailTrace_2410572 : CollatzResearch.WordTrace tailWord_2410572 prefixEnd_2410572 1237782088270047859663987 := by
  unfold tailWord_2410572
  simp only [CollatzResearch.WordTrace]
  refine ⟨43960391911458405883080985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58613855881944541177441313 43960391911458405883080985)
  ·
    refine ⟨32970293933593804412310739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43960391911458405883080985 32970293933593804412310739)
    ·
      refine ⟨49455440900390706618466109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32970293933593804412310739 49455440900390706618466109)
      ·
        refine ⟨18545790337646514981924791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49455440900390706618466109 18545790337646514981924791)
        ·
          refine ⟨27818685506469772472887187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18545790337646514981924791 27818685506469772472887187)
          ·
            refine ⟨41728028259704658709330781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27818685506469772472887187 41728028259704658709330781)
            ·
              refine ⟨15648010597389247015999043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41728028259704658709330781 15648010597389247015999043)
              ·
                refine ⟨23472015896083870523998565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15648010597389247015999043 23472015896083870523998565)
                ·
                  refine ⟨4401002980515725723249731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23472015896083870523998565 4401002980515725723249731)
                  ·
                    refine ⟨6601504470773588584874597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4401002980515725723249731 6601504470773588584874597)
                    ·
                      refine ⟨1237782088270047859663987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6601504470773588584874597 1237782088270047859663987)
                      ·
                        rfl

theorem cell23_2410572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2410572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410572 prefixEnd_2410572 := by exact prefixLift 2410572
  have htrace : WordTrace (prefixWord ++ tailWord_2410572) baseStart_2410572 baseEnd_2410572 := by
    simpa [prefixWord, tailWord_2410572, baseEnd_2410572] using wordTrace_append hprefix tailTrace_2410572
  have hstable : (prefixWord ++ tailWord_2410572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410572).length < 2 ^ (prefixWord ++ tailWord_2410572).sum := by decide
  have hdescent : baseEnd_2410572 < baseStart_2410572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410575 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 5]
def baseStart_2410575 : Nat := 118140960795 + 2410575 * 2 ^ 59
def prefixEnd_2410575 : Nat := 4983230072969 + 3 ^ 40 * 2410575 * 2
def baseEnd_2410575 : Nat := 1237783628712011347926473

theorem tailTrace_2410575 : CollatzResearch.WordTrace tailWord_2410575 prefixEnd_2410575 1237783628712011347926473 := by
  unfold tailWord_2410575
  simp only [CollatzResearch.WordTrace]
  refine ⟨87920893241905943278521179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58613928827937295519014119 87920893241905943278521179)
  ·
    refine ⟨131881339862858914917781769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87920893241905943278521179 131881339862858914917781769)
    ·
      refine ⟨98911004897144186188336327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131881339862858914917781769 98911004897144186188336327)
      ·
        refine ⟨148366507345716279282504491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98911004897144186188336327 148366507345716279282504491)
        ·
          refine ⟨222549761018574418923756737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148366507345716279282504491 222549761018574418923756737)
          ·
            refine ⟨166912320763930814192817553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222549761018574418923756737 166912320763930814192817553)
            ·
              refine ⟨125184240572948110644613165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166912320763930814192817553 125184240572948110644613165)
              ·
                refine ⟨46944090214855541491729937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125184240572948110644613165 46944090214855541491729937)
                ·
                  refine ⟨35208067661141656118797453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46944090214855541491729937 35208067661141656118797453)
                  ·
                    refine ⟨13203025372928121044549045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35208067661141656118797453 13203025372928121044549045)
                    ·
                      refine ⟨1237783628712011347926473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13203025372928121044549045 1237783628712011347926473)
                      ·
                        rfl

theorem cell23_2410575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_2410575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410575 prefixEnd_2410575 := by exact prefixLift 2410575
  have htrace : WordTrace (prefixWord ++ tailWord_2410575) baseStart_2410575 baseEnd_2410575 := by
    simpa [prefixWord, tailWord_2410575, baseEnd_2410575] using wordTrace_append hprefix tailTrace_2410575
  have hstable : (prefixWord ++ tailWord_2410575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410575).length < 2 ^ (prefixWord ++ tailWord_2410575).sum := by decide
  have hdescent : baseEnd_2410575 < baseStart_2410575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410609 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 2, 2, 3]
def baseStart_2410609 : Nat := 118140960795 + 2410609 * 2 ^ 59
def prefixEnd_2410609 : Nat := 4983230072969 + 3 ^ 40 * 2410609 * 2
def baseEnd_2410609 : Nat := 1237801087054264214901317

theorem tailTrace_2410609 : CollatzResearch.WordTrace tailWord_2410609 prefixEnd_2410609 1237801087054264214901317 := by
  unfold tailWord_2410609
  simp only [CollatzResearch.WordTrace]
  refine ⟨87922133323782767085258881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58614755549188511390172587 87922133323782767085258881)
  ·
    refine ⟨65941599992837075313944161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87922133323782767085258881 65941599992837075313944161)
    ·
      refine ⟨49456199994627806485458121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65941599992837075313944161 49456199994627806485458121)
      ·
        refine ⟨37092149995970854864093591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49456199994627806485458121 37092149995970854864093591)
        ·
          refine ⟨55638224993956282296140387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37092149995970854864093591 55638224993956282296140387)
          ·
            refine ⟨83457337490934423444210581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55638224993956282296140387 83457337490934423444210581)
            ·
              refine ⟨3912062694887551098947371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83457337490934423444210581 3912062694887551098947371)
              ·
                refine ⟨5868094042331326648421057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3912062694887551098947371 5868094042331326648421057)
                ·
                  refine ⟨4401070531748494986315793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5868094042331326648421057 4401070531748494986315793)
                  ·
                    refine ⟨3300802898811371239736845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4401070531748494986315793 3300802898811371239736845)
                    ·
                      refine ⟨1237801087054264214901317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3300802898811371239736845 1237801087054264214901317)
                      ·
                        rfl

theorem cell23_2410609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_2410609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410609 prefixEnd_2410609 := by exact prefixLift 2410609
  have htrace : WordTrace (prefixWord ++ tailWord_2410609) baseStart_2410609 baseEnd_2410609 := by
    simpa [prefixWord, tailWord_2410609, baseEnd_2410609] using wordTrace_append hprefix tailTrace_2410609
  have hstable : (prefixWord ++ tailWord_2410609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410609).length < 2 ^ (prefixWord ++ tailWord_2410609).sum := by decide
  have hdescent : baseEnd_2410609 < baseStart_2410609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410629 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 6]
def baseStart_2410629 : Nat := 118140960795 + 2410629 * 2 ^ 59
def prefixEnd_2410629 : Nat := 4983230072969 + 3 ^ 40 * 2410629 * 2
def baseEnd_2410629 : Nat := 137534595185261570739025

theorem tailTrace_2410629 : CollatzResearch.WordTrace tailWord_2410629 prefixEnd_2410629 137534595185261570739025 := by
  unfold tailWord_2410629
  simp only [CollatzResearch.WordTrace]
  refine ⟨87922862783710310500986941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58615241855806873667324627 87922862783710310500986941)
  ·
    refine ⟨32971073543891366437870103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87922862783710310500986941 32971073543891366437870103)
    ·
      refine ⟨49456610315837049656805155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32971073543891366437870103 49456610315837049656805155)
      ·
        refine ⟨74184915473755574485207733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49456610315837049656805155 74184915473755574485207733)
        ·
          refine ⟨6954835825664585107988225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74184915473755574485207733 6954835825664585107988225)
          ·
            refine ⟨5216126869248438830991169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6954835825664585107988225 5216126869248438830991169)
            ·
              refine ⟨3912095151936329123243377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5216126869248438830991169 3912095151936329123243377)
              ·
                refine ⟨2934071363952246842432533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3912095151936329123243377 2934071363952246842432533)
                ·
                  refine ⟨137534595185261570739025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2934071363952246842432533 137534595185261570739025)
                  ·
                    rfl

theorem cell23_2410629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_2410629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410629 prefixEnd_2410629 := by exact prefixLift 2410629
  have htrace : WordTrace (prefixWord ++ tailWord_2410629) baseStart_2410629 baseEnd_2410629 := by
    simpa [prefixWord, tailWord_2410629, baseEnd_2410629] using wordTrace_append hprefix tailTrace_2410629
  have hstable : (prefixWord ++ tailWord_2410629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410629).length < 2 ^ (prefixWord ++ tailWord_2410629).sum := by decide
  have hdescent : baseEnd_2410629 < baseStart_2410629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410649 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 4, 3, 2]
def baseStart_2410649 : Nat := 118140960795 + 2410649 * 2 ^ 59
def prefixEnd_2410649 : Nat := 4983230072969 + 3 ^ 40 * 2410649 * 2
def baseEnd_2410649 : Nat := 1237821626280444058401133

theorem tailTrace_2410649 : CollatzResearch.WordTrace tailWord_2410649 prefixEnd_2410649 1237821626280444058401133 := by
  unfold tailWord_2410649
  simp only [CollatzResearch.WordTrace]
  refine ⟨87923592243637853916715001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58615728162425235944476667 87923592243637853916715001)
  ·
    refine ⟨65942694182728390437536251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87923592243637853916715001 65942694182728390437536251)
    ·
      refine ⟨98914041274092585656304377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65942694182728390437536251 98914041274092585656304377)
      ·
        refine ⟨74185530955569439242228283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98914041274092585656304377 74185530955569439242228283)
        ·
          refine ⟨111278296433354158863342425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74185530955569439242228283 111278296433354158863342425)
          ·
            refine ⟨83458722325015619147506819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111278296433354158863342425 83458722325015619147506819)
            ·
              refine ⟨125188083487523428721260229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83458722325015619147506819 125188083487523428721260229)
              ·
                refine ⟨23472765653910642885236293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125188083487523428721260229 23472765653910642885236293)
                ·
                  refine ⟨4401143560108245540981805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23472765653910642885236293 4401143560108245540981805)
                  ·
                    refine ⟨1650428835040592077868177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4401143560108245540981805 1650428835040592077868177)
                    ·
                      refine ⟨1237821626280444058401133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1650428835040592077868177 1237821626280444058401133)
                      ·
                        rfl

theorem cell23_2410649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 3, 2].length) (baseStart_2410649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410649 prefixEnd_2410649 := by exact prefixLift 2410649
  have htrace : WordTrace (prefixWord ++ tailWord_2410649) baseStart_2410649 baseEnd_2410649 := by
    simpa [prefixWord, tailWord_2410649, baseEnd_2410649] using wordTrace_append hprefix tailTrace_2410649
  have hstable : (prefixWord ++ tailWord_2410649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410649).length < 2 ^ (prefixWord ++ tailWord_2410649).sum := by decide
  have hdescent : baseEnd_2410649 < baseStart_2410649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410652 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2410652 : Nat := 118140960795 + 2410652 * 2 ^ 59
def prefixEnd_2410652 : Nat := 4983230072969 + 3 ^ 40 * 2410652 * 2
def baseEnd_2410652 : Nat := 1237823166722407546663619

theorem tailTrace_2410652 : CollatzResearch.WordTrace tailWord_2410652 prefixEnd_2410652 1237823166722407546663619 := by
  unfold tailWord_2410652
  simp only [CollatzResearch.WordTrace]
  refine ⟨43961850831313492714537105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58615801108417990286049473 43961850831313492714537105)
  ·
    refine ⟨32971388123485119535902829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43961850831313492714537105 32971388123485119535902829)
    ·
      refine ⟨12364270546306919825963561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32971388123485119535902829 12364270546306919825963561)
      ·
        refine ⟨9273202909730189869472671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12364270546306919825963561 9273202909730189869472671)
        ·
          refine ⟨13909804364595284804209007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9273202909730189869472671 13909804364595284804209007)
          ·
            refine ⟨20864706546892927206313511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13909804364595284804209007 20864706546892927206313511)
            ·
              refine ⟨31297059820339390809470267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20864706546892927206313511 31297059820339390809470267)
              ·
                refine ⟨46945589730509086214205401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31297059820339390809470267 46945589730509086214205401)
                ·
                  refine ⟨35209192297881814660654051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46945589730509086214205401 35209192297881814660654051)
                  ·
                    refine ⟨52813788446822721990981077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35209192297881814660654051 52813788446822721990981077)
                    ·
                      refine ⟨1237823166722407546663619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 52813788446822721990981077 1237823166722407546663619)
                      ·
                        rfl

theorem cell23_2410652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2410652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410652 prefixEnd_2410652 := by exact prefixLift 2410652
  have htrace : WordTrace (prefixWord ++ tailWord_2410652) baseStart_2410652 baseEnd_2410652 := by
    simpa [prefixWord, tailWord_2410652, baseEnd_2410652] using wordTrace_append hprefix tailTrace_2410652
  have hstable : (prefixWord ++ tailWord_2410652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410652).length < 2 ^ (prefixWord ++ tailWord_2410652).sum := by decide
  have hdescent : baseEnd_2410652 < baseStart_2410652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410656 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 3, 1, 3]
def baseStart_2410656 : Nat := 118140960795 + 2410656 * 2 ^ 59
def prefixEnd_2410656 : Nat := 4983230072969 + 3 ^ 40 * 2410656 * 2
def baseEnd_2410656 : Nat := 1237825220645025531013601

theorem tailTrace_2410656 : CollatzResearch.WordTrace tailWord_2410656 prefixEnd_2410656 1237825220645025531013601 := by
  unfold tailWord_2410656
  simp only [CollatzResearch.WordTrace]
  refine ⟨43961923777306247056109911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58615898369741662741479881 43961923777306247056109911)
  ·
    refine ⟨65942885665959370584164867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43961923777306247056109911 65942885665959370584164867)
    ·
      refine ⟨98914328498939055876247301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65942885665959370584164867 98914328498939055876247301)
      ·
        refine ⟨18546436593551072976796369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98914328498939055876247301 18546436593551072976796369)
        ·
          refine ⟨13909827445163304732597277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18546436593551072976796369 13909827445163304732597277)
          ·
            refine ⟨5216185291936239274723979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13909827445163304732597277 5216185291936239274723979)
            ·
              refine ⟨7824277937904358912085969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216185291936239274723979 7824277937904358912085969)
              ·
                refine ⟨5868208453428269184064477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7824277937904358912085969 5868208453428269184064477)
                ·
                  refine ⟨2200578170035600944024179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5868208453428269184064477 2200578170035600944024179)
                  ·
                    refine ⟨3300867255053401416036269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2200578170035600944024179 3300867255053401416036269)
                    ·
                      refine ⟨1237825220645025531013601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3300867255053401416036269 1237825220645025531013601)
                      ·
                        rfl

theorem cell23_2410656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_2410656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410656 prefixEnd_2410656 := by exact prefixLift 2410656
  have htrace : WordTrace (prefixWord ++ tailWord_2410656) baseStart_2410656 baseEnd_2410656 := by
    simpa [prefixWord, tailWord_2410656, baseEnd_2410656] using wordTrace_append hprefix tailTrace_2410656
  have hstable : (prefixWord ++ tailWord_2410656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410656).length < 2 ^ (prefixWord ++ tailWord_2410656).sum := by decide
  have hdescent : baseEnd_2410656 < baseStart_2410656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410690 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_2410690 : Nat := 118140960795 + 2410690 * 2 ^ 59
def prefixEnd_2410690 : Nat := 4983230072969 + 3 ^ 40 * 2410690 * 2
def baseEnd_2410690 : Nat := 1237842678987278397988445

theorem tailTrace_2410690 : CollatzResearch.WordTrace tailWord_2410690 prefixEnd_2410690 1237842678987278397988445 := by
  unfold tailWord_2410690
  simp only [CollatzResearch.WordTrace]
  refine ⟨21981271909122329479739381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58616725090992878612638349 21981271909122329479739381)
  ·
    refine ⟨2060744241480218388725567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21981271909122329479739381 2060744241480218388725567)
    ·
      refine ⟨3091116362220327583088351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2060744241480218388725567 3091116362220327583088351)
      ·
        refine ⟨4636674543330491374632527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3091116362220327583088351 4636674543330491374632527)
        ·
          refine ⟨6955011814995737061948791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4636674543330491374632527 6955011814995737061948791)
          ·
            refine ⟨10432517722493605592923187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6955011814995737061948791 10432517722493605592923187)
            ·
              refine ⟨15648776583740408389384781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10432517722493605592923187 15648776583740408389384781)
              ·
                refine ⟨5868291218902653146019293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15648776583740408389384781 5868291218902653146019293)
                ·
                  refine ⟨2200609207088494929757235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5868291218902653146019293 2200609207088494929757235)
                  ·
                    refine ⟨3300913810632742394635853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2200609207088494929757235 3300913810632742394635853)
                    ·
                      refine ⟨1237842678987278397988445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3300913810632742394635853 1237842678987278397988445)
                      ·
                        rfl

theorem cell23_2410690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_2410690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410690 prefixEnd_2410690 := by exact prefixLift 2410690
  have htrace : WordTrace (prefixWord ++ tailWord_2410690) baseStart_2410690 baseEnd_2410690 := by
    simpa [prefixWord, tailWord_2410690, baseEnd_2410690] using wordTrace_append hprefix tailTrace_2410690
  have hstable : (prefixWord ++ tailWord_2410690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410690).length < 2 ^ (prefixWord ++ tailWord_2410690).sum := by decide
  have hdescent : baseEnd_2410690 < baseStart_2410690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410706 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 1, 6]
def baseStart_2410706 : Nat := 118140960795 + 2410706 * 2 ^ 59
def prefixEnd_2410706 : Nat := 4983230072969 + 3 ^ 40 * 2410706 * 2
def baseEnd_2410706 : Nat := 412616964892583445129457

theorem tailTrace_2410706 : CollatzResearch.WordTrace tailWord_2410706 prefixEnd_2410706 412616964892583445129457 := by
  unfold tailWord_2410706
  simp only [CollatzResearch.WordTrace]
  refine ⟨21981417801107838162884993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58617114136287568434359981 21981417801107838162884993)
  ·
    refine ⟨16486063350830878622163745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21981417801107838162884993 16486063350830878622163745)
    ·
      refine ⟨12364547513123158966622809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16486063350830878622163745 12364547513123158966622809)
      ·
        refine ⟨9273410634842369224967107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12364547513123158966622809 9273410634842369224967107)
        ·
          refine ⟨13910115952263553837450661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9273410634842369224967107 13910115952263553837450661)
          ·
            refine ⟨2608146741049416344521999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13910115952263553837450661 2608146741049416344521999)
            ·
              refine ⟨3912220111574124516782999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2608146741049416344521999 3912220111574124516782999)
              ·
                refine ⟨5868330167361186775174499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3912220111574124516782999 5868330167361186775174499)
                ·
                  refine ⟨8802495251041780162761749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5868330167361186775174499 8802495251041780162761749)
                  ·
                    refine ⟨412616964892583445129457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8802495251041780162761749 412616964892583445129457)
                    ·
                      rfl

theorem cell23_2410706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_2410706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410706 prefixEnd_2410706 := by exact prefixLift 2410706
  have htrace : WordTrace (prefixWord ++ tailWord_2410706) baseStart_2410706 baseEnd_2410706 := by
    simpa [prefixWord, tailWord_2410706, baseEnd_2410706] using wordTrace_append hprefix tailTrace_2410706
  have hstable : (prefixWord ++ tailWord_2410706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410706).length < 2 ^ (prefixWord ++ tailWord_2410706).sum := by decide
  have hdescent : baseEnd_2410706 < baseStart_2410706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410746 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3]
def baseStart_2410746 : Nat := 118140960795 + 2410746 * 2 ^ 59
def prefixEnd_2410746 : Nat := 4983230072969 + 3 ^ 40 * 2410746 * 2
def baseEnd_2410746 : Nat := 1237871433903930178888187

theorem tailTrace_2410746 : CollatzResearch.WordTrace tailWord_2410746 prefixEnd_2410746 1237871433903930178888187 := by
  unfold tailWord_2410746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21981782531071609870749023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58618086749524292988664061 21981782531071609870749023)
  ·
    refine ⟨32972673796607414806123535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21981782531071609870749023 32972673796607414806123535)
    ·
      refine ⟨49459010694911122209185303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32972673796607414806123535 49459010694911122209185303)
      ·
        refine ⟨74188516042366683313777955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49459010694911122209185303 74188516042366683313777955)
        ·
          refine ⟨111282774063550024970666933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74188516042366683313777955 111282774063550024970666933)
          ·
            refine ⟨10432760068457814841000025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111282774063550024970666933 10432760068457814841000025)
            ·
              refine ⟨7824570051343361130750019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10432760068457814841000025 7824570051343361130750019)
              ·
                refine ⟨11736855077015041696125029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7824570051343361130750019 11736855077015041696125029)
                ·
                  refine ⟨2200660326940320318023443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11736855077015041696125029 2200660326940320318023443)
                  ·
                    refine ⟨3300990490410480477035165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2200660326940320318023443 3300990490410480477035165)
                    ·
                      refine ⟨1237871433903930178888187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3300990490410480477035165 1237871433903930178888187)
                      ·
                        rfl

theorem cell23_2410746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_2410746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410746 prefixEnd_2410746 := by exact prefixLift 2410746
  have htrace : WordTrace (prefixWord ++ tailWord_2410746) baseStart_2410746 baseEnd_2410746 := by
    simpa [prefixWord, tailWord_2410746, baseEnd_2410746] using wordTrace_append hprefix tailTrace_2410746
  have hstable : (prefixWord ++ tailWord_2410746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410746).length < 2 ^ (prefixWord ++ tailWord_2410746).sum := by decide
  have hdescent : baseEnd_2410746 < baseStart_2410746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410773 : List Nat := [1, 3, 2, 1, 2, 1, 5, 2, 1, 3, 2]
def baseStart_2410773 : Nat := 118140960795 + 2410773 * 2 ^ 59
def prefixEnd_2410773 : Nat := 4983230072969 + 3 ^ 40 * 2410773 * 2
def baseEnd_2410773 : Nat := 1237885297881601573250563

theorem tailTrace_2410773 : CollatzResearch.WordTrace tailWord_2410773 prefixEnd_2410773 1237885297881601573250563 := by
  unfold tailWord_2410773
  simp only [CollatzResearch.WordTrace]
  refine ⟨87928114895188623094228973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58618743263459082062819315 87928114895188623094228973)
  ·
    refine ⟨32973043085695733660335865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87928114895188623094228973 32973043085695733660335865)
    ·
      refine ⟨24729782314271800245251899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32973043085695733660335865 24729782314271800245251899)
      ·
        refine ⟨37094673471407700367877849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24729782314271800245251899 37094673471407700367877849)
        ·
          refine ⟨27821005103555775275908387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37094673471407700367877849 27821005103555775275908387)
          ·
            refine ⟨41731507655333662913862581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27821005103555775275908387 41731507655333662913862581)
            ·
              refine ⟨3912328842687530898174617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41731507655333662913862581 3912328842687530898174617)
              ·
                refine ⟨2934246632015648173630963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3912328842687530898174617 2934246632015648173630963)
                ·
                  refine ⟨4401369948023472260446445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934246632015648173630963 4401369948023472260446445)
                  ·
                    refine ⟨1650513730508802097667417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4401369948023472260446445 1650513730508802097667417)
                    ·
                      refine ⟨1237885297881601573250563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1650513730508802097667417 1237885297881601573250563)
                      ·
                        rfl

theorem cell23_2410773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_2410773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410773 prefixEnd_2410773 := by exact prefixLift 2410773
  have htrace : WordTrace (prefixWord ++ tailWord_2410773) baseStart_2410773 baseEnd_2410773 := by
    simpa [prefixWord, tailWord_2410773, baseEnd_2410773] using wordTrace_append hprefix tailTrace_2410773
  have hstable : (prefixWord ++ tailWord_2410773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410773).length < 2 ^ (prefixWord ++ tailWord_2410773).sum := by decide
  have hdescent : baseEnd_2410773 < baseStart_2410773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410797 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2410797 : Nat := 118140960795 + 2410797 * 2 ^ 59
def prefixEnd_2410797 : Nat := 4983230072969 + 3 ^ 40 * 2410797 * 2
def baseEnd_2410797 : Nat := 1237897621417309479350453

theorem tailTrace_2410797 : CollatzResearch.WordTrace tailWord_2410797 prefixEnd_2410797 1237897621417309479350453 := by
  unfold tailWord_2410797
  simp only [CollatzResearch.WordTrace]
  refine ⟨87928990247101675193102645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58619326831401116795401763 87928990247101675193102645)
  ·
    refine ⟨8243342835665782049353373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87928990247101675193102645 8243342835665782049353373)
    ·
      refine ⟨3091253563374668268507515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8243342835665782049353373 3091253563374668268507515)
      ·
        refine ⟨4636880345062002402761273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3091253563374668268507515 4636880345062002402761273)
        ·
          refine ⟨3477660258796501802070955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4636880345062002402761273 3477660258796501802070955)
          ·
            refine ⟨5216490388194752703106433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477660258796501802070955 5216490388194752703106433)
            ·
              refine ⟨3912367791146064527329825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5216490388194752703106433 3912367791146064527329825)
              ·
                refine ⟨2934275843359548395497369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3912367791146064527329825 2934275843359548395497369)
                ·
                  refine ⟨2200706882519661296623027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2934275843359548395497369 2200706882519661296623027)
                  ·
                    refine ⟨3301060323779491944934541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2200706882519661296623027 3301060323779491944934541)
                    ·
                      refine ⟨1237897621417309479350453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3301060323779491944934541 1237897621417309479350453)
                      ·
                        rfl

theorem cell23_2410797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2410797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410797 prefixEnd_2410797 := by exact prefixLift 2410797
  have htrace : WordTrace (prefixWord ++ tailWord_2410797) baseStart_2410797 baseEnd_2410797 := by
    simpa [prefixWord, tailWord_2410797, baseEnd_2410797] using wordTrace_append hprefix tailTrace_2410797
  have hstable : (prefixWord ++ tailWord_2410797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410797).length < 2 ^ (prefixWord ++ tailWord_2410797).sum := by decide
  have hdescent : baseEnd_2410797 < baseStart_2410797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410798 : List Nat := [4, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2410798 : Nat := 118140960795 + 2410798 * 2 ^ 59
def prefixEnd_2410798 : Nat := 4983230072969 + 3 ^ 40 * 2410798 * 2
def baseEnd_2410798 : Nat := 1237898134897963975437949

theorem tailTrace_2410798 : CollatzResearch.WordTrace tailWord_2410798 prefixEnd_2410798 1237898134897963975437949 := by
  unfold tailWord_2410798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10991128340012256545486131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58619351146732034909259365 10991128340012256545486131)
  ·
    refine ⟨16486692510018384818229197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10991128340012256545486131 16486692510018384818229197)
    ·
      refine ⟨6182509691256894306835949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16486692510018384818229197 6182509691256894306835949)
      ·
        refine ⟨2318441134221335365063481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6182509691256894306835949 2318441134221335365063481)
        ·
          refine ⟨1738830850666001523797611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2318441134221335365063481 1738830850666001523797611)
          ·
            refine ⟨2608246275999002285696417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738830850666001523797611 2608246275999002285696417)
            ·
              refine ⟨1956184706999251714272313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2608246275999002285696417 1956184706999251714272313)
              ·
                refine ⟨1467138530249438785704235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1956184706999251714272313 1467138530249438785704235)
                ·
                  refine ⟨2200707795374158178556353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467138530249438785704235 2200707795374158178556353)
                  ·
                    refine ⟨1650530846530618633917265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2200707795374158178556353 1650530846530618633917265)
                    ·
                      refine ⟨1237898134897963975437949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1650530846530618633917265 1237898134897963975437949)
                      ·
                        rfl

theorem cell23_2410798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2410798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410798 prefixEnd_2410798 := by exact prefixLift 2410798
  have htrace : WordTrace (prefixWord ++ tailWord_2410798) baseStart_2410798 baseEnd_2410798 := by
    simpa [prefixWord, tailWord_2410798, baseEnd_2410798] using wordTrace_append hprefix tailTrace_2410798
  have hstable : (prefixWord ++ tailWord_2410798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410798).length < 2 ^ (prefixWord ++ tailWord_2410798).sum := by decide
  have hdescent : baseEnd_2410798 < baseStart_2410798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410819 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 3]
def baseStart_2410819 : Nat := 118140960795 + 2410819 * 2 ^ 59
def prefixEnd_2410819 : Nat := 4983230072969 + 3 ^ 40 * 2410819 * 2
def baseEnd_2410819 : Nat := 1237908917991708393275351

theorem tailTrace_2410819 : CollatzResearch.WordTrace tailWord_2410819 prefixEnd_2410819 1237908917991708393275351 := by
  unfold tailWord_2410819
  simp only [CollatzResearch.WordTrace]
  refine ⟨87929792653021972950403511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58619861768681315300269007 87929792653021972950403511)
  ·
    refine ⟨131894688979532959425605267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87929792653021972950403511 131894688979532959425605267)
    ·
      refine ⟨197842033469299439138407901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131894688979532959425605267 197842033469299439138407901)
      ·
        refine ⟨74190762550987289676902963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197842033469299439138407901 74190762550987289676902963)
        ·
          refine ⟨111286143826480934515354445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74190762550987289676902963 111286143826480934515354445)
          ·
            refine ⟨41732303934930350443257917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111286143826480934515354445 41732303934930350443257917)
            ·
              refine ⟨15649613975598881416221719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41732303934930350443257917 15649613975598881416221719)
              ·
                refine ⟨23474420963398322124332579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15649613975598881416221719 23474420963398322124332579)
                ·
                  refine ⟨35211631445097483186498869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23474420963398322124332579 35211631445097483186498869)
                  ·
                    refine ⟨3301090447977889048734269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35211631445097483186498869 3301090447977889048734269)
                    ·
                      refine ⟨1237908917991708393275351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3301090447977889048734269 1237908917991708393275351)
                      ·
                        rfl

theorem cell23_2410819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_2410819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410819 prefixEnd_2410819 := by exact prefixLift 2410819
  have htrace : WordTrace (prefixWord ++ tailWord_2410819) baseStart_2410819 baseEnd_2410819 := by
    simpa [prefixWord, tailWord_2410819, baseEnd_2410819] using wordTrace_append hprefix tailTrace_2410819
  have hstable : (prefixWord ++ tailWord_2410819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410819).length < 2 ^ (prefixWord ++ tailWord_2410819).sum := by decide
  have hdescent : baseEnd_2410819 < baseStart_2410819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410839 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 1, 7]
def baseStart_2410839 : Nat := 118140960795 + 2410839 * 2 ^ 59
def prefixEnd_2410839 : Nat := 4983230072969 + 3 ^ 40 * 2410839 * 2
def baseEnd_2410839 : Nat := 412639729201599438341753

theorem tailTrace_2410839 : CollatzResearch.WordTrace tailWord_2410839 prefixEnd_2410839 412639729201599438341753 := by
  unfold tailWord_2410839
  simp only [CollatzResearch.WordTrace]
  refine ⟨87930522112949516366131571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58620348075299677577421047 87930522112949516366131571)
  ·
    refine ⟨131895783169424274549197357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87930522112949516366131571 131895783169424274549197357)
    ·
      refine ⟨49460918688534102955949009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131895783169424274549197357 49460918688534102955949009)
      ·
        refine ⟨37095689016400577216961757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49460918688534102955949009 37095689016400577216961757)
        ·
          refine ⟨13910883381150216456360659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37095689016400577216961757 13910883381150216456360659)
          ·
            refine ⟨20866325071725324684540989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13910883381150216456360659 20866325071725324684540989)
            ·
              refine ⟨7824871901896996756702871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20866325071725324684540989 7824871901896996756702871)
              ·
                refine ⟨11737307852845495135054307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7824871901896996756702871 11737307852845495135054307)
                ·
                  refine ⟨17605961779268242702581461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11737307852845495135054307 17605961779268242702581461)
                  ·
                    refine ⟨412639729201599438341753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17605961779268242702581461 412639729201599438341753)
                    ·
                      rfl

theorem cell23_2410839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_2410839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410839 prefixEnd_2410839 := by exact prefixLift 2410839
  have htrace : WordTrace (prefixWord ++ tailWord_2410839) baseStart_2410839 baseEnd_2410839 := by
    simpa [prefixWord, tailWord_2410839, baseEnd_2410839] using wordTrace_append hprefix tailTrace_2410839
  have hstable : (prefixWord ++ tailWord_2410839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410839).length < 2 ^ (prefixWord ++ tailWord_2410839).sum := by decide
  have hdescent : baseEnd_2410839 < baseStart_2410839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410876 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 1, 6, 2]
def baseStart_2410876 : Nat := 118140960795 + 2410876 * 2 ^ 59
def prefixEnd_2410876 : Nat := 4983230072969 + 3 ^ 40 * 2410876 * 2
def baseEnd_2410876 : Nat := 1237938186389014670262589

theorem tailTrace_2410876 : CollatzResearch.WordTrace tailWord_2410876 prefixEnd_2410876 1237938186389014670262589 := by
  unfold tailWord_2410876
  simp only [CollatzResearch.WordTrace]
  refine ⟨43965935806907735842614241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58621247742543647790152321 43965935806907735842614241)
  ·
    refine ⟨32974451855180801881960681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43965935806907735842614241 32974451855180801881960681)
    ·
      refine ⟨24730838891385601411470511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32974451855180801881960681 24730838891385601411470511)
      ·
        refine ⟨37096258337078402117205767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24730838891385601411470511 37096258337078402117205767)
        ·
          refine ⟨55644387505617603175808651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37096258337078402117205767 55644387505617603175808651)
          ·
            refine ⟨83466581258426404763712977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55644387505617603175808651 83466581258426404763712977)
            ·
              refine ⟨62599935943819803572784733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83466581258426404763712977 62599935943819803572784733)
              ·
                refine ⟨23474975978932426339794275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62599935943819803572784733 23474975978932426339794275)
                ·
                  refine ⟨35212463968398639509691413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23474975978932426339794275 35212463968398639509691413)
                  ·
                    refine ⟨1650584248518686227016785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35212463968398639509691413 1650584248518686227016785)
                    ·
                      refine ⟨1237938186389014670262589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1650584248518686227016785 1237938186389014670262589)
                      ·
                        rfl

theorem cell23_2410876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_2410876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410876 prefixEnd_2410876 := by exact prefixLift 2410876
  have htrace : WordTrace (prefixWord ++ tailWord_2410876) baseStart_2410876 baseEnd_2410876 := by
    simpa [prefixWord, tailWord_2410876, baseEnd_2410876] using wordTrace_append hprefix tailTrace_2410876
  have hstable : (prefixWord ++ tailWord_2410876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410876).length < 2 ^ (prefixWord ++ tailWord_2410876).sum := by decide
  have hdescent : baseEnd_2410876 < baseStart_2410876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410910 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2410910 : Nat := 118140960795 + 2410910 * 2 ^ 59
def prefixEnd_2410910 : Nat := 4983230072969 + 3 ^ 40 * 2410910 * 2
def baseEnd_2410910 : Nat := 1237955644731267537237433

theorem tailTrace_2410910 : CollatzResearch.WordTrace tailWord_2410910 prefixEnd_2410910 1237955644731267537237433 := by
  unfold tailWord_2410910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10991638961961536936495773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58622074463794863661310789 10991638961961536936495773)
  ·
    refine ⟨4121864610735576351185915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10991638961961536936495773 4121864610735576351185915)
    ·
      refine ⟨6182796916103364526778873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4121864610735576351185915 6182796916103364526778873)
      ·
        refine ⟨4637097687077523395084155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6182796916103364526778873 4637097687077523395084155)
        ·
          refine ⟨6955646530616285092626233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4637097687077523395084155 6955646530616285092626233)
          ·
            refine ⟨5216734897962213819469675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6955646530616285092626233 5216734897962213819469675)
            ·
              refine ⟨7825102346943320729204513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216734897962213819469675 7825102346943320729204513)
              ·
                refine ⟨5868826760207490546903385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7825102346943320729204513 5868826760207490546903385)
                ·
                  refine ⟨4401620070155617910177539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5868826760207490546903385 4401620070155617910177539)
                  ·
                    refine ⟨6602430105233426865266309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4401620070155617910177539 6602430105233426865266309)
                    ·
                      refine ⟨1237955644731267537237433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6602430105233426865266309 1237955644731267537237433)
                      ·
                        rfl

theorem cell23_2410910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2410910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410910 prefixEnd_2410910 := by exact prefixLift 2410910
  have htrace : WordTrace (prefixWord ++ tailWord_2410910) baseStart_2410910 baseEnd_2410910 := by
    simpa [prefixWord, tailWord_2410910, baseEnd_2410910] using wordTrace_append hprefix tailTrace_2410910
  have hstable : (prefixWord ++ tailWord_2410910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410910).length < 2 ^ (prefixWord ++ tailWord_2410910).sum := by decide
  have hdescent : baseEnd_2410910 < baseStart_2410910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410920 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2410920 : Nat := 118140960795 + 2410920 * 2 ^ 59
def prefixEnd_2410920 : Nat := 4983230072969 + 3 ^ 40 * 2410920 * 2
def baseEnd_2410920 : Nat := 412653593179270832704129

theorem tailTrace_2410920 : CollatzResearch.WordTrace tailWord_2410920 prefixEnd_2410920 412653593179270832704129 := by
  unfold tailWord_2410920
  simp only [CollatzResearch.WordTrace]
  refine ⟨43966738212828033599915107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58622317617104044799886809 43966738212828033599915107)
  ·
    refine ⟨65950107319242050399872661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43966738212828033599915107 65950107319242050399872661)
    ·
      refine ⟨3091411280589471112494031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65950107319242050399872661 3091411280589471112494031)
      ·
        refine ⟨4637116920884206668741047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3091411280589471112494031 4637116920884206668741047)
        ·
          refine ⟨6955675381326310003111571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4637116920884206668741047 6955675381326310003111571)
          ·
            refine ⟨10433513071989465004667357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6955675381326310003111571 10433513071989465004667357)
            ·
              refine ⟨3912567401996049376750259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10433513071989465004667357 3912567401996049376750259)
              ·
                refine ⟨5868851102994074065125389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3912567401996049376750259 5868851102994074065125389)
                ·
                  refine ⟨2200819163622777774422021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5868851102994074065125389 2200819163622777774422021)
                  ·
                    refine ⟨412653593179270832704129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2200819163622777774422021 412653593179270832704129)
                    ·
                      rfl

theorem cell23_2410920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2410920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410920 prefixEnd_2410920 := by exact prefixLift 2410920
  have htrace : WordTrace (prefixWord ++ tailWord_2410920) baseStart_2410920 baseEnd_2410920 := by
    simpa [prefixWord, tailWord_2410920, baseEnd_2410920] using wordTrace_append hprefix tailTrace_2410920
  have hstable : (prefixWord ++ tailWord_2410920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410920).length < 2 ^ (prefixWord ++ tailWord_2410920).sum := by decide
  have hdescent : baseEnd_2410920 < baseStart_2410920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410933 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 6]
def baseStart_2410933 : Nat := 118140960795 + 2410933 * 2 ^ 59
def prefixEnd_2410933 : Nat := 4983230072969 + 3 ^ 40 * 2410933 * 2
def baseEnd_2410933 : Nat := 137551939420702327472203

theorem tailTrace_2410933 : CollatzResearch.WordTrace tailWord_2410933 prefixEnd_2410933 137551939420702327472203 := by
  unfold tailWord_2410933
  simp only [CollatzResearch.WordTrace]
  refine ⟨87933950574608970420053453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58622633716405980280035635 87933950574608970420053453)
  ·
    refine ⟨32975231465478363907520045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87933950574608970420053453 32975231465478363907520045)
    ·
      refine ⟨12365711799554386465320017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32975231465478363907520045 12365711799554386465320017)
      ·
        refine ⟨9274283849665789848990013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12365711799554386465320017 9274283849665789848990013)
        ·
          refine ⟨3477856443624671193371255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9274283849665789848990013 3477856443624671193371255)
          ·
            refine ⟨5216784665437006790056883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3477856443624671193371255 5216784665437006790056883)
            ·
              refine ⟨7825176998155510185085325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216784665437006790056883 7825176998155510185085325)
              ·
                refine ⟨2934441374308316319406997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7825176998155510185085325 2934441374308316319406997)
                ·
                  refine ⟨137551939420702327472203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2934441374308316319406997 137551939420702327472203)
                  ·
                    rfl

theorem cell23_2410933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_2410933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410933 prefixEnd_2410933 := by exact prefixLift 2410933
  have htrace : WordTrace (prefixWord ++ tailWord_2410933) baseStart_2410933 baseEnd_2410933 := by
    simpa [prefixWord, tailWord_2410933, baseEnd_2410933] using wordTrace_append hprefix tailTrace_2410933
  have hstable : (prefixWord ++ tailWord_2410933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410933).length < 2 ^ (prefixWord ++ tailWord_2410933).sum := by decide
  have hdescent : baseEnd_2410933 < baseStart_2410933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410953 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 2, 3, 2]
def baseStart_2410953 : Nat := 118140960795 + 2410953 * 2 ^ 59
def prefixEnd_2410953 : Nat := 4983230072969 + 3 ^ 40 * 2410953 * 2
def baseEnd_2410953 : Nat := 1237977724399410868999735

theorem tailTrace_2410953 : CollatzResearch.WordTrace tailWord_2410953 prefixEnd_2410953 1237977724399410868999735 := by
  unfold tailWord_2410953
  simp only [CollatzResearch.WordTrace]
  refine ⟨87934680034536513835781513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58623120023024342557187675 87934680034536513835781513)
  ·
    refine ⟨65951010025902385376836135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87934680034536513835781513 65951010025902385376836135)
    ·
      refine ⟨98926515038853578065254203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65951010025902385376836135 98926515038853578065254203)
      ·
        refine ⟨148389772558280367097881305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98926515038853578065254203 148389772558280367097881305)
        ·
          refine ⟨111292329418710275323410979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148389772558280367097881305 111292329418710275323410979)
          ·
            refine ⟨166938494128065412985116469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111292329418710275323410979 166938494128065412985116469)
            ·
              refine ⟨15650483824506132467354669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 166938494128065412985116469 15650483824506132467354669)
              ·
                refine ⟨5868931434189799675258001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15650483824506132467354669 5868931434189799675258001)
                ·
                  refine ⟨4401698575642349756443501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5868931434189799675258001 4401698575642349756443501)
                  ·
                    refine ⟨1650636965865881158666313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4401698575642349756443501 1650636965865881158666313)
                    ·
                      refine ⟨1237977724399410868999735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1650636965865881158666313 1237977724399410868999735)
                      ·
                        rfl

theorem cell23_2410953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 3, 2].length) (baseStart_2410953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410953 prefixEnd_2410953 := by exact prefixLift 2410953
  have htrace : WordTrace (prefixWord ++ tailWord_2410953) baseStart_2410953 baseEnd_2410953 := by
    simpa [prefixWord, tailWord_2410953, baseEnd_2410953] using wordTrace_append hprefix tailTrace_2410953
  have hstable : (prefixWord ++ tailWord_2410953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410953).length < 2 ^ (prefixWord ++ tailWord_2410953).sum := by decide
  have hdescent : baseEnd_2410953 < baseStart_2410953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2410993 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 2, 4]
def baseStart_2410993 : Nat := 118140960795 + 2410993 * 2 ^ 59
def prefixEnd_2410993 : Nat := 4983230072969 + 3 ^ 40 * 2410993 * 2
def baseEnd_2410993 : Nat := 412666087875196904166517

theorem tailTrace_2410993 : CollatzResearch.WordTrace tailWord_2410993 prefixEnd_2410993 412666087875196904166517 := by
  unfold tailWord_2410993
  simp only [CollatzResearch.WordTrace]
  refine ⟨87936138954391600667237633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58624092636261067111491755 87936138954391600667237633)
  ·
    refine ⟨65952104215793700500428225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87936138954391600667237633 65952104215793700500428225)
    ·
      refine ⟨49464078161845275375321169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65952104215793700500428225 49464078161845275375321169)
      ·
        refine ⟨37098058621383956531490877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49464078161845275375321169 37098058621383956531490877)
        ·
          refine ⟨13911771983018983699309079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37098058621383956531490877 13911771983018983699309079)
          ·
            refine ⟨20867657974528475548963619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13911771983018983699309079 20867657974528475548963619)
            ·
              refine ⟨31301486961792713323445429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20867657974528475548963619 31301486961792713323445429)
              ·
                refine ⟨2934514402668066874073009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31301486961792713323445429 2934514402668066874073009)
                ·
                  refine ⟨2200885802001050155554757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2934514402668066874073009 2200885802001050155554757)
                  ·
                    refine ⟨412666087875196904166517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2200885802001050155554757 412666087875196904166517)
                    ·
                      rfl

theorem cell23_2410993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_2410993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2410993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2410993 prefixEnd_2410993 := by exact prefixLift 2410993
  have htrace : WordTrace (prefixWord ++ tailWord_2410993) baseStart_2410993 baseEnd_2410993 := by
    simpa [prefixWord, tailWord_2410993, baseEnd_2410993] using wordTrace_append hprefix tailTrace_2410993
  have hstable : (prefixWord ++ tailWord_2410993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2410993).length < 2 ^ (prefixWord ++ tailWord_2410993).sum := by decide
  have hdescent : baseEnd_2410993 < baseStart_2410993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2410993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411000 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 3, 2, 2]
def baseStart_2411000 : Nat := 118140960795 + 2411000 * 2 ^ 59
def prefixEnd_2411000 : Nat := 4983230072969 + 3 ^ 40 * 2411000 * 2
def baseEnd_2411000 : Nat := 1238001857990172185112019

theorem tailTrace_2411000 : CollatzResearch.WordTrace tailWord_2411000 prefixEnd_2411000 1238001857990172185112019 := by
  unfold tailWord_2411000
  simp only [CollatzResearch.WordTrace]
  refine ⟨43968197132683120431371227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58624262843577493908494969 43968197132683120431371227)
  ·
    refine ⟨65952295699024680647056841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43968197132683120431371227 65952295699024680647056841)
    ·
      refine ⟨49464221774268510485292631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65952295699024680647056841 49464221774268510485292631)
      ·
        refine ⟨74196332661402765727938947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49464221774268510485292631 74196332661402765727938947)
        ·
          refine ⟨111294498992104148591908421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74196332661402765727938947 111294498992104148591908421)
          ·
            refine ⟨20867718561019527860982829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111294498992104148591908421 20867718561019527860982829)
            ·
              refine ⟨7825394460382322947868561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20867718561019527860982829 7825394460382322947868561)
              ·
                refine ⟨5869045845286742210901421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7825394460382322947868561 5869045845286742210901421)
                ·
                  refine ⟨2200892191982528329088033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5869045845286742210901421 2200892191982528329088033)
                  ·
                    refine ⟨1650669143986896246816025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2200892191982528329088033 1650669143986896246816025)
                    ·
                      refine ⟨1238001857990172185112019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1650669143986896246816025 1238001857990172185112019)
                      ·
                        rfl

theorem cell23_2411000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 3, 2, 2].length) (baseStart_2411000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411000 prefixEnd_2411000 := by exact prefixLift 2411000
  have htrace : WordTrace (prefixWord ++ tailWord_2411000) baseStart_2411000 baseEnd_2411000 := by
    simpa [prefixWord, tailWord_2411000, baseEnd_2411000] using wordTrace_append hprefix tailTrace_2411000
  have hstable : (prefixWord ++ tailWord_2411000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411000).length < 2 ^ (prefixWord ++ tailWord_2411000).sum := by decide
  have hdescent : baseEnd_2411000 < baseStart_2411000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411014 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2411014 : Nat := 118140960795 + 2411014 * 2 ^ 59
def prefixEnd_2411014 : Nat := 4983230072969 + 3 ^ 40 * 2411014 * 2
def baseEnd_2411014 : Nat := 412669682239778376778985

theorem tailTrace_2411014 : CollatzResearch.WordTrace tailWord_2411014 prefixEnd_2411014 412669682239778376778985 := by
  unfold tailWord_2411014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748028277728610039179753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58624603258210347502501397 2748028277728610039179753)
  ·
    refine ⟨2061021208296457529384815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2748028277728610039179753 2061021208296457529384815)
    ·
      refine ⟨3091531812444686294077223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2061021208296457529384815 3091531812444686294077223)
      ·
        refine ⟨4637297718667029441115835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3091531812444686294077223 4637297718667029441115835)
        ·
          refine ⟨6955946578000544161673753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4637297718667029441115835 6955946578000544161673753)
          ·
            refine ⟨5216959933500408121255315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6955946578000544161673753 5216959933500408121255315)
            ·
              refine ⟨7825439900250612181882973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216959933500408121255315 7825439900250612181882973)
              ·
                refine ⟨2934539962593979568206115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7825439900250612181882973 2934539962593979568206115)
                ·
                  refine ⟨4401809943890969352309173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934539962593979568206115 4401809943890969352309173)
                  ·
                    refine ⟨412669682239778376778985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4401809943890969352309173 412669682239778376778985)
                    ·
                      rfl

theorem cell23_2411014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2411014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411014 prefixEnd_2411014 := by exact prefixLift 2411014
  have htrace : WordTrace (prefixWord ++ tailWord_2411014) baseStart_2411014 baseEnd_2411014 := by
    simpa [prefixWord, tailWord_2411014, baseEnd_2411014] using wordTrace_append hprefix tailTrace_2411014
  have hstable : (prefixWord ++ tailWord_2411014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411014).length < 2 ^ (prefixWord ++ tailWord_2411014).sum := by decide
  have hdescent : baseEnd_2411014 < baseStart_2411014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411020 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 1, 2, 3]
def baseStart_2411020 : Nat := 118140960795 + 2411020 * 2 ^ 59
def prefixEnd_2411020 : Nat := 4983230072969 + 3 ^ 40 * 2411020 * 2
def baseEnd_2411020 : Nat := 1238012127603262106861927

theorem tailTrace_2411020 : CollatzResearch.WordTrace tailWord_2411020 prefixEnd_2411020 1238012127603262106861927 := by
  unfold tailWord_2411020
  simp only [CollatzResearch.WordTrace]
  refine ⟨43968561862646892139235257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58624749150195856185647009 43968561862646892139235257)
  ·
    refine ⟨32976421396985169104426443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43968561862646892139235257 32976421396985169104426443)
    ·
      refine ⟨49464632095477753656639665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32976421396985169104426443 49464632095477753656639665)
      ·
        refine ⟨37098474071608315242479749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49464632095477753656639665 37098474071608315242479749)
        ·
          refine ⟨6955963888426559107964953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37098474071608315242479749 6955963888426559107964953)
          ·
            refine ⟨5216972916319919330973715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6955963888426559107964953 5216972916319919330973715)
            ·
              refine ⟨7825459374479878996460573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5216972916319919330973715 7825459374479878996460573)
              ·
                refine ⟨2934547265429954623672715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7825459374479878996460573 2934547265429954623672715)
                ·
                  refine ⟨4401820898144931935509073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934547265429954623672715 4401820898144931935509073)
                  ·
                    refine ⟨3301365673608698951631805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4401820898144931935509073 3301365673608698951631805)
                    ·
                      refine ⟨1238012127603262106861927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3301365673608698951631805 1238012127603262106861927)
                      ·
                        rfl

theorem cell23_2411020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_2411020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411020 prefixEnd_2411020 := by exact prefixLift 2411020
  have htrace : WordTrace (prefixWord ++ tailWord_2411020) baseStart_2411020 baseEnd_2411020 := by
    simpa [prefixWord, tailWord_2411020, baseEnd_2411020] using wordTrace_append hprefix tailTrace_2411020
  have hstable : (prefixWord ++ tailWord_2411020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411020).length < 2 ^ (prefixWord ++ tailWord_2411020).sum := by decide
  have hdescent : baseEnd_2411020 < baseStart_2411020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411033 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 4, 1, 3]
def baseStart_2411033 : Nat := 118140960795 + 2411033 * 2 ^ 59
def prefixEnd_2411033 : Nat := 4983230072969 + 3 ^ 40 * 2411033 * 2
def baseEnd_2411033 : Nat := 1238018802851770555999367

theorem tailTrace_2411033 : CollatzResearch.WordTrace tailWord_2411033 prefixEnd_2411033 1238018802851770555999367 := by
  unfold tailWord_2411033
  simp only [CollatzResearch.WordTrace]
  refine ⟨87937597874246687498693753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58625065249497791665795835 87937597874246687498693753)
  ·
    refine ⟨65953198405685015624020315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87937597874246687498693753 65953198405685015624020315)
    ·
      refine ⟨98929797608527523436030473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65953198405685015624020315 98929797608527523436030473)
      ·
        refine ⟨74197348206395642577022855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98929797608527523436030473 74197348206395642577022855)
        ·
          refine ⟨111296022309593463865534283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74197348206395642577022855 111296022309593463865534283)
          ·
            refine ⟨166944033464390195798301425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111296022309593463865534283 166944033464390195798301425)
            ·
              refine ⟨125208025098292646848726069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166944033464390195798301425 125208025098292646848726069)
              ·
                refine ⟨11738252352964935642068069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125208025098292646848726069 11738252352964935642068069)
                ·
                  refine ⟨2200922316180925432887763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11738252352964935642068069 2200922316180925432887763)
                  ·
                    refine ⟨3301383474271388149331645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2200922316180925432887763 3301383474271388149331645)
                    ·
                      refine ⟨1238018802851770555999367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3301383474271388149331645 1238018802851770555999367)
                      ·
                        rfl

theorem cell23_2411033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_2411033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411033 prefixEnd_2411033 := by exact prefixLift 2411033
  have htrace : WordTrace (prefixWord ++ tailWord_2411033) baseStart_2411033 baseEnd_2411033 := by
    simpa [prefixWord, tailWord_2411033, baseEnd_2411033] using wordTrace_append hprefix tailTrace_2411033
  have hstable : (prefixWord ++ tailWord_2411033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411033).length < 2 ^ (prefixWord ++ tailWord_2411033).sum := by decide
  have hdescent : baseEnd_2411033 < baseStart_2411033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411044 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_2411044 : Nat := 118140960795 + 2411044 * 2 ^ 59
def prefixEnd_2411044 : Nat := 4983230072969 + 3 ^ 40 * 2411044 * 2
def baseEnd_2411044 : Nat := 412674817046323337653939

theorem tailTrace_2411044 : CollatzResearch.WordTrace tailWord_2411044 prefixEnd_2411044 412674817046323337653939 := by
  unfold tailWord_2411044
  simp only [CollatzResearch.WordTrace]
  refine ⟨43968999538603418188672093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58625332718137890918229457 43968999538603418188672093)
  ·
    refine ⟨16488374826976281820752035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43968999538603418188672093 16488374826976281820752035)
    ·
      refine ⟨24732562240464422731128053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16488374826976281820752035 24732562240464422731128053)
      ·
        refine ⟨2318677710043539631043255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24732562240464422731128053 2318677710043539631043255)
        ·
          refine ⟨3478016565065309446564883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318677710043539631043255 3478016565065309446564883)
          ·
            refine ⟨5217024847597964169847325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478016565065309446564883 5217024847597964169847325)
            ·
              refine ⟨1956384317849236563692747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5217024847597964169847325 1956384317849236563692747)
              ·
                refine ⟨2934576476773854845539121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1956384317849236563692747 2934576476773854845539121)
                ·
                  refine ⟨2200932357580391134154341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2934576476773854845539121 2200932357580391134154341)
                  ·
                    refine ⟨412674817046323337653939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2200932357580391134154341 412674817046323337653939)
                    ·
                      rfl

theorem cell23_2411044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_2411044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411044 prefixEnd_2411044 := by exact prefixLift 2411044
  have htrace : WordTrace (prefixWord ++ tailWord_2411044) baseStart_2411044 baseEnd_2411044 := by
    simpa [prefixWord, tailWord_2411044, baseEnd_2411044] using wordTrace_append hprefix tailTrace_2411044
  have hstable : (prefixWord ++ tailWord_2411044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411044).length < 2 ^ (prefixWord ++ tailWord_2411044).sum := by decide
  have hdescent : baseEnd_2411044 < baseStart_2411044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411050 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_2411050 : Nat := 118140960795 + 2411050 * 2 ^ 59
def prefixEnd_2411050 : Nat := 4983230072969 + 3 ^ 40 * 2411050 * 2
def baseEnd_2411050 : Nat := 1238027532022896989486789

theorem tailTrace_2411050 : CollatzResearch.WordTrace tailWord_2411050 prefixEnd_2411050 1238027532022896989486789 := by
  unfold tailWord_2411050
  simp only [CollatzResearch.WordTrace]
  refine ⟨21984554478796274850515651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58625478610123399601375069 21984554478796274850515651)
  ·
    refine ⟨32976831718194412275773477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21984554478796274850515651 32976831718194412275773477)
    ·
      refine ⟨6183155947161452301707527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32976831718194412275773477 6183155947161452301707527)
      ·
        refine ⟨9274733920742178452561291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6183155947161452301707527 9274733920742178452561291)
        ·
          refine ⟨13912100881113267678841937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9274733920742178452561291 13912100881113267678841937)
          ·
            refine ⟨10434075660834950759131453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13912100881113267678841937 10434075660834950759131453)
            ·
              refine ⟨3912778372813106534674295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10434075660834950759131453 3912778372813106534674295)
              ·
                refine ⟨5869167559219659802011443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3912778372813106534674295 5869167559219659802011443)
                ·
                  refine ⟨8803751338829489703017165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5869167559219659802011443 8803751338829489703017165)
                  ·
                    refine ⟨3301406752061058638631437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8803751338829489703017165 3301406752061058638631437)
                    ·
                      refine ⟨1238027532022896989486789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3301406752061058638631437 1238027532022896989486789)
                      ·
                        rfl

theorem cell23_2411050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_2411050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411050 prefixEnd_2411050 := by exact prefixLift 2411050
  have htrace : WordTrace (prefixWord ++ tailWord_2411050) baseStart_2411050 baseEnd_2411050 := by
    simpa [prefixWord, tailWord_2411050, baseEnd_2411050] using wordTrace_append hprefix tailTrace_2411050
  have hstable : (prefixWord ++ tailWord_2411050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411050).length < 2 ^ (prefixWord ++ tailWord_2411050).sum := by decide
  have hdescent : baseEnd_2411050 < baseStart_2411050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411056 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 4]
def baseStart_2411056 : Nat := 118140960795 + 2411056 * 2 ^ 59
def prefixEnd_2411056 : Nat := 4983230072969 + 3 ^ 40 * 2411056 * 2
def baseEnd_2411056 : Nat := 1238030612906823966011761

theorem tailTrace_2411056 : CollatzResearch.WordTrace tailWord_2411056 prefixEnd_2411056 1238030612906823966011761 := by
  unfold tailWord_2411056
  simp only [CollatzResearch.WordTrace]
  refine ⟨43969218376581681213390511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58625624502108908284520681 43969218376581681213390511)
  ·
    refine ⟨65953827564872521820085767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43969218376581681213390511 65953827564872521820085767)
    ·
      refine ⟨98930741347308782730128651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65953827564872521820085767 98930741347308782730128651)
      ·
        refine ⟨148396112020963174095192977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98930741347308782730128651 148396112020963174095192977)
        ·
          refine ⟨111297084015722380571394733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148396112020963174095192977 111297084015722380571394733)
          ·
            refine ⟨41736406505895892714273025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111297084015722380571394733 41736406505895892714273025)
            ·
              refine ⟨31302304879421919535704769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41736406505895892714273025 31302304879421919535704769)
              ·
                refine ⟨23476728659566439651778577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31302304879421919535704769 23476728659566439651778577)
                ·
                  refine ⟨17607546494674829738833933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23476728659566439651778577 17607546494674829738833933)
                  ·
                    refine ⟨6602829935503061152062725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17607546494674829738833933 6602829935503061152062725)
                    ·
                      refine ⟨1238030612906823966011761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6602829935503061152062725 1238030612906823966011761)
                      ·
                        rfl

theorem cell23_2411056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_2411056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411056 prefixEnd_2411056 := by exact prefixLift 2411056
  have htrace : WordTrace (prefixWord ++ tailWord_2411056) baseStart_2411056 baseEnd_2411056 := by
    simpa [prefixWord, tailWord_2411056, baseEnd_2411056] using wordTrace_append hprefix tailTrace_2411056
  have hstable : (prefixWord ++ tailWord_2411056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411056).length < 2 ^ (prefixWord ++ tailWord_2411056).sum := by decide
  have hdescent : baseEnd_2411056 < baseStart_2411056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411107 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 2, 2, 2]
def baseStart_2411107 : Nat := 118140960795 + 2411107 * 2 ^ 59
def prefixEnd_2411107 : Nat := 4983230072969 + 3 ^ 40 * 2411107 * 2
def baseEnd_2411107 : Nat := 1238056800420203266474027

theorem tailTrace_2411107 : CollatzResearch.WordTrace tailWord_2411107 prefixEnd_2411107 1238056800420203266474027 := by
  unfold tailWord_2411107
  simp only [CollatzResearch.WordTrace]
  refine ⟨87940296875978598136887575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58626864583985732091258383 87940296875978598136887575)
  ·
    refine ⟨131910445313967897205331363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87940296875978598136887575 131910445313967897205331363)
    ·
      refine ⟨197865667970951845807997045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131910445313967897205331363 197865667970951845807997045)
      ·
        refine ⟨18549906372276735544499723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197865667970951845807997045 18549906372276735544499723)
        ·
          refine ⟨27824859558415103316749585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18549906372276735544499723 27824859558415103316749585)
          ·
            refine ⟨20868644668811327487562189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27824859558415103316749585 20868644668811327487562189)
            ·
              refine ⟨7825741750804247807835821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20868644668811327487562189 7825741750804247807835821)
              ·
                refine ⟨2934653156551592927938433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7825741750804247807835821 2934653156551592927938433)
                ·
                  refine ⟨2200989867413694695953825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2934653156551592927938433 2200989867413694695953825)
                  ·
                    refine ⟨1650742400560271021965369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2200989867413694695953825 1650742400560271021965369)
                    ·
                      refine ⟨1238056800420203266474027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1650742400560271021965369 1238056800420203266474027)
                      ·
                        rfl

theorem cell23_2411107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_2411107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411107 prefixEnd_2411107 := by exact prefixLift 2411107
  have htrace : WordTrace (prefixWord ++ tailWord_2411107) baseStart_2411107 baseEnd_2411107 := by
    simpa [prefixWord, tailWord_2411107, baseEnd_2411107] using wordTrace_append hprefix tailTrace_2411107
  have hstable : (prefixWord ++ tailWord_2411107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411107).length < 2 ^ (prefixWord ++ tailWord_2411107).sum := by decide
  have hdescent : baseEnd_2411107 < baseStart_2411107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411143 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 2, 5]
def baseStart_2411143 : Nat := 118140960795 + 2411143 * 2 ^ 59
def prefixEnd_2411143 : Nat := 4983230072969 + 3 ^ 40 * 2411143 * 2
def baseEnd_2411143 : Nat := 412691761907921708541287

theorem tailTrace_2411143 : CollatzResearch.WordTrace tailWord_2411143 prefixEnd_2411143 412691761907921708541287 := by
  unfold tailWord_2411143
  simp only [CollatzResearch.WordTrace]
  refine ⟨87941609903848176285198083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58627739935898784190132055 87941609903848176285198083)
  ·
    refine ⟨131912414855772264427797125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87941609903848176285198083 131912414855772264427797125)
    ·
      refine ⟨24733577785457299580211961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 131912414855772264427797125 24733577785457299580211961)
      ·
        refine ⟨18550183339092974685158971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24733577785457299580211961 18550183339092974685158971)
        ·
          refine ⟨27825275008639462027738457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18550183339092974685158971 27825275008639462027738457)
          ·
            refine ⟨20868956256479596520803843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27825275008639462027738457 20868956256479596520803843)
            ·
              refine ⟨31303434384719394781205765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20868956256479596520803843 31303434384719394781205765)
              ·
                refine ⟨5869393947134886521476081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31303434384719394781205765 5869393947134886521476081)
                ·
                  refine ⟨4402045460351164891107061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5869393947134886521476081 4402045460351164891107061)
                  ·
                    refine ⟨412691761907921708541287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4402045460351164891107061 412691761907921708541287)
                    ·
                      rfl

theorem cell23_2411143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_2411143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411143 prefixEnd_2411143 := by exact prefixLift 2411143
  have htrace : WordTrace (prefixWord ++ tailWord_2411143) baseStart_2411143 baseEnd_2411143 := by
    simpa [prefixWord, tailWord_2411143, baseEnd_2411143] using wordTrace_append hprefix tailTrace_2411143
  have hstable : (prefixWord ++ tailWord_2411143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411143).length < 2 ^ (prefixWord ++ tailWord_2411143).sum := by decide
  have hdescent : baseEnd_2411143 < baseStart_2411143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411150 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2]
def baseStart_2411150 : Nat := 118140960795 + 2411150 * 2 ^ 59
def prefixEnd_2411150 : Nat := 4983230072969 + 3 ^ 40 * 2411150 * 2
def baseEnd_2411150 : Nat := 1238078880088346598236329

theorem tailTrace_2411150 : CollatzResearch.WordTrace tailWord_2411150 prefixEnd_2411150 1238078880088346598236329 := by
  unfold tailWord_2411150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10992733151852852060087863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58627910143215210987135269 10992733151852852060087863)
  ·
    refine ⟨16489099727779278090131795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10992733151852852060087863 16489099727779278090131795)
    ·
      refine ⟨24733649591668917135197693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16489099727779278090131795 24733649591668917135197693)
      ·
        refine ⟨9275118596875843925699135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24733649591668917135197693 9275118596875843925699135)
        ·
          refine ⟨13912677895313765888548703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9275118596875843925699135 13912677895313765888548703)
          ·
            refine ⟨20869016842970648832823055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13912677895313765888548703 20869016842970648832823055)
            ·
              refine ⟨31303525264455973249234583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20869016842970648832823055 31303525264455973249234583)
              ·
                refine ⟨46955287896683959873851875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31303525264455973249234583 46955287896683959873851875)
                ·
                  refine ⟨70432931845025939810777813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46955287896683959873851875 70432931845025939810777813)
                  ·
                    refine ⟨1650771840117795464315105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 70432931845025939810777813 1650771840117795464315105)
                    ·
                      refine ⟨1238078880088346598236329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1650771840117795464315105 1238078880088346598236329)
                      ·
                        rfl

theorem cell23_2411150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_2411150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411150 prefixEnd_2411150 := by exact prefixLift 2411150
  have htrace : WordTrace (prefixWord ++ tailWord_2411150) baseStart_2411150 baseEnd_2411150 := by
    simpa [prefixWord, tailWord_2411150, baseEnd_2411150] using wordTrace_append hprefix tailTrace_2411150
  have hstable : (prefixWord ++ tailWord_2411150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411150).length < 2 ^ (prefixWord ++ tailWord_2411150).sum := by decide
  have hdescent : baseEnd_2411150 < baseStart_2411150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411283 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 6]
def baseStart_2411283 : Nat := 118140960795 + 2411283 * 2 ^ 59
def prefixEnd_2411283 : Nat := 4983230072969 + 3 ^ 40 * 2411283 * 2
def baseEnd_2411283 : Nat := 1238147173015394577873217

theorem tailTrace_2411283 : CollatzResearch.WordTrace tailWord_2411283 prefixEnd_2411283 1238147173015394577873217 := by
  unfold tailWord_2411283
  simp only [CollatzResearch.WordTrace]
  refine ⟨87946716123340980195294503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58631144082227320130196335 87946716123340980195294503)
  ·
    refine ⟨131920074185011470292941755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87946716123340980195294503 131920074185011470292941755)
    ·
      refine ⟨197880111277517205439412633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131920074185011470292941755 197880111277517205439412633)
      ·
        refine ⟨148410083458137904079559475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197880111277517205439412633 148410083458137904079559475)
        ·
          refine ⟨222615125187206856119339213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148410083458137904079559475 222615125187206856119339213)
          ·
            refine ⟨83480671945202571044752205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222615125187206856119339213 83480671945202571044752205)
            ·
              refine ⟨31305251979450964141782077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83480671945202571044752205 31305251979450964141782077)
              ·
                refine ⟨11739469492294111553168279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31305251979450964141782077 11739469492294111553168279)
                ·
                  refine ⟨17609204238441167329752419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11739469492294111553168279 17609204238441167329752419)
                  ·
                    refine ⟨26413806357661750994628629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17609204238441167329752419 26413806357661750994628629)
                    ·
                      refine ⟨1238147173015394577873217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26413806357661750994628629 1238147173015394577873217)
                      ·
                        rfl

theorem cell23_2411283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_2411283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411283 prefixEnd_2411283 := by exact prefixLift 2411283
  have htrace : WordTrace (prefixWord ++ tailWord_2411283) baseStart_2411283 baseEnd_2411283 := by
    simpa [prefixWord, tailWord_2411283, baseEnd_2411283] using wordTrace_append hprefix tailTrace_2411283
  have hstable : (prefixWord ++ tailWord_2411283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411283).length < 2 ^ (prefixWord ++ tailWord_2411283).sum := by decide
  have hdescent : baseEnd_2411283 < baseStart_2411283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411287 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 4]
def baseStart_2411287 : Nat := 118140960795 + 2411287 * 2 ^ 59
def prefixEnd_2411287 : Nat := 4983230072969 + 3 ^ 40 * 2411287 * 2
def baseEnd_2411287 : Nat := 1238149226938012562223199

theorem tailTrace_2411287 : CollatzResearch.WordTrace tailWord_2411287 prefixEnd_2411287 1238149226938012562223199 := by
  unfold tailWord_2411287
  simp only [CollatzResearch.WordTrace]
  refine ⟨87946862015326488878440115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58631241343550992585626743 87946862015326488878440115)
  ·
    refine ⟨131920293022989733317660173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87946862015326488878440115 131920293022989733317660173)
    ·
      refine ⟨49470109883621149994122565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131920293022989733317660173 49470109883621149994122565)
      ·
        refine ⟨9275645603178965623897981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49470109883621149994122565 9275645603178965623897981)
        ·
          refine ⟨3478367101192112108961743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9275645603178965623897981 3478367101192112108961743)
          ·
            refine ⟨5217550651788168163442615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478367101192112108961743 5217550651788168163442615)
            ·
              refine ⟨7826325977682252245163923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217550651788168163442615 7826325977682252245163923)
              ·
                refine ⟨11739488966523378367745885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7826325977682252245163923 11739488966523378367745885)
                ·
                  refine ⟨4402308362446266887904707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11739488966523378367745885 4402308362446266887904707)
                  ·
                    refine ⟨6603462543669400331857061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4402308362446266887904707 6603462543669400331857061)
                    ·
                      refine ⟨1238149226938012562223199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6603462543669400331857061 1238149226938012562223199)
                      ·
                        rfl

theorem cell23_2411287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_2411287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411287 prefixEnd_2411287 := by exact prefixLift 2411287
  have htrace : WordTrace (prefixWord ++ tailWord_2411287) baseStart_2411287 baseEnd_2411287 := by
    simpa [prefixWord, tailWord_2411287, baseEnd_2411287] using wordTrace_append hprefix tailTrace_2411287
  have hstable : (prefixWord ++ tailWord_2411287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411287).length < 2 ^ (prefixWord ++ tailWord_2411287).sum := by decide
  have hdescent : baseEnd_2411287 < baseStart_2411287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411304 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_2411304 : Nat := 118140960795 + 2411304 * 2 ^ 59
def prefixEnd_2411304 : Nat := 4983230072969 + 3 ^ 40 * 2411304 * 2
def baseEnd_2411304 : Nat := 1238157956109138995710621

theorem tailTrace_2411304 : CollatzResearch.WordTrace tailWord_2411304 prefixEnd_2411304 1238157956109138995710621 := by
  unfold tailWord_2411304
  simp only [CollatzResearch.WordTrace]
  refine ⟨43973741028132450390904483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58631654704176600521205977 43973741028132450390904483)
  ·
    refine ⟨65960611542198675586356725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43973741028132450390904483 65960611542198675586356725)
    ·
      refine ⟨6183807332081125836220943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65960611542198675586356725 6183807332081125836220943)
      ·
        refine ⟨9275710998121688754331415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6183807332081125836220943 9275710998121688754331415)
        ·
          refine ⟨13913566497182533131497123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9275710998121688754331415 13913566497182533131497123)
          ·
            refine ⟨20870349745773799697245685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13913566497182533131497123 20870349745773799697245685)
            ·
              refine ⟨1956595288666293721616783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20870349745773799697245685 1956595288666293721616783)
              ·
                refine ⟨2934892932999440582425175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1956595288666293721616783 2934892932999440582425175)
                ·
                  refine ⟨4402339399499160873637763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2934892932999440582425175 4402339399499160873637763)
                  ·
                    refine ⟨6603509099248741310456645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4402339399499160873637763 6603509099248741310456645)
                    ·
                      refine ⟨1238157956109138995710621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6603509099248741310456645 1238157956109138995710621)
                      ·
                        rfl

theorem cell23_2411304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_2411304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411304 prefixEnd_2411304 := by exact prefixLift 2411304
  have htrace : WordTrace (prefixWord ++ tailWord_2411304) baseStart_2411304 baseEnd_2411304 := by
    simpa [prefixWord, tailWord_2411304, baseEnd_2411304] using wordTrace_append hprefix tailTrace_2411304
  have hstable : (prefixWord ++ tailWord_2411304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411304).length < 2 ^ (prefixWord ++ tailWord_2411304).sum := by decide
  have hdescent : baseEnd_2411304 < baseStart_2411304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411310 : List Nat := [4, 1, 3, 2, 1, 12]
def baseStart_2411310 : Nat := 118140960795 + 2411310 * 2 ^ 59
def prefixEnd_2411310 : Nat := 4983230072969 + 3 ^ 40 * 2411310 * 2
def baseEnd_2411310 : Nat := 5095312909436485482451

theorem tailTrace_2411310 : CollatzResearch.WordTrace tailWord_2411310 prefixEnd_2411310 5095312909436485482451 := by
  unfold tailWord_2411310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10993462611780395475815923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58631800596162109204351589 10993462611780395475815923)
  ·
    refine ⟨16490193917670593213723885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10993462611780395475815923 16490193917670593213723885)
    ·
      refine ⟨6183822719126472455146457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16490193917670593213723885 6183822719126472455146457)
      ·
        refine ⟨4637867039344854341359843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6183822719126472455146457 4637867039344854341359843)
        ·
          refine ⟨6956800559017281512039765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4637867039344854341359843 6956800559017281512039765)
          ·
            refine ⟨5095312909436485482451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6956800559017281512039765 5095312909436485482451)
            ·
              rfl

theorem cell23_2411310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 12].length) (baseStart_2411310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411310 prefixEnd_2411310 := by exact prefixLift 2411310
  have htrace : WordTrace (prefixWord ++ tailWord_2411310) baseStart_2411310 baseEnd_2411310 := by
    simpa [prefixWord, tailWord_2411310, baseEnd_2411310] using wordTrace_append hprefix tailTrace_2411310
  have hstable : (prefixWord ++ tailWord_2411310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411310).length < 2 ^ (prefixWord ++ tailWord_2411310).sum := by decide
  have hdescent : baseEnd_2411310 < baseStart_2411310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411320 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 3, 3, 3]
def baseStart_2411320 : Nat := 118140960795 + 2411320 * 2 ^ 59
def prefixEnd_2411320 : Nat := 4983230072969 + 3 ^ 40 * 2411320 * 2
def baseEnd_2411320 : Nat := 1238166171799610933110547

theorem tailTrace_2411320 : CollatzResearch.WordTrace tailWord_2411320 prefixEnd_2411320 1238166171799610933110547 := by
  unfold tailWord_2411320
  simp only [CollatzResearch.WordTrace]
  refine ⟨43974032812103467757195707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58632043749471290342927609 43974032812103467757195707)
  ·
    refine ⟨65961049218155201635793561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43974032812103467757195707 65961049218155201635793561)
    ·
      refine ⟨49470786913616401226845171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65961049218155201635793561 49470786913616401226845171)
      ·
        refine ⟨74206180370424601840267757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49470786913616401226845171 74206180370424601840267757)
        ·
          refine ⟨27827317638909225690100409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74206180370424601840267757 27827317638909225690100409)
          ·
            refine ⟨20870488229181919267575307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27827317638909225690100409 20870488229181919267575307)
            ·
              refine ⟨31305732343772878901362961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20870488229181919267575307 31305732343772878901362961)
              ·
                refine ⟨23479299257829659176022221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31305732343772878901362961 23479299257829659176022221)
                ·
                  refine ⟨8804737221686122191008333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23479299257829659176022221 8804737221686122191008333)
                  ·
                    refine ⟨3301776458132295821628125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8804737221686122191008333 3301776458132295821628125)
                    ·
                      refine ⟨1238166171799610933110547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3301776458132295821628125 1238166171799610933110547)
                      ·
                        rfl

theorem cell23_2411320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_2411320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411320 prefixEnd_2411320 := by exact prefixLift 2411320
  have htrace : WordTrace (prefixWord ++ tailWord_2411320) baseStart_2411320 baseEnd_2411320 := by
    simpa [prefixWord, tailWord_2411320, baseEnd_2411320] using wordTrace_append hprefix tailTrace_2411320
  have hstable : (prefixWord ++ tailWord_2411320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411320).length < 2 ^ (prefixWord ++ tailWord_2411320).sum := by decide
  have hdescent : baseEnd_2411320 < baseStart_2411320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411337 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 1, 3, 3]
def baseStart_2411337 : Nat := 118140960795 + 2411337 * 2 ^ 59
def prefixEnd_2411337 : Nat := 4983230072969 + 3 ^ 40 * 2411337 * 2
def baseEnd_2411337 : Nat := 1238174900970737366597969

theorem tailTrace_2411337 : CollatzResearch.WordTrace tailWord_2411337 prefixEnd_2411337 1238174900970737366597969 := by
  unfold tailWord_2411337
  simp only [CollatzResearch.WordTrace]
  refine ⟨87948685665145347417760265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58632457110096898278506843 87948685665145347417760265)
  ·
    refine ⟨65961514248859010563320199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87948685665145347417760265 65961514248859010563320199)
    ·
      refine ⟨98942271373288515844980299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65961514248859010563320199 98942271373288515844980299)
      ·
        refine ⟨148413407059932773767470449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98942271373288515844980299 148413407059932773767470449)
        ·
          refine ⟨111310055294949580325602837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148413407059932773767470449 111310055294949580325602837)
          ·
            refine ⟨5217658841950761577762633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111310055294949580325602837 5217658841950761577762633)
            ·
              refine ⟨3913244131463071183321975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5217658841950761577762633 3913244131463071183321975)
              ·
                refine ⟨5869866197194606774982963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913244131463071183321975 5869866197194606774982963)
                ·
                  refine ⟨8804799295791910162474445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5869866197194606774982963 8804799295791910162474445)
                  ·
                    refine ⟨3301799735921966310927917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8804799295791910162474445 3301799735921966310927917)
                    ·
                      refine ⟨1238174900970737366597969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3301799735921966310927917 1238174900970737366597969)
                      ·
                        rfl

theorem cell23_2411337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 3, 3].length) (baseStart_2411337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411337 prefixEnd_2411337 := by exact prefixLift 2411337
  have htrace : WordTrace (prefixWord ++ tailWord_2411337) baseStart_2411337 baseEnd_2411337 := by
    simpa [prefixWord, tailWord_2411337, baseEnd_2411337] using wordTrace_append hprefix tailTrace_2411337
  have hstable : (prefixWord ++ tailWord_2411337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411337).length < 2 ^ (prefixWord ++ tailWord_2411337).sum := by decide
  have hdescent : baseEnd_2411337 < baseStart_2411337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411462 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_2411462 : Nat := 118140960795 + 2411462 * 2 ^ 59
def prefixEnd_2411462 : Nat := 4983230072969 + 3 ^ 40 * 2411462 * 2
def baseEnd_2411462 : Nat := 1238239086052549377534895

theorem tailTrace_2411462 : CollatzResearch.WordTrace tailWord_2411462 prefixEnd_2411462 1238239086052549377534895 := by
  unfold tailWord_2411462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2748538899677890430189395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58635496526461662510707093 2748538899677890430189395)
  ·
    refine ⟨4122808349516835645284093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2748538899677890430189395 4122808349516835645284093)
    ·
      refine ⟨1546053131068813366981535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4122808349516835645284093 1546053131068813366981535)
      ·
        refine ⟨2319079696603220050472303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546053131068813366981535 2319079696603220050472303)
        ·
          refine ⟨3478619544904830075708455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2319079696603220050472303 3478619544904830075708455)
          ·
            refine ⟨5217929317357245113562683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478619544904830075708455 5217929317357245113562683)
            ·
              refine ⟨7826893976035867670344025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217929317357245113562683 7826893976035867670344025)
              ·
                refine ⟨5870170482026900752758019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7826893976035867670344025 5870170482026900752758019)
                ·
                  refine ⟨8805255723040351129137029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5870170482026900752758019 8805255723040351129137029)
                  ·
                    refine ⟨1650985448070065836713193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8805255723040351129137029 1650985448070065836713193)
                    ·
                      refine ⟨1238239086052549377534895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1650985448070065836713193 1238239086052549377534895)
                      ·
                        rfl

theorem cell23_2411462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_2411462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411462 prefixEnd_2411462 := by exact prefixLift 2411462
  have htrace : WordTrace (prefixWord ++ tailWord_2411462) baseStart_2411462 baseEnd_2411462 := by
    simpa [prefixWord, tailWord_2411462, baseEnd_2411462] using wordTrace_append hprefix tailTrace_2411462
  have hstable : (prefixWord ++ tailWord_2411462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411462).length < 2 ^ (prefixWord ++ tailWord_2411462).sum := by decide
  have hdescent : baseEnd_2411462 < baseStart_2411462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411464 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 2, 5]
def baseStart_2411464 : Nat := 118140960795 + 2411464 * 2 ^ 59
def prefixEnd_2411464 : Nat := 4983230072969 + 3 ^ 40 * 2411464 * 2
def baseEnd_2411464 : Nat := 412746704337952789903295

theorem tailTrace_2411464 : CollatzResearch.WordTrace tailWord_2411464 prefixEnd_2411464 412746704337952789903295 := by
  unfold tailWord_2411464
  simp only [CollatzResearch.WordTrace]
  refine ⟨43976658867842624053816723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58635545157123498738422297 43976658867842624053816723)
  ·
    refine ⟨65964988301763936080725085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43976658867842624053816723 65964988301763936080725085)
    ·
      refine ⟨24736870613161476030271907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65964988301763936080725085 24736870613161476030271907)
      ·
        refine ⟨37105305919742214045407861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24736870613161476030271907 37105305919742214045407861)
        ·
          refine ⟨3478622429975832566756987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37105305919742214045407861 3478622429975832566756987)
          ·
            refine ⟨5217933644963748850135481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478622429975832566756987 5217933644963748850135481)
            ·
              refine ⟨3913450233722811637601611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5217933644963748850135481 3913450233722811637601611)
              ·
                refine ⟨5870175350584217456402417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913450233722811637601611 5870175350584217456402417)
                ·
                  refine ⟨4402631512938163092301813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5870175350584217456402417 4402631512938163092301813)
                  ·
                    refine ⟨412746704337952789903295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4402631512938163092301813 412746704337952789903295)
                    ·
                      rfl

theorem cell23_2411464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_2411464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411464 prefixEnd_2411464 := by exact prefixLift 2411464
  have htrace : WordTrace (prefixWord ++ tailWord_2411464) baseStart_2411464 baseEnd_2411464 := by
    simpa [prefixWord, tailWord_2411464, baseEnd_2411464] using wordTrace_append hprefix tailTrace_2411464
  have hstable : (prefixWord ++ tailWord_2411464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411464).length < 2 ^ (prefixWord ++ tailWord_2411464).sum := by decide
  have hdescent : baseEnd_2411464 < baseStart_2411464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411467 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 4]
def baseStart_2411467 : Nat := 118140960795 + 2411467 * 2 ^ 59
def prefixEnd_2411467 : Nat := 4983230072969 + 3 ^ 40 * 2411467 * 2
def baseEnd_2411467 : Nat := 1238241653455821857972371

theorem tailTrace_2411467 : CollatzResearch.WordTrace tailWord_2411467 prefixEnd_2411467 1238241653455821857972371 := by
  unfold tailWord_2411467
  simp only [CollatzResearch.WordTrace]
  refine ⟨87953427154674379619992655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58635618103116253079995103 87953427154674379619992655)
  ·
    refine ⟨131930140732011569429988983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87953427154674379619992655 131930140732011569429988983)
    ·
      refine ⟨197895211098017354144983475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131930140732011569429988983 197895211098017354144983475)
      ·
        refine ⟨296842816647026031217475213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197895211098017354144983475 296842816647026031217475213)
        ·
          refine ⟨111316056242634761706553205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296842816647026031217475213 111316056242634761706553205)
          ·
            refine ⟨10435880272747008909989363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111316056242634761706553205 10435880272747008909989363)
            ·
              refine ⟨15653820409120513364984045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10435880272747008909989363 15653820409120513364984045)
              ·
                refine ⟨5870182653420192511869017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15653820409120513364984045 5870182653420192511869017)
                ·
                  refine ⟨4402636990065144383901763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5870182653420192511869017 4402636990065144383901763)
                  ·
                    refine ⟨6603955485097716575852645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4402636990065144383901763 6603955485097716575852645)
                    ·
                      refine ⟨1238241653455821857972371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6603955485097716575852645 1238241653455821857972371)
                      ·
                        rfl

theorem cell23_2411467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 4].length) (baseStart_2411467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411467 prefixEnd_2411467 := by exact prefixLift 2411467
  have htrace : WordTrace (prefixWord ++ tailWord_2411467) baseStart_2411467 baseEnd_2411467 := by
    simpa [prefixWord, tailWord_2411467, baseEnd_2411467] using wordTrace_append hprefix tailTrace_2411467
  have hstable : (prefixWord ++ tailWord_2411467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411467).length < 2 ^ (prefixWord ++ tailWord_2411467).sum := by decide
  have hdescent : baseEnd_2411467 < baseStart_2411467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411518 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_2411518 : Nat := 118140960795 + 2411518 * 2 ^ 59
def prefixEnd_2411518 : Nat := 4983230072969 + 3 ^ 40 * 2411518 * 2
def baseEnd_2411518 : Nat := 1238267840969201158434637

theorem tailTrace_2411518 : CollatzResearch.WordTrace tailWord_2411518 prefixEnd_2411518 1238267840969201158434637 := by
  unfold tailWord_2411518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10994410909686201916262401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58636858184993076886732805 10994410909686201916262401)
  ·
    refine ⟨8245808182264651437196801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10994410909686201916262401 8245808182264651437196801)
    ·
      refine ⟨6184356136698488577897601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8245808182264651437196801 6184356136698488577897601)
      ·
        refine ⟨4638267102523866433423201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6184356136698488577897601 4638267102523866433423201)
        ·
          refine ⟨3478700326892899825067401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4638267102523866433423201 3478700326892899825067401)
          ·
            refine ⟨2609025245169674868800551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3478700326892899825067401 2609025245169674868800551)
            ·
              refine ⟨3913537867754512303200827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609025245169674868800551 3913537867754512303200827)
              ·
                refine ⟨5870306801631768454801241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913537867754512303200827 5870306801631768454801241)
                ·
                  refine ⟨4402730101223826341100931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5870306801631768454801241 4402730101223826341100931)
                  ·
                    refine ⟨6604095151835739511651397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4402730101223826341100931 6604095151835739511651397)
                    ·
                      refine ⟨1238267840969201158434637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6604095151835739511651397 1238267840969201158434637)
                      ·
                        rfl

theorem cell23_2411518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_2411518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411518 prefixEnd_2411518 := by exact prefixLift 2411518
  have htrace : WordTrace (prefixWord ++ tailWord_2411518) baseStart_2411518 baseEnd_2411518 := by
    simpa [prefixWord, tailWord_2411518, baseEnd_2411518] using wordTrace_append hprefix tailTrace_2411518
  have hstable : (prefixWord ++ tailWord_2411518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411518).length < 2 ^ (prefixWord ++ tailWord_2411518).sum := by decide
  have hdescent : baseEnd_2411518 < baseStart_2411518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411521 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_2411521 : Nat := 118140960795 + 2411521 * 2 ^ 59
def prefixEnd_2411521 : Nat := 4983230072969 + 3 ^ 40 * 2411521 * 2
def baseEnd_2411521 : Nat := 1238269381411164646697123

theorem tailTrace_2411521 : CollatzResearch.WordTrace tailWord_2411521 prefixEnd_2411521 1238269381411164646697123 := by
  unfold tailWord_2411521
  simp only [CollatzResearch.WordTrace]
  refine ⟨87955396696478746842458417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58636931130985831228305611 87955396696478746842458417)
  ·
    refine ⟨65966547522359060131843813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87955396696478746842458417 65966547522359060131843813)
    ·
      refine ⟨12368727660442323774720715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65966547522359060131843813 12368727660442323774720715)
      ·
        refine ⟨18553091490663485662081073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12368727660442323774720715 18553091490663485662081073)
        ·
          refine ⟨13914818617997614246560805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18553091490663485662081073 13914818617997614246560805)
          ·
            refine ⟨2609028490874552671230151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13914818617997614246560805 2609028490874552671230151)
            ·
              refine ⟨3913542736311829006845227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609028490874552671230151 3913542736311829006845227)
              ·
                refine ⟨5870314104467743510267841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913542736311829006845227 5870314104467743510267841)
                ·
                  refine ⟨4402735578350807632700881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5870314104467743510267841 4402735578350807632700881)
                  ·
                    refine ⟨3302051683763105724525661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4402735578350807632700881 3302051683763105724525661)
                    ·
                      refine ⟨1238269381411164646697123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3302051683763105724525661 1238269381411164646697123)
                      ·
                        rfl

theorem cell23_2411521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_2411521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411521 prefixEnd_2411521 := by exact prefixLift 2411521
  have htrace : WordTrace (prefixWord ++ tailWord_2411521) baseStart_2411521 baseEnd_2411521 := by
    simpa [prefixWord, tailWord_2411521, baseEnd_2411521] using wordTrace_append hprefix tailTrace_2411521
  have hstable : (prefixWord ++ tailWord_2411521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411521).length < 2 ^ (prefixWord ++ tailWord_2411521).sum := by decide
  have hdescent : baseEnd_2411521 < baseStart_2411521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411551 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 3, 1, 3]
def baseStart_2411551 : Nat := 118140960795 + 2411551 * 2 ^ 59
def prefixEnd_2411551 : Nat := 4983230072969 + 3 ^ 40 * 2411551 * 2
def baseEnd_2411551 : Nat := 1238284785830799529321985

theorem tailTrace_2411551 : CollatzResearch.WordTrace tailWord_2411551 prefixEnd_2411551 1238284785830799529321985 := by
  unfold tailWord_2411551
  simp only [CollatzResearch.WordTrace]
  refine ⟨87956490886370061966050507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58637660590913374644033671 87956490886370061966050507)
  ·
    refine ⟨131934736329555092949075761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87956490886370061966050507 131934736329555092949075761)
    ·
      refine ⟨98951052247166319711806821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131934736329555092949075761 98951052247166319711806821)
      ·
        refine ⟨18553322296343684945963779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98951052247166319711806821 18553322296343684945963779)
        ·
          refine ⟨27829983444515527418945669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18553322296343684945963779 27829983444515527418945669)
          ·
            refine ⟨5218121895846661391052313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27829983444515527418945669 5218121895846661391052313)
            ·
              refine ⟨3913591421884996043289235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5218121895846661391052313 3913591421884996043289235)
              ·
                refine ⟨5870387132827494064933853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913591421884996043289235 5870387132827494064933853)
                ·
                  refine ⟨2201395174810310274350195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5870387132827494064933853 2201395174810310274350195)
                  ·
                    refine ⟨3302092762215465411525293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2201395174810310274350195 3302092762215465411525293)
                    ·
                      refine ⟨1238284785830799529321985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3302092762215465411525293 1238284785830799529321985)
                      ·
                        rfl

theorem cell23_2411551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_2411551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411551 prefixEnd_2411551 := by exact prefixLift 2411551
  have htrace : WordTrace (prefixWord ++ tailWord_2411551) baseStart_2411551 baseEnd_2411551 := by
    simpa [prefixWord, tailWord_2411551, baseEnd_2411551] using wordTrace_append hprefix tailTrace_2411551
  have hstable : (prefixWord ++ tailWord_2411551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411551).length < 2 ^ (prefixWord ++ tailWord_2411551).sum := by decide
  have hdescent : baseEnd_2411551 < baseStart_2411551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411587 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 4]
def baseStart_2411587 : Nat := 118140960795 + 2411587 * 2 ^ 59
def prefixEnd_2411587 : Nat := 4983230072969 + 3 ^ 40 * 2411587 * 2
def baseEnd_2411587 : Nat := 1238303271134361388471819

theorem tailTrace_2411587 : CollatzResearch.WordTrace tailWord_2411587 prefixEnd_2411587 1238303271134361388471819 := by
  unfold tailWord_2411587
  simp only [CollatzResearch.WordTrace]
  refine ⟨87957803914239640114361015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58638535942826426742907343 87957803914239640114361015)
  ·
    refine ⟨131936705871359460171541523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87957803914239640114361015 131936705871359460171541523)
    ·
      refine ⟨197905058807039190257312285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131936705871359460171541523 197905058807039190257312285)
      ·
        refine ⟨74214397052639696346492107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197905058807039190257312285 74214397052639696346492107)
        ·
          refine ⟨111321595578959544519738161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74214397052639696346492107 111321595578959544519738161)
          ·
            refine ⟨83491196684219658389803621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111321595578959544519738161 83491196684219658389803621)
            ·
              refine ⟨15654599378291185948088179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83491196684219658389803621 15654599378291185948088179)
              ·
                refine ⟨23481899067436778922132269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15654599378291185948088179 23481899067436778922132269)
                ·
                  refine ⟨8805712150288792095799601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23481899067436778922132269 8805712150288792095799601)
                  ·
                    refine ⟨6604284112716594071849701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8805712150288792095799601 6604284112716594071849701)
                    ·
                      refine ⟨1238303271134361388471819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6604284112716594071849701 1238303271134361388471819)
                      ·
                        rfl

theorem cell23_2411587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_2411587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411587 prefixEnd_2411587 := by exact prefixLift 2411587
  have htrace : WordTrace (prefixWord ++ tailWord_2411587) baseStart_2411587 baseEnd_2411587 := by
    simpa [prefixWord, tailWord_2411587, baseEnd_2411587] using wordTrace_append hprefix tailTrace_2411587
  have hstable : (prefixWord ++ tailWord_2411587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411587).length < 2 ^ (prefixWord ++ tailWord_2411587).sum := by decide
  have hdescent : baseEnd_2411587 < baseStart_2411587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411618 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2411618 : Nat := 118140960795 + 2411618 * 2 ^ 59
def prefixEnd_2411618 : Nat := 4983230072969 + 3 ^ 40 * 2411618 * 2
def baseEnd_2411618 : Nat := 412773063011550255728059

theorem tailTrace_2411618 : CollatzResearch.WordTrace tailWord_2411618 prefixEnd_2411618 412773063011550255728059 := by
  unfold tailWord_2411618
  simp only [CollatzResearch.WordTrace]
  refine ⟨21989733644281833102184877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58639289718084888272493005 21989733644281833102184877)
  ·
    refine ⟨8246150116605687413319329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21989733644281833102184877 8246150116605687413319329)
    ·
      refine ⟨6184612587454265559989497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8246150116605687413319329 6184612587454265559989497)
      ·
        refine ⟨4638459440590699169992123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6184612587454265559989497 4638459440590699169992123)
        ·
          refine ⟨6957689160886048754988185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4638459440590699169992123 6957689160886048754988185)
          ·
            refine ⟨5218266870664536566241139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6957689160886048754988185 5218266870664536566241139)
            ·
              refine ⟨7827400305996804849361709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5218266870664536566241139 7827400305996804849361709)
              ·
                refine ⟨2935275114748801818510641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7827400305996804849361709 2935275114748801818510641)
                ·
                  refine ⟨2201456336061601363882981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2935275114748801818510641 2201456336061601363882981)
                  ·
                    refine ⟨412773063011550255728059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2201456336061601363882981 412773063011550255728059)
                    ·
                      rfl

theorem cell23_2411618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2411618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411618 prefixEnd_2411618 := by exact prefixLift 2411618
  have htrace : WordTrace (prefixWord ++ tailWord_2411618) baseStart_2411618 baseEnd_2411618 := by
    simpa [prefixWord, tailWord_2411618, baseEnd_2411618] using wordTrace_append hprefix tailTrace_2411618
  have hstable : (prefixWord ++ tailWord_2411618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411618).length < 2 ^ (prefixWord ++ tailWord_2411618).sum := by decide
  have hdescent : baseEnd_2411618 < baseStart_2411618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411641 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 1, 3, 3]
def baseStart_2411641 : Nat := 118140960795 + 2411641 * 2 ^ 59
def prefixEnd_2411641 : Nat := 4983230072969 + 3 ^ 40 * 2411641 * 2
def baseEnd_2411641 : Nat := 1238330999089704177196571

theorem tailTrace_2411641 : CollatzResearch.WordTrace tailWord_2411641 prefixEnd_2411641 1238330999089704177196571 := by
  unfold tailWord_2411641
  simp only [CollatzResearch.WordTrace]
  refine ⟨87959773456044007336826777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58639848970696004891217851 87959773456044007336826777)
  ·
    refine ⟨65969830092033005502620083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87959773456044007336826777 65969830092033005502620083)
    ·
      refine ⟨98954745138049508253930125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65969830092033005502620083 98954745138049508253930125)
      ·
        refine ⟨37108029426768565595223797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98954745138049508253930125 37108029426768565595223797)
        ·
          refine ⟨3478877758759553024552231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37108029426768565595223797 3478877758759553024552231)
          ·
            refine ⟨5218316638139329536828347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478877758759553024552231 5218316638139329536828347)
            ·
              refine ⟨7827474957208994305242521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5218316638139329536828347 7827474957208994305242521)
              ·
                refine ⟨5870606217906745728931891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7827474957208994305242521 5870606217906745728931891)
                ·
                  refine ⟨8805909326860118593397837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5870606217906745728931891 8805909326860118593397837)
                  ·
                    refine ⟨3302215997572544472524189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8805909326860118593397837 3302215997572544472524189)
                    ·
                      refine ⟨1238330999089704177196571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3302215997572544472524189 1238330999089704177196571)
                      ·
                        rfl

theorem cell23_2411641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_2411641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411641 prefixEnd_2411641 := by exact prefixLift 2411641
  have htrace : WordTrace (prefixWord ++ tailWord_2411641) baseStart_2411641 baseEnd_2411641 := by
    simpa [prefixWord, tailWord_2411641, baseEnd_2411641] using wordTrace_append hprefix tailTrace_2411641
  have hstable : (prefixWord ++ tailWord_2411641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411641).length < 2 ^ (prefixWord ++ tailWord_2411641).sum := by decide
  have hdescent : baseEnd_2411641 < baseStart_2411641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411647 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 4]
def baseStart_2411647 : Nat := 118140960795 + 2411647 * 2 ^ 59
def prefixEnd_2411647 : Nat := 4983230072969 + 3 ^ 40 * 2411647 * 2
def baseEnd_2411647 : Nat := 1238334079973631153721543

theorem tailTrace_2411647 : CollatzResearch.WordTrace tailWord_2411647 prefixEnd_2411647 1238334079973631153721543 := by
  unfold tailWord_2411647
  simp only [CollatzResearch.WordTrace]
  refine ⟨87959992294022270361545195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58639994862681513574363463 87959992294022270361545195)
  ·
    refine ⟨131939988441033405542317793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87959992294022270361545195 131939988441033405542317793)
    ·
      refine ⟨98954991330775054156738345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131939988441033405542317793 98954991330775054156738345)
      ·
        refine ⟨74216243498081290617553759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98954991330775054156738345 74216243498081290617553759)
        ·
          refine ⟨111324365247121935926330639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74216243498081290617553759 111324365247121935926330639)
          ·
            refine ⟨166986547870682903889495959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111324365247121935926330639 166986547870682903889495959)
            ·
              refine ⟨250479821806024355834243939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166986547870682903889495959 250479821806024355834243939)
              ·
                refine ⟨375719732709036533751365909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250479821806024355834243939 375719732709036533751365909)
                ·
                  refine ⟨17611862470736087519595277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 375719732709036533751365909 17611862470736087519595277)
                  ·
                    refine ⟨6604448426526032819848229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17611862470736087519595277 6604448426526032819848229)
                    ·
                      refine ⟨1238334079973631153721543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6604448426526032819848229 1238334079973631153721543)
                      ·
                        rfl

theorem cell23_2411647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_2411647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411647 prefixEnd_2411647 := by exact prefixLift 2411647
  have htrace : WordTrace (prefixWord ++ tailWord_2411647) baseStart_2411647 baseEnd_2411647 := by
    simpa [prefixWord, tailWord_2411647, baseEnd_2411647] using wordTrace_append hprefix tailTrace_2411647
  have hstable : (prefixWord ++ tailWord_2411647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411647).length < 2 ^ (prefixWord ++ tailWord_2411647).sum := by decide
  have hdescent : baseEnd_2411647 < baseStart_2411647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411658 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_2411658 : Nat := 118140960795 + 2411658 * 2 ^ 59
def prefixEnd_2411658 : Nat := 4983230072969 + 3 ^ 40 * 2411658 * 2
def baseEnd_2411658 : Nat := 1238339728260830610683993

theorem tailTrace_2411658 : CollatzResearch.WordTrace tailWord_2411658 prefixEnd_2411658 1238339728260830610683993 := by
  unfold tailWord_2411658
  simp only [CollatzResearch.WordTrace]
  refine ⟨21990098374245604810048907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58640262331321612826797085 21990098374245604810048907)
  ·
    refine ⟨32985147561368407215073361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21990098374245604810048907 32985147561368407215073361)
    ·
      refine ⟨24738860671026305411305021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32985147561368407215073361 24738860671026305411305021)
      ·
        refine ⟨9277072751634864529239383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24738860671026305411305021 9277072751634864529239383)
        ·
          refine ⟨13915609127452296793859075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9277072751634864529239383 13915609127452296793859075)
          ·
            refine ⟨20873413691178445190788613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13915609127452296793859075 20873413691178445190788613)
            ·
              refine ⟨3913765067095958473272865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20873413691178445190788613 3913765067095958473272865)
              ·
                refine ⟨2935323800321968854954649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3913765067095958473272865 2935323800321968854954649)
                ·
                  refine ⟨2201492850241476641215987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2935323800321968854954649 2201492850241476641215987)
                  ·
                    refine ⟨3302239275362214961823981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2201492850241476641215987 3302239275362214961823981)
                    ·
                      refine ⟨1238339728260830610683993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3302239275362214961823981 1238339728260830610683993)
                      ·
                        rfl

theorem cell23_2411658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_2411658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411658 prefixEnd_2411658 := by exact prefixLift 2411658
  have htrace : WordTrace (prefixWord ++ tailWord_2411658) baseStart_2411658 baseEnd_2411658 := by
    simpa [prefixWord, tailWord_2411658, baseEnd_2411658] using wordTrace_append hprefix tailTrace_2411658
  have hstable : (prefixWord ++ tailWord_2411658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411658).length < 2 ^ (prefixWord ++ tailWord_2411658).sum := by decide
  have hdescent : baseEnd_2411658 < baseStart_2411658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411667 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 5]
def baseStart_2411667 : Nat := 118140960795 + 2411667 * 2 ^ 59
def prefixEnd_2411667 : Nat := 4983230072969 + 3 ^ 40 * 2411667 * 2
def baseEnd_2411667 : Nat := 1238344349586721075471451

theorem tailTrace_2411667 : CollatzResearch.WordTrace tailWord_2411667 prefixEnd_2411667 1238344349586721075471451 := by
  unfold tailWord_2411667
  simp only [CollatzResearch.WordTrace]
  refine ⟨87960721753949813777273255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58640481169299875851515503 87960721753949813777273255)
  ·
    refine ⟨131941082630924720665909883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87960721753949813777273255 131941082630924720665909883)
    ·
      refine ⟨197911623946387080998864825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131941082630924720665909883 197911623946387080998864825)
      ·
        refine ⟨148433717959790310749148619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197911623946387080998864825 148433717959790310749148619)
        ·
          refine ⟨222650576939685466123722929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148433717959790310749148619 222650576939685466123722929)
          ·
            refine ⟨166987932704764099592792197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222650576939685466123722929 166987932704764099592792197)
            ·
              refine ⟨31310237382143268673648537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 166987932704764099592792197 31310237382143268673648537)
              ·
                refine ⟨23482678036607451505236403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31310237382143268673648537 23482678036607451505236403)
                ·
                  refine ⟨35224017054911177257854605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23482678036607451505236403 35224017054911177257854605)
                  ·
                    refine ⟨13209006395591691471695477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35224017054911177257854605 13209006395591691471695477)
                    ·
                      refine ⟨1238344349586721075471451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13209006395591691471695477 1238344349586721075471451)
                      ·
                        rfl

theorem cell23_2411667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_2411667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411667 prefixEnd_2411667 := by exact prefixLift 2411667
  have htrace : WordTrace (prefixWord ++ tailWord_2411667) baseStart_2411667 baseEnd_2411667 := by
    simpa [prefixWord, tailWord_2411667, baseEnd_2411667] using wordTrace_append hprefix tailTrace_2411667
  have hstable : (prefixWord ++ tailWord_2411667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411667).length < 2 ^ (prefixWord ++ tailWord_2411667).sum := by decide
  have hdescent : baseEnd_2411667 < baseStart_2411667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411674 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_2411674 : Nat := 118140960795 + 2411674 * 2 ^ 59
def prefixEnd_2411674 : Nat := 4983230072969 + 3 ^ 40 * 2411674 * 2
def baseEnd_2411674 : Nat := 412782647983767516027973

theorem tailTrace_2411674 : CollatzResearch.WordTrace tailWord_2411674 prefixEnd_2411674 412782647983767516027973 := by
  unfold tailWord_2411674
  simp only [CollatzResearch.WordTrace]
  refine ⟨21990244266231113493194519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58640651376616302648518717 21990244266231113493194519)
  ·
    refine ⟨32985366399346670239791779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21990244266231113493194519 32985366399346670239791779)
    ·
      refine ⟨49478049599020005359687669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32985366399346670239791779 49478049599020005359687669)
      ·
        refine ⟨4638567149908125502470719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49478049599020005359687669 4638567149908125502470719)
        ·
          refine ⟨6957850724862188253706079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4638567149908125502470719 6957850724862188253706079)
          ·
            refine ⟨10436776087293282380559119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6957850724862188253706079 10436776087293282380559119)
            ·
              refine ⟨15655164130939923570838679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10436776087293282380559119 15655164130939923570838679)
              ·
                refine ⟨23482746196409885356258019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15655164130939923570838679 23482746196409885356258019)
                ·
                  refine ⟨35224119294614828034387029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23482746196409885356258019 35224119294614828034387029)
                  ·
                    refine ⟨412782647983767516027973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35224119294614828034387029 412782647983767516027973)
                    ·
                      rfl

theorem cell23_2411674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_2411674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411674 prefixEnd_2411674 := by exact prefixLift 2411674
  have htrace : WordTrace (prefixWord ++ tailWord_2411674) baseStart_2411674 baseEnd_2411674 := by
    simpa [prefixWord, tailWord_2411674, baseEnd_2411674] using wordTrace_append hprefix tailTrace_2411674
  have hstable : (prefixWord ++ tailWord_2411674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411674).length < 2 ^ (prefixWord ++ tailWord_2411674).sum := by decide
  have hdescent : baseEnd_2411674 < baseStart_2411674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411732 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_2411732 : Nat := 118140960795 + 2411732 * 2 ^ 59
def prefixEnd_2411732 : Nat := 4983230072969 + 3 ^ 40 * 2411732 * 2
def baseEnd_2411732 : Nat := 1238377725829263321158653

theorem tailTrace_2411732 : CollatzResearch.WordTrace tailWord_2411732 prefixEnd_2411732 1238377725829263321158653 := by
  unfold tailWord_2411732
  simp only [CollatzResearch.WordTrace]
  refine ⟨43981546249357164939194725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58642061665809553252259633 43981546249357164939194725)
  ·
    refine ⟨8246539921754468426099011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43981546249357164939194725 8246539921754468426099011)
    ·
      refine ⟨12369809882631702639148517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8246539921754468426099011 12369809882631702639148517)
      ·
        refine ⟨2319339352993444244840347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12369809882631702639148517 2319339352993444244840347)
        ·
          refine ⟨3479009029490166367260521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2319339352993444244840347 3479009029490166367260521)
          ·
            refine ⟨2609256772117624775445391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3479009029490166367260521 2609256772117624775445391)
            ·
              refine ⟨3913885158176437163168087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609256772117624775445391 3913885158176437163168087)
              ·
                refine ⟨5870827737264655744752131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913885158176437163168087 5870827737264655744752131)
                ·
                  refine ⟨8806241605896983617128197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5870827737264655744752131 8806241605896983617128197)
                  ·
                    refine ⟨1651170301105684428211537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8806241605896983617128197 1651170301105684428211537)
                    ·
                      refine ⟨1238377725829263321158653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651170301105684428211537 1238377725829263321158653)
                      ·
                        rfl

theorem cell23_2411732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_2411732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411732 prefixEnd_2411732 := by exact prefixLift 2411732
  have htrace : WordTrace (prefixWord ++ tailWord_2411732) baseStart_2411732 baseEnd_2411732 := by
    simpa [prefixWord, tailWord_2411732, baseEnd_2411732] using wordTrace_append hprefix tailTrace_2411732
  have hstable : (prefixWord ++ tailWord_2411732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411732).length < 2 ^ (prefixWord ++ tailWord_2411732).sum := by decide
  have hdescent : baseEnd_2411732 < baseStart_2411732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411778 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_2411778 : Nat := 118140960795 + 2411778 * 2 ^ 59
def prefixEnd_2411778 : Nat := 4983230072969 + 3 ^ 40 * 2411778 * 2
def baseEnd_2411778 : Nat := 1238401345939370141183441

theorem tailTrace_2411778 : CollatzResearch.WordTrace tailWord_2411778 prefixEnd_2411778 1238401345939370141183441 := by
  unfold tailWord_2411778
  simp only [CollatzResearch.WordTrace]
  refine ⟨21991192564136919933640997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58643180171031786489709325 21991192564136919933640997)
  ·
    refine ⟨4123348605775672487557687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21991192564136919933640997 4123348605775672487557687)
    ·
      refine ⟨6185022908663508731336531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4123348605775672487557687 6185022908663508731336531)
      ·
        refine ⟨9277534362995263097004797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6185022908663508731336531 9277534362995263097004797)
        ·
          refine ⟨3479075386123223661376799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9277534362995263097004797 3479075386123223661376799)
          ·
            refine ⟨5218613079184835492065199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3479075386123223661376799 5218613079184835492065199)
            ·
              refine ⟨7827919618777253238097799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5218613079184835492065199 7827919618777253238097799)
              ·
                refine ⟨11741879428165879857146699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7827919618777253238097799 11741879428165879857146699)
                ·
                  refine ⟨17612819142248819785720049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11741879428165879857146699 17612819142248819785720049)
                  ·
                    refine ⟨13209614356686614839290037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17612819142248819785720049 13209614356686614839290037)
                    ·
                      refine ⟨1238401345939370141183441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13209614356686614839290037 1238401345939370141183441)
                      ·
                        rfl

theorem cell23_2411778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_2411778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411778 prefixEnd_2411778 := by exact prefixLift 2411778
  have htrace : WordTrace (prefixWord ++ tailWord_2411778) baseStart_2411778 baseEnd_2411778 := by
    simpa [prefixWord, tailWord_2411778, baseEnd_2411778] using wordTrace_append hprefix tailTrace_2411778
  have hstable : (prefixWord ++ tailWord_2411778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411778).length < 2 ^ (prefixWord ++ tailWord_2411778).sum := by decide
  have hdescent : baseEnd_2411778 < baseStart_2411778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411828 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2411828 : Nat := 118140960795 + 2411828 * 2 ^ 59
def prefixEnd_2411828 : Nat := 4983230072969 + 3 ^ 40 * 2411828 * 2
def baseEnd_2411828 : Nat := 137603002219121660617579

theorem tailTrace_2411828 : CollatzResearch.WordTrace tailWord_2411828 prefixEnd_2411828 137603002219121660617579 := by
  unfold tailWord_2411828
  simp only [CollatzResearch.WordTrace]
  refine ⟨43983296953183269136942069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58644395937577692182589425 43983296953183269136942069)
  ·
    refine ⟨4123434089360931481588319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43983296953183269136942069 4123434089360931481588319)
    ·
      refine ⟨6185151134041397222382479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4123434089360931481588319 6185151134041397222382479)
      ·
        refine ⟨9277726701062095833573719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6185151134041397222382479 9277726701062095833573719)
        ·
          refine ⟨13916590051593143750360579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9277726701062095833573719 13916590051593143750360579)
          ·
            refine ⟨20874885077389715625540869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13916590051593143750360579 20874885077389715625540869)
            ·
              refine ⟨3914040952010571679788913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20874885077389715625540869 3914040952010571679788913)
              ·
                refine ⟨2935530714007928759841685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3914040952010571679788913 2935530714007928759841685)
                ·
                  refine ⟨137603002219121660617579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2935530714007928759841685 137603002219121660617579)
                  ·
                    rfl

theorem cell23_2411828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2411828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411828 prefixEnd_2411828 := by exact prefixLift 2411828
  have htrace : WordTrace (prefixWord ++ tailWord_2411828) baseStart_2411828 baseEnd_2411828 := by
    simpa [prefixWord, tailWord_2411828, baseEnd_2411828] using wordTrace_append hprefix tailTrace_2411828
  have hstable : (prefixWord ++ tailWord_2411828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411828).length < 2 ^ (prefixWord ++ tailWord_2411828).sum := by decide
  have hdescent : baseEnd_2411828 < baseStart_2411828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411831 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 5, 5, 2]
def baseStart_2411831 : Nat := 118140960795 + 2411831 * 2 ^ 59
def prefixEnd_2411831 : Nat := 4983230072969 + 3 ^ 40 * 2411831 * 2
def baseEnd_2411831 : Nat := 1238428560414058433820697

theorem tailTrace_2411831 : CollatzResearch.WordTrace tailWord_2411831 prefixEnd_2411831 1238428560414058433820697 := by
  unfold tailWord_2411831
  simp only [CollatzResearch.WordTrace]
  refine ⟨87966703325355669786243347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58644468883570446524162231 87966703325355669786243347)
  ·
    refine ⟨131950054988033504679365021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87966703325355669786243347 131950054988033504679365021)
    ·
      refine ⟨49481270620512564254761883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131950054988033504679365021 49481270620512564254761883)
      ·
        refine ⟨74221905930768846382142825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49481270620512564254761883 74221905930768846382142825)
        ·
          refine ⟨55666429448076634786607119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74221905930768846382142825 55666429448076634786607119)
          ·
            refine ⟨83499644172114952179910679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55666429448076634786607119 83499644172114952179910679)
            ·
              refine ⟨125249466258172428269866019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83499644172114952179910679 125249466258172428269866019)
              ·
                refine ⟨187874199387258642404799029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125249466258172428269866019 187874199387258642404799029)
                ·
                  refine ⟨17613206192555497725449909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187874199387258642404799029 17613206192555497725449909)
                  ·
                    refine ⟨1651238080552077911760929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17613206192555497725449909 1651238080552077911760929)
                    ·
                      refine ⟨1238428560414058433820697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651238080552077911760929 1238428560414058433820697)
                      ·
                        rfl

theorem cell23_2411831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 5, 2].length) (baseStart_2411831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411831 prefixEnd_2411831 := by exact prefixLift 2411831
  have htrace : WordTrace (prefixWord ++ tailWord_2411831) baseStart_2411831 baseEnd_2411831 := by
    simpa [prefixWord, tailWord_2411831, baseEnd_2411831] using wordTrace_append hprefix tailTrace_2411831
  have hstable : (prefixWord ++ tailWord_2411831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411831).length < 2 ^ (prefixWord ++ tailWord_2411831).sum := by decide
  have hdescent : baseEnd_2411831 < baseStart_2411831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411871 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 4, 4]
def baseStart_2411871 : Nat := 118140960795 + 2411871 * 2 ^ 59
def prefixEnd_2411871 : Nat := 4983230072969 + 3 ^ 40 * 2411871 * 2
def baseEnd_2411871 : Nat := 412816366546746092440171

theorem tailTrace_2411871 : CollatzResearch.WordTrace tailWord_2411871 prefixEnd_2411871 412816366546746092440171 := by
  unfold tailWord_2411871
  simp only [CollatzResearch.WordTrace]
  refine ⟨87968162245210756617699467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58645441496807171078466311 87968162245210756617699467)
  ·
    refine ⟨131952243367816134926549201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87968162245210756617699467 131952243367816134926549201)
    ·
      refine ⟨98964182525862101194911901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131952243367816134926549201 98964182525862101194911901)
      ·
        refine ⟨37111568447198287948091963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98964182525862101194911901 37111568447198287948091963)
        ·
          refine ⟨55667352670797431922137945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37111568447198287948091963 55667352670797431922137945)
          ·
            refine ⟨41750514503098073941603459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55667352670797431922137945 41750514503098073941603459)
            ·
              refine ⟨62625771754647110912405189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41750514503098073941603459 62625771754647110912405189)
              ·
                refine ⟨11742332203996333296075973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62625771754647110912405189 11742332203996333296075973)
                ·
                  refine ⟨2201687288249312493014245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11742332203996333296075973 2201687288249312493014245)
                  ·
                    refine ⟨412816366546746092440171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2201687288249312493014245 412816366546746092440171)
                    ·
                      rfl

theorem cell23_2411871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 4].length) (baseStart_2411871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411871 prefixEnd_2411871 := by exact prefixLift 2411871
  have htrace : WordTrace (prefixWord ++ tailWord_2411871) baseStart_2411871 baseEnd_2411871 := by
    simpa [prefixWord, tailWord_2411871, baseEnd_2411871] using wordTrace_append hprefix tailTrace_2411871
  have hstable : (prefixWord ++ tailWord_2411871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411871).length < 2 ^ (prefixWord ++ tailWord_2411871).sum := by decide
  have hdescent : baseEnd_2411871 < baseStart_2411871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411872 : List Nat := [2, 1, 1, 3, 4, 2, 2, 3, 1, 1, 3]
def baseStart_2411872 : Nat := 118140960795 + 2411872 * 2 ^ 59
def prefixEnd_2411872 : Nat := 4983230072969 + 3 ^ 40 * 2411872 * 2
def baseEnd_2411872 : Nat := 1238449613120892773408009

theorem tailTrace_2411872 : CollatzResearch.WordTrace tailWord_2411872 prefixEnd_2411872 1238449613120892773408009 := by
  unfold tailWord_2411872
  simp only [CollatzResearch.WordTrace]
  refine ⟨43984099359103566894242935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58645465812138089192323913 43984099359103566894242935)
  ·
    refine ⟨65976149038655350341364403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43984099359103566894242935 65976149038655350341364403)
    ·
      refine ⟨98964223557983025512046605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65976149038655350341364403 98964223557983025512046605)
      ·
        refine ⟨37111583834243634567017477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98964223557983025512046605 37111583834243634567017477)
        ·
          refine ⟨6958421968920681481315777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37111583834243634567017477 6958421968920681481315777)
          ·
            refine ⟨5218816476690511110986833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6958421968920681481315777 5218816476690511110986833)
            ·
              refine ⟨3914112357517883333240125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5218816476690511110986833 3914112357517883333240125)
              ·
                refine ⟨1467792134069206249965047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3914112357517883333240125 1467792134069206249965047)
                ·
                  refine ⟨2201688201103809374947571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467792134069206249965047 2201688201103809374947571)
                  ·
                    refine ⟨3302532301655714062421357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2201688201103809374947571 3302532301655714062421357)
                    ·
                      refine ⟨1238449613120892773408009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3302532301655714062421357 1238449613120892773408009)
                      ·
                        rfl

theorem cell23_2411872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_2411872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411872 prefixEnd_2411872 := by exact prefixLift 2411872
  have htrace : WordTrace (prefixWord ++ tailWord_2411872) baseStart_2411872 baseEnd_2411872 := by
    simpa [prefixWord, tailWord_2411872, baseEnd_2411872] using wordTrace_append hprefix tailTrace_2411872
  have hstable : (prefixWord ++ tailWord_2411872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411872).length < 2 ^ (prefixWord ++ tailWord_2411872).sum := by decide
  have hdescent : baseEnd_2411872 < baseStart_2411872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411875 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 1, 5]
def baseStart_2411875 : Nat := 118140960795 + 2411875 * 2 ^ 59
def prefixEnd_2411875 : Nat := 4983230072969 + 3 ^ 40 * 2411875 * 2
def baseEnd_2411875 : Nat := 412817051187618753890165

theorem tailTrace_2411875 : CollatzResearch.WordTrace tailWord_2411875 prefixEnd_2411875 412817051187618753890165 := by
  unfold tailWord_2411875
  simp only [CollatzResearch.WordTrace]
  refine ⟨87968308137196265300845079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58645538758130843533896719 87968308137196265300845079)
  ·
    refine ⟨131952462205794397951267619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87968308137196265300845079 131952462205794397951267619)
    ·
      refine ⟨197928693308691596926901429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131952462205794397951267619 197928693308691596926901429)
      ·
        refine ⟨18555814997689837211897009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 197928693308691596926901429 18555814997689837211897009)
        ·
          refine ⟨13916861248267377908922757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18555814997689837211897009 13916861248267377908922757)
          ·
            refine ⟨2609411484050133357923017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13916861248267377908922757 2609411484050133357923017)
            ·
              refine ⟨1957058613037600018442263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2609411484050133357923017 1957058613037600018442263)
              ·
                refine ⟨2935587919556400027663395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957058613037600018442263 2935587919556400027663395)
                ·
                  refine ⟨4403381879334600041495093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2935587919556400027663395 4403381879334600041495093)
                  ·
                    refine ⟨412817051187618753890165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4403381879334600041495093 412817051187618753890165)
                    ·
                      rfl

theorem cell23_2411875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 5].length) (baseStart_2411875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411875 prefixEnd_2411875 := by exact prefixLift 2411875
  have htrace : WordTrace (prefixWord ++ tailWord_2411875) baseStart_2411875 baseEnd_2411875 := by
    simpa [prefixWord, tailWord_2411875, baseEnd_2411875] using wordTrace_append hprefix tailTrace_2411875
  have hstable : (prefixWord ++ tailWord_2411875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411875).length < 2 ^ (prefixWord ++ tailWord_2411875).sum := by decide
  have hdescent : baseEnd_2411875 < baseStart_2411875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411881 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 5, 2, 3]
def baseStart_2411881 : Nat := 118140960795 + 2411881 * 2 ^ 59
def prefixEnd_2411881 : Nat := 4983230072969 + 3 ^ 40 * 2411881 * 2
def baseEnd_2411881 : Nat := 1238454234446783238195467

theorem tailTrace_2411881 : CollatzResearch.WordTrace tailWord_2411881 prefixEnd_2411881 1238454234446783238195467 := by
  unfold tailWord_2411881
  simp only [CollatzResearch.WordTrace]
  refine ⟨87968526975174528325563497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58645684650116352217042331 87968526975174528325563497)
  ·
    refine ⟨65976395231380896244172623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87968526975174528325563497 65976395231380896244172623)
    ·
      refine ⟨98964592847071344366258935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65976395231380896244172623 98964592847071344366258935)
      ·
        refine ⟨148446889270607016549388403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98964592847071344366258935 148446889270607016549388403)
        ·
          refine ⟨222670333905910524824082605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148446889270607016549388403 222670333905910524824082605)
          ·
            refine ⟨83501375214716446809030977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 222670333905910524824082605 83501375214716446809030977)
            ·
              refine ⟨62626031411037335106773233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83501375214716446809030977 62626031411037335106773233)
              ·
                refine ⟨46969523558278001330079925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62626031411037335106773233 46969523558278001330079925)
                ·
                  refine ⟨4403392833588562624694993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46969523558278001330079925 4403392833588562624694993)
                  ·
                    refine ⟨3302544625191421968521245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4403392833588562624694993 3302544625191421968521245)
                    ·
                      refine ⟨1238454234446783238195467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3302544625191421968521245 1238454234446783238195467)
                      ·
                        rfl

theorem cell23_2411881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 2, 3].length) (baseStart_2411881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411881 prefixEnd_2411881 := by exact prefixLift 2411881
  have htrace : WordTrace (prefixWord ++ tailWord_2411881) baseStart_2411881 baseEnd_2411881 := by
    simpa [prefixWord, tailWord_2411881, baseEnd_2411881] using wordTrace_append hprefix tailTrace_2411881
  have hstable : (prefixWord ++ tailWord_2411881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411881).length < 2 ^ (prefixWord ++ tailWord_2411881).sum := by decide
  have hdescent : baseEnd_2411881 < baseStart_2411881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411895 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 3, 2, 2]
def baseStart_2411895 : Nat := 118140960795 + 2411895 * 2 ^ 59
def prefixEnd_2411895 : Nat := 4983230072969 + 3 ^ 40 * 2411895 * 2
def baseEnd_2411895 : Nat := 1238461423175946183420403

theorem tailTrace_2411895 : CollatzResearch.WordTrace tailWord_2411895 prefixEnd_2411895 1238461423175946183420403 := by
  unfold tailWord_2411895
  simp only [CollatzResearch.WordTrace]
  refine ⟨87969037597123808716573139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58646025064749205811048759 87969037597123808716573139)
  ·
    refine ⟨131953556395685713074859709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87969037597123808716573139 131953556395685713074859709)
    ·
      refine ⟨49482583648382142403072391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131953556395685713074859709 49482583648382142403072391)
      ·
        refine ⟨74223875472573213604608587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49482583648382142403072391 74223875472573213604608587)
        ·
          refine ⟨111335813208859820406912881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74223875472573213604608587 111335813208859820406912881)
          ·
            refine ⟨83501859906644865305184661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111335813208859820406912881 83501859906644865305184661)
            ·
              refine ⟨3914149683123978061180531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83501859906644865305184661 3914149683123978061180531)
              ·
                refine ⟨5871224524685967091770797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3914149683123978061180531 5871224524685967091770797)
                ·
                  refine ⟨2201709196757237659414049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5871224524685967091770797 2201709196757237659414049)
                  ·
                    refine ⟨1651281897567928244560537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2201709196757237659414049 1651281897567928244560537)
                    ·
                      refine ⟨1238461423175946183420403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651281897567928244560537 1238461423175946183420403)
                      ·
                        rfl

theorem cell23_2411895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 2, 2].length) (baseStart_2411895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411895 prefixEnd_2411895 := by exact prefixLift 2411895
  have htrace : WordTrace (prefixWord ++ tailWord_2411895) baseStart_2411895 baseEnd_2411895 := by
    simpa [prefixWord, tailWord_2411895, baseEnd_2411895] using wordTrace_append hprefix tailTrace_2411895
  have hstable : (prefixWord ++ tailWord_2411895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411895).length < 2 ^ (prefixWord ++ tailWord_2411895).sum := by decide
  have hdescent : baseEnd_2411895 < baseStart_2411895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411905 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 1, 6]
def baseStart_2411905 : Nat := 118140960795 + 2411905 * 2 ^ 59
def prefixEnd_2411905 : Nat := 4983230072969 + 3 ^ 40 * 2411905 * 2
def baseEnd_2411905 : Nat := 412822185994163714765119

theorem tailTrace_2411905 : CollatzResearch.WordTrace tailWord_2411905 prefixEnd_2411905 412822185994163714765119 := by
  unfold tailWord_2411905
  simp only [CollatzResearch.WordTrace]
  refine ⟨87969402327087580424437169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58646268218058386949624779 87969402327087580424437169)
  ·
    refine ⟨65977051745315685318327877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87969402327087580424437169 65977051745315685318327877)
    ·
      refine ⟨12370697202246690997186477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65977051745315685318327877 12370697202246690997186477)
      ·
        refine ⟨4639011450842509123944929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12370697202246690997186477 4639011450842509123944929)
        ·
          refine ⟨3479258588131881842958697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4639011450842509123944929 3479258588131881842958697)
          ·
            refine ⟨2609443941098911382219023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3479258588131881842958697 2609443941098911382219023)
            ·
              refine ⟨3914165911648367073328535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609443941098911382219023 3914165911648367073328535)
              ·
                refine ⟨5871248867472550609992803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3914165911648367073328535 5871248867472550609992803)
                ·
                  refine ⟨8806873301208825914989205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5871248867472550609992803 8806873301208825914989205)
                  ·
                    refine ⟨412822185994163714765119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8806873301208825914989205 412822185994163714765119)
                    ·
                      rfl

theorem cell23_2411905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_2411905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411905 prefixEnd_2411905 := by exact prefixLift 2411905
  have htrace : WordTrace (prefixWord ++ tailWord_2411905) baseStart_2411905 baseEnd_2411905 := by
    simpa [prefixWord, tailWord_2411905, baseEnd_2411905] using wordTrace_append hprefix tailTrace_2411905
  have hstable : (prefixWord ++ tailWord_2411905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411905).length < 2 ^ (prefixWord ++ tailWord_2411905).sum := by decide
  have hdescent : baseEnd_2411905 < baseStart_2411905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411908 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_2411908 : Nat := 118140960795 + 2411908 * 2 ^ 59
def prefixEnd_2411908 : Nat := 4983230072969 + 3 ^ 40 * 2411908 * 2
def baseEnd_2411908 : Nat := 1238468098424454632557843

theorem tailTrace_2411908 : CollatzResearch.WordTrace tailWord_2411908 prefixEnd_2411908 1238468098424454632557843 := by
  unfold tailWord_2411908
  simp only [CollatzResearch.WordTrace]
  refine ⟨43984755873038355968398189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58646341164051141291197585 43984755873038355968398189)
  ·
    refine ⟨16494283452389383488149321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43984755873038355968398189 16494283452389383488149321)
    ·
      refine ⟨12370712589292037616111991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16494283452389383488149321 12370712589292037616111991)
      ·
        refine ⟨18556068883938056424167987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12370712589292037616111991 18556068883938056424167987)
        ·
          refine ⟨27834103325907084636251981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18556068883938056424167987 27834103325907084636251981)
          ·
            refine ⟨10437788747215156738594493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27834103325907084636251981 10437788747215156738594493)
            ·
              refine ⟨3914170780205683776972935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10437788747215156738594493 3914170780205683776972935)
              ·
                refine ⟨5871256170308525665459403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3914170780205683776972935 5871256170308525665459403)
                ·
                  refine ⟨8806884255462788498189105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5871256170308525665459403 8806884255462788498189105)
                  ·
                    refine ⟨6605163191597091373641829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8806884255462788498189105 6605163191597091373641829)
                    ·
                      refine ⟨1238468098424454632557843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6605163191597091373641829 1238468098424454632557843)
                      ·
                        rfl

theorem cell23_2411908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_2411908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411908 prefixEnd_2411908 := by exact prefixLift 2411908
  have htrace : WordTrace (prefixWord ++ tailWord_2411908) baseStart_2411908 baseEnd_2411908 := by
    simpa [prefixWord, tailWord_2411908, baseEnd_2411908] using wordTrace_append hprefix tailTrace_2411908
  have hstable : (prefixWord ++ tailWord_2411908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411908).length < 2 ^ (prefixWord ++ tailWord_2411908).sum := by decide
  have hdescent : baseEnd_2411908 < baseStart_2411908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411918 : List Nat := [4, 1, 1, 4, 2, 1, 1, 9]
def baseStart_2411918 : Nat := 118140960795 + 2411918 * 2 ^ 59
def prefixEnd_2411918 : Nat := 4983230072969 + 3 ^ 40 * 2411918 * 2
def baseEnd_2411918 : Nat := 45869379008555540497511

theorem tailTrace_2411918 : CollatzResearch.WordTrace tailWord_2411918 prefixEnd_2411918 45869379008555540497511 := by
  unfold tailWord_2411918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10996234559505060455582551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58646584317360322429773605 10996234559505060455582551)
  ·
    refine ⟨16494351839257590683373827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10996234559505060455582551 16494351839257590683373827)
    ·
      refine ⟨24741527758886386025060741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16494351839257590683373827 24741527758886386025060741)
      ·
        refine ⟨4639036454791197379698889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24741527758886386025060741 4639036454791197379698889)
        ·
          refine ⟨3479277341093398034774167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4639036454791197379698889 3479277341093398034774167)
          ·
            refine ⟨5218916011640097052161251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3479277341093398034774167 5218916011640097052161251)
            ·
              refine ⟨7828374017460145578241877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5218916011640097052161251 7828374017460145578241877)
              ·
                refine ⟨45869379008555540497511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7828374017460145578241877 45869379008555540497511)
                ·
                  rfl

theorem cell23_2411918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_2411918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411918 prefixEnd_2411918 := by exact prefixLift 2411918
  have htrace : WordTrace (prefixWord ++ tailWord_2411918) baseStart_2411918 baseEnd_2411918 := by
    simpa [prefixWord, tailWord_2411918, baseEnd_2411918] using wordTrace_append hprefix tailTrace_2411918
  have hstable : (prefixWord ++ tailWord_2411918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411918).length < 2 ^ (prefixWord ++ tailWord_2411918).sum := by decide
  have hdescent : baseEnd_2411918 < baseStart_2411918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411929 : List Nat := [1, 2, 1, 2, 1, 7, 1, 3, 1, 2, 2]
def baseStart_2411929 : Nat := 118140960795 + 2411929 * 2 ^ 59
def prefixEnd_2411929 : Nat := 4983230072969 + 3 ^ 40 * 2411929 * 2
def baseEnd_2411929 : Nat := 1238478881518199050395247

theorem tailTrace_2411929 : CollatzResearch.WordTrace tailWord_2411929 prefixEnd_2411929 1238478881518199050395247 := by
  unfold tailWord_2411929
  simp only [CollatzResearch.WordTrace]
  refine ⟨87970277679000632523310841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58646851786000421682207227 87970277679000632523310841)
  ·
    refine ⟨65977708259250474392483131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87970277679000632523310841 65977708259250474392483131)
    ·
      refine ⟨98966562388875711588724697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65977708259250474392483131 98966562388875711588724697)
      ·
        refine ⟨74224921791656783691543523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98966562388875711588724697 74224921791656783691543523)
        ·
          refine ⟨111337382687485175537315285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74224921791656783691543523 111337382687485175537315285)
          ·
            refine ⟨2609469906737933801655827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 111337382687485175537315285 2609469906737933801655827)
            ·
              refine ⟨3914204860106900702483741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609469906737933801655827 3914204860106900702483741)
              ·
                refine ⟨1467826822540087763431403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3914204860106900702483741 1467826822540087763431403)
                ·
                  refine ⟨2201740233810131645147105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467826822540087763431403 2201740233810131645147105)
                  ·
                    refine ⟨1651305175357598733860329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2201740233810131645147105 1651305175357598733860329)
                    ·
                      refine ⟨1238478881518199050395247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651305175357598733860329 1238478881518199050395247)
                      ·
                        rfl

theorem cell23_2411929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 1, 2, 2].length) (baseStart_2411929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411929 prefixEnd_2411929 := by exact prefixLift 2411929
  have htrace : WordTrace (prefixWord ++ tailWord_2411929) baseStart_2411929 baseEnd_2411929 := by
    simpa [prefixWord, tailWord_2411929, baseEnd_2411929] using wordTrace_append hprefix tailTrace_2411929
  have hstable : (prefixWord ++ tailWord_2411929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411929).length < 2 ^ (prefixWord ++ tailWord_2411929).sum := by decide
  have hdescent : baseEnd_2411929 < baseStart_2411929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411971 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 5]
def baseStart_2411971 : Nat := 118140960795 + 2411971 * 2 ^ 59
def prefixEnd_2411971 : Nat := 4983230072969 + 3 ^ 40 * 2411971 * 2
def baseEnd_2411971 : Nat := 1238500447705687886070053

theorem tailTrace_2411971 : CollatzResearch.WordTrace tailWord_2411971 prefixEnd_2411971 1238500447705687886070053 := by
  unfold tailWord_2411971
  simp only [CollatzResearch.WordTrace]
  refine ⟨87971809544848473696339767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58647873029898982464226511 87971809544848473696339767)
  ·
    refine ⟨131957714317272710544509651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87971809544848473696339767 131957714317272710544509651)
    ·
      refine ⟨197936571475909065816764477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131957714317272710544509651 197936571475909065816764477)
      ·
        refine ⟨74226214303465899681286679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197936571475909065816764477 74226214303465899681286679)
        ·
          refine ⟨111339321455198849521930019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74226214303465899681286679 111339321455198849521930019)
          ·
            refine ⟨167008982182798274282895029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111339321455198849521930019 167008982182798274282895029)
            ·
              refine ⟨15657092079637338214021409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167008982182798274282895029 15657092079637338214021409)
              ·
                refine ⟨11742819059728003660516057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15657092079637338214021409 11742819059728003660516057)
                ·
                  refine ⟨8807114294796002745387043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11742819059728003660516057 8807114294796002745387043)
                  ·
                    refine ⟨13210671442194004118080565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8807114294796002745387043 13210671442194004118080565)
                    ·
                      refine ⟨1238500447705687886070053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13210671442194004118080565 1238500447705687886070053)
                      ·
                        rfl

theorem cell23_2411971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_2411971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411971 prefixEnd_2411971 := by exact prefixLift 2411971
  have htrace : WordTrace (prefixWord ++ tailWord_2411971) baseStart_2411971 baseEnd_2411971 := by
    simpa [prefixWord, tailWord_2411971, baseEnd_2411971] using wordTrace_append hprefix tailTrace_2411971
  have hstable : (prefixWord ++ tailWord_2411971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411971).length < 2 ^ (prefixWord ++ tailWord_2411971).sum := by decide
  have hdescent : baseEnd_2411971 < baseStart_2411971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2411972 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_2411972 : Nat := 118140960795 + 2411972 * 2 ^ 59
def prefixEnd_2411972 : Nat := 4983230072969 + 3 ^ 40 * 2411972 * 2
def baseEnd_2411972 : Nat := 1238500961186342382157549

theorem tailTrace_2411972 : CollatzResearch.WordTrace tailWord_2411972 prefixEnd_2411972 1238500961186342382157549 := by
  unfold tailWord_2411972
  simp only [CollatzResearch.WordTrace]
  refine ⟨43985923008922425433563085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58647897345229900578084113 43985923008922425433563085)
  ·
    refine ⟨16494721128345909537586157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43985923008922425433563085 16494721128345909537586157)
    ·
      refine ⟨6185520423129716076594809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16494721128345909537586157 6185520423129716076594809)
      ·
        refine ⟨4639140317347287057446107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6185520423129716076594809 4639140317347287057446107)
        ·
          refine ⟨6958710476020930586169161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4639140317347287057446107 6958710476020930586169161)
          ·
            refine ⟨5219032857015697939626871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6958710476020930586169161 5219032857015697939626871)
            ·
              refine ⟨7828549285523546909440307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5219032857015697939626871 7828549285523546909440307)
              ·
                refine ⟨11742823928285320364160461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7828549285523546909440307 11742823928285320364160461)
                ·
                  refine ⟨4403558973106995136560173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11742823928285320364160461 4403558973106995136560173)
                  ·
                    refine ⟨1651334614915123176210065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4403558973106995136560173 1651334614915123176210065)
                    ·
                      refine ⟨1238500961186342382157549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651334614915123176210065 1238500961186342382157549)
                      ·
                        rfl

theorem cell23_2411972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_2411972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2411972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2411972 prefixEnd_2411972 := by exact prefixLift 2411972
  have htrace : WordTrace (prefixWord ++ tailWord_2411972) baseStart_2411972 baseEnd_2411972 := by
    simpa [prefixWord, tailWord_2411972, baseEnd_2411972] using wordTrace_append hprefix tailTrace_2411972
  have hstable : (prefixWord ++ tailWord_2411972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2411972).length < 2 ^ (prefixWord ++ tailWord_2411972).sum := by decide
  have hdescent : baseEnd_2411972 < baseStart_2411972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2411972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412031 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 5]
def baseStart_2412031 : Nat := 118140960795 + 2412031 * 2 ^ 59
def prefixEnd_2412031 : Nat := 4983230072969 + 3 ^ 40 * 2412031 * 2
def baseEnd_2412031 : Nat := 1238531256544957651319777

theorem tailTrace_2412031 : CollatzResearch.WordTrace tailWord_2412031 prefixEnd_2412031 1238531256544957651319777 := by
  unfold tailWord_2412031
  simp only [CollatzResearch.WordTrace]
  refine ⟨87973997924631103943523947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58649331949754069295682631 87973997924631103943523947)
  ·
    refine ⟨131960996886946655915285921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87973997924631103943523947 131960996886946655915285921)
    ·
      refine ⟨98970747665209991936464441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131960996886946655915285921 98970747665209991936464441)
      ·
        refine ⟨74228060748907493952348331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98970747665209991936464441 74228060748907493952348331)
        ·
          refine ⟨111342091123361240928522497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74228060748907493952348331 111342091123361240928522497)
          ·
            refine ⟨83506568342520930696391873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111342091123361240928522497 83506568342520930696391873)
            ·
              refine ⟨62629926256890698022293905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83506568342520930696391873 62629926256890698022293905)
              ·
                refine ⟨46972444692668023516720429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62629926256890698022293905 46972444692668023516720429)
                ·
                  refine ⟨17614666759750508818770161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46972444692668023516720429 17614666759750508818770161)
                  ·
                    refine ⟨13211000069812881614077621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17614666759750508818770161 13211000069812881614077621)
                    ·
                      refine ⟨1238531256544957651319777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13211000069812881614077621 1238531256544957651319777)
                      ·
                        rfl

theorem cell23_2412031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_2412031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412031 prefixEnd_2412031 := by exact prefixLift 2412031
  have htrace : WordTrace (prefixWord ++ tailWord_2412031) baseStart_2412031 baseEnd_2412031 := by
    simpa [prefixWord, tailWord_2412031, baseEnd_2412031] using wordTrace_append hprefix tailTrace_2412031
  have hstable : (prefixWord ++ tailWord_2412031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412031).length < 2 ^ (prefixWord ++ tailWord_2412031).sum := by decide
  have hdescent : baseEnd_2412031 < baseStart_2412031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412058 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_2412058 : Nat := 118140960795 + 2412058 * 2 ^ 59
def prefixEnd_2412058 : Nat := 4983230072969 + 3 ^ 40 * 2412058 * 2
def baseEnd_2412058 : Nat := 1238545120522629045682153

theorem tailTrace_2412058 : CollatzResearch.WordTrace tailWord_2412058 prefixEnd_2412058 1238545120522629045682153 := by
  unfold tailWord_2412058
  simp only [CollatzResearch.WordTrace]
  refine ⟨21993745673883321888689207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58649988463688858369837885 21993745673883321888689207)
  ·
    refine ⟨32990618510824982833033811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21993745673883321888689207 32990618510824982833033811)
    ·
      refine ⟨49485927766237474249550717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32990618510824982833033811 49485927766237474249550717)
      ·
        refine ⟨18557222912339052843581519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49485927766237474249550717 18557222912339052843581519)
        ·
          refine ⟨27835834368508579265372279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18557222912339052843581519 27835834368508579265372279)
          ·
            refine ⟨41753751552762868898058419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27835834368508579265372279 41753751552762868898058419)
            ·
              refine ⟨62630627329144303347087629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41753751552762868898058419 62630627329144303347087629)
              ·
                refine ⟨23486485248429113755157861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62630627329144303347087629 23486485248429113755157861)
                ·
                  refine ⟨4403715984080458829092099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23486485248429113755157861 4403715984080458829092099)
                  ·
                    refine ⟨6605573976120688243638149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4403715984080458829092099 6605573976120688243638149)
                    ·
                      refine ⟨1238545120522629045682153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6605573976120688243638149 1238545120522629045682153)
                      ·
                        rfl

theorem cell23_2412058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_2412058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412058 prefixEnd_2412058 := by exact prefixLift 2412058
  have htrace : WordTrace (prefixWord ++ tailWord_2412058) baseStart_2412058 baseEnd_2412058 := by
    simpa [prefixWord, tailWord_2412058, baseEnd_2412058] using wordTrace_append hprefix tailTrace_2412058
  have hstable : (prefixWord ++ tailWord_2412058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412058).length < 2 ^ (prefixWord ++ tailWord_2412058).sum := by decide
  have hdescent : baseEnd_2412058 < baseStart_2412058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412085 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 3, 4]
def baseStart_2412085 : Nat := 118140960795 + 2412085 * 2 ^ 59
def prefixEnd_2412085 : Nat := 4983230072969 + 3 ^ 40 * 2412085 * 2
def baseEnd_2412085 : Nat := 412852994833433480014843

theorem tailTrace_2412085 : CollatzResearch.WordTrace tailWord_2412085 prefixEnd_2412085 412852994833433480014843 := by
  unfold tailWord_2412085
  simp only [CollatzResearch.WordTrace]
  refine ⟨87975967466435471165989709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58650644977623647443993139 87975967466435471165989709)
  ·
    refine ⟨32990987799913301687246141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87975967466435471165989709 32990987799913301687246141)
    ·
      refine ⟨12371620424967488132717303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32990987799913301687246141 12371620424967488132717303)
      ·
        refine ⟨18557430637451232199075955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12371620424967488132717303 18557430637451232199075955)
        ·
          refine ⟨27836145956176848298613933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18557430637451232199075955 27836145956176848298613933)
          ·
            refine ⟨10438554733566318111980225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27836145956176848298613933 10438554733566318111980225)
            ·
              refine ⟨7828916050174738583985169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10438554733566318111980225 7828916050174738583985169)
              ·
                refine ⟨5871687037631053937988877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7828916050174738583985169 5871687037631053937988877)
                ·
                  refine ⟨2201882639111645226745829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5871687037631053937988877 2201882639111645226745829)
                  ·
                    refine ⟨412852994833433480014843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2201882639111645226745829 412852994833433480014843)
                    ·
                      rfl

theorem cell23_2412085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_2412085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412085 prefixEnd_2412085 := by exact prefixLift 2412085
  have htrace : WordTrace (prefixWord ++ tailWord_2412085) baseStart_2412085 baseEnd_2412085 := by
    simpa [prefixWord, tailWord_2412085, baseEnd_2412085] using wordTrace_append hprefix tailTrace_2412085
  have hstable : (prefixWord ++ tailWord_2412085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412085).length < 2 ^ (prefixWord ++ tailWord_2412085).sum := by decide
  have hdescent : baseEnd_2412085 < baseStart_2412085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412119 : List Nat := [1, 1, 3, 2, 2, 4, 3, 2, 1, 4]
def baseStart_2412119 : Nat := 118140960795 + 2412119 * 2 ^ 59
def prefixEnd_2412119 : Nat := 4983230072969 + 3 ^ 40 * 2412119 * 2
def baseEnd_2412119 : Nat := 412858814280851102339791

theorem tailTrace_2412119 : CollatzResearch.WordTrace tailWord_2412119 prefixEnd_2412119 412858814280851102339791 := by
  unfold tailWord_2412119
  simp only [CollatzResearch.WordTrace]
  refine ⟨87977207548312294972727411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58651471698874863315151607 87977207548312294972727411)
  ·
    refine ⟨131965811322468442459091117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87977207548312294972727411 131965811322468442459091117)
    ·
      refine ⟨49487179245925665922159169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131965811322468442459091117 49487179245925665922159169)
      ·
        refine ⟨37115384434444249441619377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49487179245925665922159169 37115384434444249441619377)
        ·
          refine ⟨27836538325833187081214533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37115384434444249441619377 27836538325833187081214533)
          ·
            refine ⟨5219350936093722577727725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27836538325833187081214533 5219350936093722577727725)
            ·
              refine ⟨1957256601035145966647897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5219350936093722577727725 1957256601035145966647897)
              ·
                refine ⟨1467942450776359474985923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957256601035145966647897 1467942450776359474985923)
                ·
                  refine ⟨2201913676164539212478885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467942450776359474985923 2201913676164539212478885)
                  ·
                    refine ⟨412858814280851102339791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2201913676164539212478885 412858814280851102339791)
                    ·
                      rfl

theorem cell23_2412119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_2412119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412119 prefixEnd_2412119 := by exact prefixLift 2412119
  have htrace : WordTrace (prefixWord ++ tailWord_2412119) baseStart_2412119 baseEnd_2412119 := by
    simpa [prefixWord, tailWord_2412119, baseEnd_2412119] using wordTrace_append hprefix tailTrace_2412119
  have hstable : (prefixWord ++ tailWord_2412119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412119).length < 2 ^ (prefixWord ++ tailWord_2412119).sum := by decide
  have hdescent : baseEnd_2412119 < baseStart_2412119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412128 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 3, 5]
def baseStart_2412128 : Nat := 118140960795 + 2412128 * 2 ^ 59
def prefixEnd_2412128 : Nat := 4983230072969 + 3 ^ 40 * 2412128 * 2
def baseEnd_2412128 : Nat := 412860354722814590602277

theorem tailTrace_2412128 : CollatzResearch.WordTrace tailWord_2412128 prefixEnd_2412128 412860354722814590602277 := by
  unfold tailWord_2412128
  simp only [CollatzResearch.WordTrace]
  refine ⟨43988767902639844754902519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58651690536853126339870025 43988767902639844754902519)
  ·
    refine ⟨65983151853959767132353779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43988767902639844754902519 65983151853959767132353779)
    ·
      refine ⟨98974727780939650698530669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65983151853959767132353779 98974727780939650698530669)
      ·
        refine ⟨37115522917852369011949001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98974727780939650698530669 37115522917852369011949001)
        ·
          refine ⟨27836642188389276758961751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37115522917852369011949001 27836642188389276758961751)
          ·
            refine ⟨41754963282583915138442627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27836642188389276758961751 41754963282583915138442627)
            ·
              refine ⟨62632444923875872707663941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41754963282583915138442627 62632444923875872707663941)
              ·
                refine ⟨11743583423226726132686989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62632444923875872707663941 11743583423226726132686989)
                ·
                  refine ⟨4403843783710022299757621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11743583423226726132686989 4403843783710022299757621)
                  ·
                    refine ⟨412860354722814590602277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4403843783710022299757621 412860354722814590602277)
                    ·
                      rfl

theorem cell23_2412128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_2412128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412128 prefixEnd_2412128 := by exact prefixLift 2412128
  have htrace : WordTrace (prefixWord ++ tailWord_2412128) baseStart_2412128 baseEnd_2412128 := by
    simpa [prefixWord, tailWord_2412128, baseEnd_2412128] using wordTrace_append hprefix tailTrace_2412128
  have hstable : (prefixWord ++ tailWord_2412128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412128).length < 2 ^ (prefixWord ++ tailWord_2412128).sum := by decide
  have hdescent : baseEnd_2412128 < baseStart_2412128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412132 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 6]
def baseStart_2412132 : Nat := 118140960795 + 2412132 * 2 ^ 59
def prefixEnd_2412132 : Nat := 4983230072969 + 3 ^ 40 * 2412132 * 2
def baseEnd_2412132 : Nat := 137620346454562417350757

theorem tailTrace_2412132 : CollatzResearch.WordTrace tailWord_2412132 prefixEnd_2412132 137620346454562417350757 := by
  unfold tailWord_2412132
  simp only [CollatzResearch.WordTrace]
  refine ⟨43988840848632599096475325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58651787798176798795300433 43988840848632599096475325)
  ·
    refine ⟨16495815318237224661178247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43988840848632599096475325 16495815318237224661178247)
    ·
      refine ⟨24743722977355836991767371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16495815318237224661178247 24743722977355836991767371)
      ·
        refine ⟨37115584466033755487651057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24743722977355836991767371 37115584466033755487651057)
        ·
          refine ⟨27836688349525316615738293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37115584466033755487651057 27836688349525316615738293)
          ·
            refine ⟨2609689532767998432725465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27836688349525316615738293 2609689532767998432725465)
            ·
              refine ⟨1957267149575998824544099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2609689532767998432725465 1957267149575998824544099)
              ·
                refine ⟨2935900724363998236816149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957267149575998824544099 2935900724363998236816149)
                ·
                  refine ⟨137620346454562417350757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2935900724363998236816149 137620346454562417350757)
                  ·
                    rfl

theorem cell23_2412132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_2412132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412132 prefixEnd_2412132 := by exact prefixLift 2412132
  have htrace : WordTrace (prefixWord ++ tailWord_2412132) baseStart_2412132 baseEnd_2412132 := by
    simpa [prefixWord, tailWord_2412132, baseEnd_2412132] using wordTrace_append hprefix tailTrace_2412132
  have hstable : (prefixWord ++ tailWord_2412132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412132).length < 2 ^ (prefixWord ++ tailWord_2412132).sum := by decide
  have hdescent : baseEnd_2412132 < baseStart_2412132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412135 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_2412135 : Nat := 118140960795 + 2412135 * 2 ^ 59
def prefixEnd_2412135 : Nat := 4983230072969 + 3 ^ 40 * 2412135 * 2
def baseEnd_2412135 : Nat := 1238584658533025244419299

theorem tailTrace_2412135 : CollatzResearch.WordTrace tailWord_2412135 prefixEnd_2412135 1238584658533025244419299 := by
  unfold tailWord_2412135
  simp only [CollatzResearch.WordTrace]
  refine ⟨87977791116254329705309859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58651860744169553136873239 87977791116254329705309859)
  ·
    refine ⟨131966686674381494557964789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87977791116254329705309859 131966686674381494557964789)
    ·
      refine ⟨12371876875723265114809199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 131966686674381494557964789 12371876875723265114809199)
      ·
        refine ⟨18557815313584897672213799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12371876875723265114809199 18557815313584897672213799)
        ·
          refine ⟨27836722970377346508320699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18557815313584897672213799 27836722970377346508320699)
          ·
            refine ⟨41755084455566019762481049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27836722970377346508320699 41755084455566019762481049)
            ·
              refine ⟨31316313341674514821860787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41755084455566019762481049 31316313341674514821860787)
              ·
                refine ⟨46974470012511772232791181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31316313341674514821860787 46974470012511772232791181)
                ·
                  refine ⟨17615426254691914587296693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46974470012511772232791181 17615426254691914587296693)
                  ·
                    refine ⟨1651446211377366992559065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17615426254691914587296693 1651446211377366992559065)
                    ·
                      refine ⟨1238584658533025244419299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651446211377366992559065 1238584658533025244419299)
                      ·
                        rfl

theorem cell23_2412135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_2412135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412135 prefixEnd_2412135 := by exact prefixLift 2412135
  have htrace : WordTrace (prefixWord ++ tailWord_2412135) baseStart_2412135 baseEnd_2412135 := by
    simpa [prefixWord, tailWord_2412135, baseEnd_2412135] using wordTrace_append hprefix tailTrace_2412135
  have hstable : (prefixWord ++ tailWord_2412135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412135).length < 2 ^ (prefixWord ++ tailWord_2412135).sum := by decide
  have hdescent : baseEnd_2412135 < baseStart_2412135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412192 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 2, 4]
def baseStart_2412192 : Nat := 118140960795 + 2412192 * 2 ^ 59
def prefixEnd_2412192 : Nat := 4983230072969 + 3 ^ 40 * 2412192 * 2
def baseEnd_2412192 : Nat := 412871308976777173802179

theorem tailTrace_2412192 : CollatzResearch.WordTrace tailWord_2412192 prefixEnd_2412192 412871308976777173802179 := by
  unfold tailWord_2412192
  simp only [CollatzResearch.WordTrace]
  refine ⟨43989935038523914220067415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58653246718031885626756553 43989935038523914220067415)
  ·
    refine ⟨65984902557785871330101123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43989935038523914220067415 65984902557785871330101123)
    ·
      refine ⟨98977353836678806995151685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65984902557785871330101123 98977353836678806995151685)
      ·
        refine ⟨18558253844377276311590941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98977353836678806995151685 18558253844377276311590941)
        ·
          refine ⟨6959345191641478616846603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18558253844377276311590941 6959345191641478616846603)
          ·
            refine ⟨10439017787462217925269905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6959345191641478616846603 10439017787462217925269905)
            ·
              refine ⟨7829263340596663443952429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10439017787462217925269905 7829263340596663443952429)
              ·
                refine ⟨2935973752723748791482161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7829263340596663443952429 2935973752723748791482161)
                ·
                  refine ⟨2201980314542811593611621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2935973752723748791482161 2201980314542811593611621)
                  ·
                    refine ⟨412871308976777173802179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2201980314542811593611621 412871308976777173802179)
                    ·
                      rfl

theorem cell23_2412192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2, 4].length) (baseStart_2412192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412192 prefixEnd_2412192 := by exact prefixLift 2412192
  have htrace : WordTrace (prefixWord ++ tailWord_2412192) baseStart_2412192 baseEnd_2412192 := by
    simpa [prefixWord, tailWord_2412192, baseEnd_2412192] using wordTrace_append hprefix tailTrace_2412192
  have hstable : (prefixWord ++ tailWord_2412192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412192).length < 2 ^ (prefixWord ++ tailWord_2412192).sum := by decide
  have hdescent : baseEnd_2412192 < baseStart_2412192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412195 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 4]
def baseStart_2412195 : Nat := 118140960795 + 2412195 * 2 ^ 59
def prefixEnd_2412195 : Nat := 4983230072969 + 3 ^ 40 * 2412195 * 2
def baseEnd_2412195 : Nat := 1238615467372295009669023

theorem tailTrace_2412195 : CollatzResearch.WordTrace tailWord_2412195 prefixEnd_2412195 1238615467372295009669023 := by
  unfold tailWord_2412195
  simp only [CollatzResearch.WordTrace]
  refine ⟨87979979496036959952494039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58653319664024639968329359 87979979496036959952494039)
  ·
    refine ⟨131969969244055439928741059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87979979496036959952494039 131969969244055439928741059)
    ·
      refine ⟨197954953866083159893111589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131969969244055439928741059 197954953866083159893111589)
      ·
        refine ⟨37116553849890592479958423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 197954953866083159893111589 37116553849890592479958423)
        ·
          refine ⟨55674830774835888719937635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37116553849890592479958423 55674830774835888719937635)
          ·
            refine ⟨83512246162253833079906453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55674830774835888719937635 83512246162253833079906453)
            ·
              refine ⟨3914636538855648425620615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83512246162253833079906453 3914636538855648425620615)
              ·
                refine ⟨5871954808283472638430923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3914636538855648425620615 5871954808283472638430923)
                ·
                  refine ⟨8807932212425208957646385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5871954808283472638430923 8807932212425208957646385)
                  ·
                    refine ⟨6605949159318906718234789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8807932212425208957646385 6605949159318906718234789)
                    ·
                      refine ⟨1238615467372295009669023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6605949159318906718234789 1238615467372295009669023)
                      ·
                        rfl

theorem cell23_2412195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_2412195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412195 prefixEnd_2412195 := by exact prefixLift 2412195
  have htrace : WordTrace (prefixWord ++ tailWord_2412195) baseStart_2412195 baseEnd_2412195 := by
    simpa [prefixWord, tailWord_2412195, baseEnd_2412195] using wordTrace_append hprefix tailTrace_2412195
  have hstable : (prefixWord ++ tailWord_2412195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412195).length < 2 ^ (prefixWord ++ tailWord_2412195).sum := by decide
  have hdescent : baseEnd_2412195 < baseStart_2412195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412232 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_2412232 : Nat := 118140960795 + 2412232 * 2 ^ 59
def prefixEnd_2412232 : Nat := 4983230072969 + 3 ^ 40 * 2412232 * 2
def baseEnd_2412232 : Nat := 1238634466156511364906353

theorem tailTrace_2412232 : CollatzResearch.WordTrace tailWord_2412232 prefixEnd_2412232 1238634466156511364906353 := by
  unfold tailWord_2412232
  simp only [CollatzResearch.WordTrace]
  refine ⟨43990664498451457635795475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58654219331268610181060633 43990664498451457635795475)
  ·
    refine ⟨65985996747677186453693213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43990664498451457635795475 65985996747677186453693213)
    ·
      refine ⟨24744748780378944920134955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65985996747677186453693213 24744748780378944920134955)
      ·
        refine ⟨37117123170568417380202433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24744748780378944920134955 37117123170568417380202433)
        ·
          refine ⟨27837842377926313035151825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37117123170568417380202433 27837842377926313035151825)
          ·
            refine ⟨20878381783444734776363869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27837842377926313035151825 20878381783444734776363869)
            ·
              refine ⟨7829393168791775541136451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20878381783444734776363869 7829393168791775541136451)
              ·
                refine ⟨11744089753187663311704677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7829393168791775541136451 11744089753187663311704677)
                ·
                  refine ⟨2202016828722686870944627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11744089753187663311704677 2202016828722686870944627)
                  ·
                    refine ⟨3303025243084030306416941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2202016828722686870944627 3303025243084030306416941)
                    ·
                      refine ⟨1238634466156511364906353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3303025243084030306416941 1238634466156511364906353)
                      ·
                        rfl

theorem cell23_2412232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_2412232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412232 prefixEnd_2412232 := by exact prefixLift 2412232
  have htrace : WordTrace (prefixWord ++ tailWord_2412232) baseStart_2412232 baseEnd_2412232 := by
    simpa [prefixWord, tailWord_2412232, baseEnd_2412232] using wordTrace_append hprefix tailTrace_2412232
  have hstable : (prefixWord ++ tailWord_2412232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412232).length < 2 ^ (prefixWord ++ tailWord_2412232).sum := by decide
  have hdescent : baseEnd_2412232 < baseStart_2412232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412285 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_2412285 : Nat := 118140960795 + 2412285 * 2 ^ 59
def prefixEnd_2412285 : Nat := 4983230072969 + 3 ^ 40 * 2412285 * 2
def baseEnd_2412285 : Nat := 1238661680631199657543609

theorem tailTrace_2412285 : CollatzResearch.WordTrace tailWord_2412285 prefixEnd_2412285 1238661680631199657543609 := by
  unfold tailWord_2412285
  simp only [CollatzResearch.WordTrace]
  refine ⟨87983262065710905323270309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58655508043807270215513539 87983262065710905323270309)
  ·
    refine ⟨16496861637320794748113183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87983262065710905323270309 16496861637320794748113183)
    ·
      refine ⟨24745292455981192122169775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16496861637320794748113183 24745292455981192122169775)
      ·
        refine ⟨37117938683971788183254663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24745292455981192122169775 37117938683971788183254663)
        ·
          refine ⟨55676908025957682274881995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37117938683971788183254663 55676908025957682274881995)
          ·
            refine ⟨83515362038936523412322993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55676908025957682274881995 83515362038936523412322993)
            ·
              refine ⟨62636521529202392559242245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83515362038936523412322993 62636521529202392559242245)
              ·
                refine ⟨11744347786725448604857921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62636521529202392559242245 11744347786725448604857921)
                ·
                  refine ⟨8808260840044086453643441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11744347786725448604857921 8808260840044086453643441)
                  ·
                    refine ⟨6606195630033064840232581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8808260840044086453643441 6606195630033064840232581)
                    ·
                      refine ⟨1238661680631199657543609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6606195630033064840232581 1238661680631199657543609)
                      ·
                        rfl

theorem cell23_2412285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_2412285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412285 prefixEnd_2412285 := by exact prefixLift 2412285
  have htrace : WordTrace (prefixWord ++ tailWord_2412285) baseStart_2412285 baseEnd_2412285 := by
    simpa [prefixWord, tailWord_2412285, baseEnd_2412285] using wordTrace_append hprefix tailTrace_2412285
  have hstable : (prefixWord ++ tailWord_2412285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412285).length < 2 ^ (prefixWord ++ tailWord_2412285).sum := by decide
  have hdescent : baseEnd_2412285 < baseStart_2412285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412289 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_2412289 : Nat := 118140960795 + 2412289 * 2 ^ 59
def prefixEnd_2412289 : Nat := 4983230072969 + 3 ^ 40 * 2412289 * 2
def baseEnd_2412289 : Nat := 1238663734553817641893591

theorem tailTrace_2412289 : CollatzResearch.WordTrace tailWord_2412289 prefixEnd_2412289 1238663734553817641893591 := by
  unfold tailWord_2412289
  simp only [CollatzResearch.WordTrace]
  refine ⟨87983407957696414006415921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58655605305130942670943947 87983407957696414006415921)
  ·
    refine ⟨65987555968272310504811941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87983407957696414006415921 65987555968272310504811941)
    ·
      refine ⟨12372666744051058219652239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65987555968272310504811941 12372666744051058219652239)
      ·
        refine ⟨18559000116076587329478359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12372666744051058219652239 18559000116076587329478359)
        ·
          refine ⟨27838500174114880994217539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18559000116076587329478359 27838500174114880994217539)
          ·
            refine ⟨41757750261172321491326309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27838500174114880994217539 41757750261172321491326309)
            ·
              refine ⟨7829578173969810279623683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41757750261172321491326309 7829578173969810279623683)
              ·
                refine ⟨11744367260954715419435525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7829578173969810279623683 11744367260954715419435525)
                ·
                  refine ⟨2202068861429009141144161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11744367260954715419435525 2202068861429009141144161)
                  ·
                    refine ⟨1651551646071756855858121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2202068861429009141144161 1651551646071756855858121)
                    ·
                      refine ⟨1238663734553817641893591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651551646071756855858121 1238663734553817641893591)
                      ·
                        rfl

theorem cell23_2412289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_2412289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412289 prefixEnd_2412289 := by exact prefixLift 2412289
  have htrace : WordTrace (prefixWord ++ tailWord_2412289) baseStart_2412289 baseEnd_2412289 := by
    simpa [prefixWord, tailWord_2412289, baseEnd_2412289] using wordTrace_append hprefix tailTrace_2412289
  have hstable : (prefixWord ++ tailWord_2412289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412289).length < 2 ^ (prefixWord ++ tailWord_2412289).sum := by decide
  have hdescent : baseEnd_2412289 < baseStart_2412289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412294 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2412294 : Nat := 118140960795 + 2412294 * 2 ^ 59
def prefixEnd_2412294 : Nat := 4983230072969 + 3 ^ 40 * 2412294 * 2
def baseEnd_2412294 : Nat := 412888767319030040777023

theorem tailTrace_2412294 : CollatzResearch.WordTrace tailWord_2412294 prefixEnd_2412294 412888767319030040777023 := by
  unfold tailWord_2412294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2749487197583696870635873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58655726881785533240231957 2749487197583696870635873)
  ·
    refine ⟨2062115398187772652976905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2749487197583696870635873 2062115398187772652976905)
    ·
      refine ⟨1546586548640829489732679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2062115398187772652976905 1546586548640829489732679)
      ·
        refine ⟨2319879822961244234599019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546586548640829489732679 2319879822961244234599019)
        ·
          refine ⟨3479819734441866351898529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2319879822961244234599019 3479819734441866351898529)
          ·
            refine ⟨2609864800831399763923897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3479819734441866351898529 2609864800831399763923897)
            ·
              refine ⟨1957398600623549822942923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2609864800831399763923897 1957398600623549822942923)
              ·
                refine ⟨2936097900935324734414385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957398600623549822942923 2936097900935324734414385)
                ·
                  refine ⟨2202073425701493550810789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2936097900935324734414385 2202073425701493550810789)
                  ·
                    refine ⟨412888767319030040777023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2202073425701493550810789 412888767319030040777023)
                    ·
                      rfl

theorem cell23_2412294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2412294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412294 prefixEnd_2412294 := by exact prefixLift 2412294
  have htrace : WordTrace (prefixWord ++ tailWord_2412294) baseStart_2412294 baseEnd_2412294 := by
    simpa [prefixWord, tailWord_2412294, baseEnd_2412294] using wordTrace_append hprefix tailTrace_2412294
  have hstable : (prefixWord ++ tailWord_2412294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412294).length < 2 ^ (prefixWord ++ tailWord_2412294).sum := by decide
  have hdescent : baseEnd_2412294 < baseStart_2412294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412305 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 3]
def baseStart_2412305 : Nat := 118140960795 + 2412305 * 2 ^ 59
def prefixEnd_2412305 : Nat := 4983230072969 + 3 ^ 40 * 2412305 * 2
def baseEnd_2412305 : Nat := 1238671950244289579293517

theorem tailTrace_2412305 : CollatzResearch.WordTrace tailWord_2412305 prefixEnd_2412305 1238671950244289579293517 := by
  unfold tailWord_2412305
  simp only [CollatzResearch.WordTrace]
  refine ⟨87983991525638448738998369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58655994350425632492665579 87983991525638448738998369)
  ·
    refine ⟨65987993644228836554248777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87983991525638448738998369 65987993644228836554248777)
    ·
      refine ⟨49490995233171627415686583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65987993644228836554248777 49490995233171627415686583)
      ·
        refine ⟨74236492849757441123529875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49490995233171627415686583 74236492849757441123529875)
        ·
          refine ⟨111354739274636161685294813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74236492849757441123529875 111354739274636161685294813)
          ·
            refine ⟨41758027227988560631985555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111354739274636161685294813 41758027227988560631985555)
            ·
              refine ⟨62637040841982840947978333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41758027227988560631985555 62637040841982840947978333)
              ·
                refine ⟨23488890315743565355491875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62637040841982840947978333 23488890315743565355491875)
                ·
                  refine ⟨35233335473615348033237813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23488890315743565355491875 35233335473615348033237813)
                  ·
                    refine ⟨3303125200651438878116045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35233335473615348033237813 3303125200651438878116045)
                    ·
                      refine ⟨1238671950244289579293517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3303125200651438878116045 1238671950244289579293517)
                      ·
                        rfl

theorem cell23_2412305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_2412305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412305 prefixEnd_2412305 := by exact prefixLift 2412305
  have htrace : WordTrace (prefixWord ++ tailWord_2412305) baseStart_2412305 baseEnd_2412305 := by
    simpa [prefixWord, tailWord_2412305, baseEnd_2412305] using wordTrace_append hprefix tailTrace_2412305
  have hstable : (prefixWord ++ tailWord_2412305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412305).length < 2 ^ (prefixWord ++ tailWord_2412305).sum := by decide
  have hdescent : baseEnd_2412305 < baseStart_2412305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412346 : List Nat := [3, 1, 1, 1, 5, 3, 2, 2, 5]
def baseStart_2412346 : Nat := 118140960795 + 2412346 * 2 ^ 59
def prefixEnd_2412346 : Nat := 4983230072969 + 3 ^ 40 * 2412346 * 2
def baseEnd_2412346 : Nat := 137632555883458213208981

theorem tailTrace_2412346 : CollatzResearch.WordTrace tailWord_2412346 prefixEnd_2412346 137632555883458213208981 := by
  unfold tailWord_2412346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21996371729622478185310223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58656991278993275160827261 21996371729622478185310223)
  ·
    refine ⟨32994557594433717277965335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21996371729622478185310223 32994557594433717277965335)
    ·
      refine ⟨49491836391650575916948003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32994557594433717277965335 49491836391650575916948003)
      ·
        refine ⟨74237754587475863875422005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49491836391650575916948003 74237754587475863875422005)
        ·
          refine ⟨6959789492575862238320813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74237754587475863875422005 6959789492575862238320813)
          ·
            refine ⟨2609921059715948339370305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6959789492575862238320813 2609921059715948339370305)
            ·
              refine ⟨1957440794786961254527729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2609921059715948339370305 1957440794786961254527729)
              ·
                refine ⟨1468080596090220940895797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957440794786961254527729 1468080596090220940895797)
                ·
                  refine ⟨137632555883458213208981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1468080596090220940895797 137632555883458213208981)
                  ·
                    rfl

theorem cell23_2412346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_2412346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412346 prefixEnd_2412346 := by exact prefixLift 2412346
  have htrace : WordTrace (prefixWord ++ tailWord_2412346) baseStart_2412346 baseEnd_2412346 := by
    simpa [prefixWord, tailWord_2412346, baseEnd_2412346] using wordTrace_append hprefix tailTrace_2412346
  have hstable : (prefixWord ++ tailWord_2412346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412346).length < 2 ^ (prefixWord ++ tailWord_2412346).sum := by decide
  have hdescent : baseEnd_2412346 < baseStart_2412346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412349 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 2, 5, 2]
def baseStart_2412349 : Nat := 118140960795 + 2412349 * 2 ^ 59
def prefixEnd_2412349 : Nat := 4983230072969 + 3 ^ 40 * 2412349 * 2
def baseEnd_2412349 : Nat := 1238694543393087407143315

theorem tailTrace_2412349 : CollatzResearch.WordTrace tailWord_2412349 prefixEnd_2412349 1238694543393087407143315 := by
  unfold tailWord_2412349
  simp only [CollatzResearch.WordTrace]
  refine ⟨87985596337479044253600101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58657064224986029502400067 87985596337479044253600101)
  ·
    refine ⟨16497299313277320797550019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87985596337479044253600101 16497299313277320797550019)
    ·
      refine ⟨24745948969915981196325029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16497299313277320797550019 24745948969915981196325029)
      ·
        refine ⟨4639865431859246474310943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24745948969915981196325029 4639865431859246474310943)
        ·
          refine ⟨6959798147788869711466415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4639865431859246474310943 6959798147788869711466415)
          ·
            refine ⟨10439697221683304567199623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6959798147788869711466415 10439697221683304567199623)
            ·
              refine ⟨15659545832524956850799435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10439697221683304567199623 15659545832524956850799435)
              ·
                refine ⟨23489318748787435276199153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15659545832524956850799435 23489318748787435276199153)
                ·
                  refine ⟨17616989061590576457149365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23489318748787435276199153 17616989061590576457149365)
                  ·
                    refine ⟨1651592724524116542857753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17616989061590576457149365 1651592724524116542857753)
                    ·
                      refine ⟨1238694543393087407143315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651592724524116542857753 1238694543393087407143315)
                      ·
                        rfl

theorem cell23_2412349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_2412349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412349 prefixEnd_2412349 := by exact prefixLift 2412349
  have htrace : WordTrace (prefixWord ++ tailWord_2412349) baseStart_2412349 baseEnd_2412349 := by
    simpa [prefixWord, tailWord_2412349, baseEnd_2412349] using wordTrace_append hprefix tailTrace_2412349
  have hstable : (prefixWord ++ tailWord_2412349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412349).length < 2 ^ (prefixWord ++ tailWord_2412349).sum := by decide
  have hdescent : baseEnd_2412349 < baseStart_2412349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412385 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 8]
def baseStart_2412385 : Nat := 118140960795 + 2412385 * 2 ^ 59
def prefixEnd_2412385 : Nat := 4983230072969 + 3 ^ 40 * 2412385 * 2
def baseEnd_2412385 : Nat := 137634780966294362921461

theorem tailTrace_2412385 : CollatzResearch.WordTrace tailWord_2412385 prefixEnd_2412385 137634780966294362921461 := by
  unfold tailWord_2412385
  simp only [CollatzResearch.WordTrace]
  refine ⟨87986909365348622401910609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58657939576899081601273739 87986909365348622401910609)
  ·
    refine ⟨65990182024011466801432957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87986909365348622401910609 65990182024011466801432957)
    ·
      refine ⟨24746318259004300050537359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65990182024011466801432957 24746318259004300050537359)
      ·
        refine ⟨37119477388506450075806039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24746318259004300050537359 37119477388506450075806039)
        ·
          refine ⟨55679216082759675113709059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37119477388506450075806039 55679216082759675113709059)
          ·
            refine ⟨83518824124139512670563589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55679216082759675113709059 83518824124139512670563589)
            ·
              refine ⟨15659779523276158625730673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83518824124139512670563589 15659779523276158625730673)
              ·
                refine ⟨11744834642457118969298005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15659779523276158625730673 11744834642457118969298005)
                ·
                  refine ⟨137634780966294362921461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11744834642457118969298005 137634780966294362921461)
                  ·
                    rfl

theorem cell23_2412385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 8].length) (baseStart_2412385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412385 prefixEnd_2412385 := by exact prefixLift 2412385
  have htrace : WordTrace (prefixWord ++ tailWord_2412385) baseStart_2412385 baseEnd_2412385 := by
    simpa [prefixWord, tailWord_2412385, baseEnd_2412385] using wordTrace_append hprefix tailTrace_2412385
  have hstable : (prefixWord ++ tailWord_2412385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412385).length < 2 ^ (prefixWord ++ tailWord_2412385).sum := by decide
  have hdescent : baseEnd_2412385 < baseStart_2412385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412419 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 6]
def baseStart_2412419 : Nat := 118140960795 + 2412419 * 2 ^ 59
def prefixEnd_2412419 : Nat := 4983230072969 + 3 ^ 40 * 2412419 * 2
def baseEnd_2412419 : Nat := 137636720782100237029777

theorem tailTrace_2412419 : CollatzResearch.WordTrace tailWord_2412419 prefixEnd_2412419 137636720782100237029777 := by
  unfold tailWord_2412419
  simp only [CollatzResearch.WordTrace]
  refine ⟨87988149447225446208648311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58658766298150297472432207 87988149447225446208648311)
  ·
    refine ⟨131982224170838169312972467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87988149447225446208648311 131982224170838169312972467)
    ·
      refine ⟨197973336256257253969458701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131982224170838169312972467 197973336256257253969458701)
      ·
        refine ⟨74240001096096470238547013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 197973336256257253969458701 74240001096096470238547013)
        ·
          refine ⟨13920000205518088169727565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74240001096096470238547013 13920000205518088169727565)
          ·
            refine ⟨5220000077069283063647837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13920000205518088169727565 5220000077069283063647837)
            ·
              refine ⟨1957500028900981148867939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5220000077069283063647837 1957500028900981148867939)
              ·
                refine ⟨2936250043351471723301909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957500028900981148867939 2936250043351471723301909)
                ·
                  refine ⟨137636720782100237029777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2936250043351471723301909 137636720782100237029777)
                  ·
                    rfl

theorem cell23_2412419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 6].length) (baseStart_2412419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412419 prefixEnd_2412419 := by exact prefixLift 2412419
  have htrace : WordTrace (prefixWord ++ tailWord_2412419) baseStart_2412419 baseEnd_2412419 := by
    simpa [prefixWord, tailWord_2412419, baseEnd_2412419] using wordTrace_append hprefix tailTrace_2412419
  have hstable : (prefixWord ++ tailWord_2412419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412419).length < 2 ^ (prefixWord ++ tailWord_2412419).sum := by decide
  have hdescent : baseEnd_2412419 < baseStart_2412419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412432 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 1, 5]
def baseStart_2412432 : Nat := 118140960795 + 2412432 * 2 ^ 59
def prefixEnd_2412432 : Nat := 4983230072969 + 3 ^ 40 * 2412432 * 2
def baseEnd_2412432 : Nat := 412912387429136860801811

theorem tailTrace_2412432 : CollatzResearch.WordTrace tailWord_2412432 prefixEnd_2412432 412912387429136860801811 := by
  unfold tailWord_2412432
  simp only [CollatzResearch.WordTrace]
  refine ⟨43994311798089174714435775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58659082397452232952581033 43994311798089174714435775)
  ·
    refine ⟨65991467697133762071653663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43994311798089174714435775 65991467697133762071653663)
    ·
      refine ⟨98987201545700643107480495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65991467697133762071653663 98987201545700643107480495)
      ·
        refine ⟨148480802318550964661220743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98987201545700643107480495 148480802318550964661220743)
        ·
          refine ⟨222721203477826446991831115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148480802318550964661220743 222721203477826446991831115)
          ·
            refine ⟨334081805216739670487746673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222721203477826446991831115 334081805216739670487746673)
            ·
              refine ⟨250561353912554752865810005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334081805216739670487746673 250561353912554752865810005)
              ·
                refine ⟨2936265866162751010146211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 250561353912554752865810005 2936265866162751010146211)
                ·
                  refine ⟨4404398799244126515219317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2936265866162751010146211 4404398799244126515219317)
                  ·
                    refine ⟨412912387429136860801811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4404398799244126515219317 412912387429136860801811)
                    ·
                      rfl

theorem cell23_2412432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 1, 5].length) (baseStart_2412432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412432 prefixEnd_2412432 := by exact prefixLift 2412432
  have htrace : WordTrace (prefixWord ++ tailWord_2412432) baseStart_2412432 baseEnd_2412432 := by
    simpa [prefixWord, tailWord_2412432, baseEnd_2412432] using wordTrace_append hprefix tailTrace_2412432
  have hstable : (prefixWord ++ tailWord_2412432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412432).length < 2 ^ (prefixWord ++ tailWord_2412432).sum := by decide
  have hdescent : baseEnd_2412432 < baseStart_2412432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412439 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 1, 5, 2]
def baseStart_2412439 : Nat := 118140960795 + 2412439 * 2 ^ 59
def prefixEnd_2412439 : Nat := 4983230072969 + 3 ^ 40 * 2412439 * 2
def baseEnd_2412439 : Nat := 1238740756651992055017901

theorem tailTrace_2412439 : CollatzResearch.WordTrace tailWord_2412439 prefixEnd_2412439 1238740756651992055017901 := by
  unfold tailWord_2412439
  simp only [CollatzResearch.WordTrace]
  refine ⟨87988878907152989624376371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58659252604768659749584247 87988878907152989624376371)
  ·
    refine ⟨131983318360729484436564557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87988878907152989624376371 131983318360729484436564557)
    ·
      refine ⟨49493744385273556663711709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131983318360729484436564557 49493744385273556663711709)
      ·
        refine ⟨18560154144477583748891891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49493744385273556663711709 18560154144477583748891891)
        ·
          refine ⟨27840231216716375623337837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18560154144477583748891891 27840231216716375623337837)
          ·
            refine ⟨10440086706268640858751689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27840231216716375623337837 10440086706268640858751689)
            ·
              refine ⟨7830065029701480644063767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10440086706268640858751689 7830065029701480644063767)
              ·
                refine ⟨11745097544552220966095651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7830065029701480644063767 11745097544552220966095651)
                ·
                  refine ⟨17617646316828331449143477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11745097544552220966095651 17617646316828331449143477)
                  ·
                    refine ⟨1651654342202656073357201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17617646316828331449143477 1651654342202656073357201)
                    ·
                      refine ⟨1238740756651992055017901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1651654342202656073357201 1238740756651992055017901)
                      ·
                        rfl

theorem cell23_2412439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_2412439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412439 prefixEnd_2412439 := by exact prefixLift 2412439
  have htrace : WordTrace (prefixWord ++ tailWord_2412439) baseStart_2412439 baseEnd_2412439 := by
    simpa [prefixWord, tailWord_2412439, baseEnd_2412439] using wordTrace_append hprefix tailTrace_2412439
  have hstable : (prefixWord ++ tailWord_2412439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412439).length < 2 ^ (prefixWord ++ tailWord_2412439).sum := by decide
  have hdescent : baseEnd_2412439 < baseStart_2412439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412440 : List Nat := [2, 1, 2, 6, 1, 2, 1, 3, 1, 4]
def baseStart_2412440 : Nat := 118140960795 + 2412440 * 2 ^ 59
def prefixEnd_2412440 : Nat := 4983230072969 + 3 ^ 40 * 2412440 * 2
def baseEnd_2412440 : Nat := 412913756710882183701799

theorem tailTrace_2412440 : CollatzResearch.WordTrace tailWord_2412440 prefixEnd_2412440 412913756710882183701799 := by
  unfold tailWord_2412440
  simp only [CollatzResearch.WordTrace]
  refine ⟨43994457690074683397581387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58659276920099577863441849 43994457690074683397581387)
  ·
    refine ⟨65991686535112025096372081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43994457690074683397581387 65991686535112025096372081)
    ·
      refine ⟨49493764901334018822279061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65991686535112025096372081 49493764901334018822279061)
      ·
        refine ⟨2320020229750032132294331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49493764901334018822279061 2320020229750032132294331)
        ·
          refine ⟨3480030344625048198441497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2320020229750032132294331 3480030344625048198441497)
          ·
            refine ⟨2610022758468786148831123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3480030344625048198441497 2610022758468786148831123)
            ·
              refine ⟨3915034137703179223246685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610022758468786148831123 3915034137703179223246685)
              ·
                refine ⟨1468137801638692208717507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3915034137703179223246685 1468137801638692208717507)
                ·
                  refine ⟨2202206702458038313076261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468137801638692208717507 2202206702458038313076261)
                  ·
                    refine ⟨412913756710882183701799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2202206702458038313076261 412913756710882183701799)
                    ·
                      rfl

theorem cell23_2412440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_2412440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412440 prefixEnd_2412440 := by exact prefixLift 2412440
  have htrace : WordTrace (prefixWord ++ tailWord_2412440) baseStart_2412440 baseEnd_2412440 := by
    simpa [prefixWord, tailWord_2412440, baseEnd_2412440] using wordTrace_append hprefix tailTrace_2412440
  have hstable : (prefixWord ++ tailWord_2412440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412440).length < 2 ^ (prefixWord ++ tailWord_2412440).sum := by decide
  have hdescent : baseEnd_2412440 < baseStart_2412440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412463 : List Nat := [1, 1, 2, 1, 2, 2, 7, 2, 1, 1, 3]
def baseStart_2412463 : Nat := 118140960795 + 2412463 * 2 ^ 59
def prefixEnd_2412463 : Nat := 4983230072969 + 3 ^ 40 * 2412463 * 2
def baseEnd_2412463 : Nat := 1238753080187699961117791

theorem tailTrace_2412463 : CollatzResearch.WordTrace tailWord_2412463 prefixEnd_2412463 1238753080187699961117791 := by
  unfold tailWord_2412463
  simp only [CollatzResearch.WordTrace]
  refine ⟨87989754259066041723250043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58659836172710694482166695 87989754259066041723250043)
  ·
    refine ⟨131984631388599062584875065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87989754259066041723250043 131984631388599062584875065)
    ·
      refine ⟨98988473541449296938656299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131984631388599062584875065 98988473541449296938656299)
      ·
        refine ⟨148482710312173945407984449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98988473541449296938656299 148482710312173945407984449)
        ·
          refine ⟨111362032734130459055988337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148482710312173945407984449 111362032734130459055988337)
          ·
            refine ⟨83521524550597844291991253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111362032734130459055988337 83521524550597844291991253)
            ·
              refine ⟨1957535731654636975593545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 83521524550597844291991253 1957535731654636975593545)
              ·
                refine ⟨1468151798740977731695159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957535731654636975593545 1468151798740977731695159)
                ·
                  refine ⟨2202227698111466597542739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468151798740977731695159 2202227698111466597542739)
                  ·
                    refine ⟨3303341547167199896314109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2202227698111466597542739 3303341547167199896314109)
                    ·
                      refine ⟨1238753080187699961117791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3303341547167199896314109 1238753080187699961117791)
                      ·
                        rfl

theorem cell23_2412463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 1, 1, 3].length) (baseStart_2412463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412463 prefixEnd_2412463 := by exact prefixLift 2412463
  have htrace : WordTrace (prefixWord ++ tailWord_2412463) baseStart_2412463 baseEnd_2412463 := by
    simpa [prefixWord, tailWord_2412463, baseEnd_2412463] using wordTrace_append hprefix tailTrace_2412463
  have hstable : (prefixWord ++ tailWord_2412463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412463).length < 2 ^ (prefixWord ++ tailWord_2412463).sum := by decide
  have hdescent : baseEnd_2412463 < baseStart_2412463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412472 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_2412472 : Nat := 118140960795 + 2412472 * 2 ^ 59
def prefixEnd_2412472 : Nat := 4983230072969 + 3 ^ 40 * 2412472 * 2
def baseEnd_2412472 : Nat := 1238757701513590425905249

theorem tailTrace_2412472 : CollatzResearch.WordTrace tailWord_2412472 prefixEnd_2412472 1238757701513590425905249 := by
  unfold tailWord_2412472
  simp only [CollatzResearch.WordTrace]
  refine ⟨43995041258016718130163835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58660055010688957506885113 43995041258016718130163835)
  ·
    refine ⟨65992561887025077195245753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43995041258016718130163835 65992561887025077195245753)
    ·
      refine ⟨49494421415268807896434315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65992561887025077195245753 49494421415268807896434315)
      ·
        refine ⟨74241632122903211844651473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49494421415268807896434315 74241632122903211844651473)
        ·
          refine ⟨55681224092177408883488605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74241632122903211844651473 55681224092177408883488605)
          ·
            refine ⟨20880459034566528331308227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55681224092177408883488605 20880459034566528331308227)
            ·
              refine ⟨31320688551849792496962341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20880459034566528331308227 31320688551849792496962341)
              ·
                refine ⟨5872629103471836093180439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31320688551849792496962341 5872629103471836093180439)
                ·
                  refine ⟨8808943655207754139770659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5872629103471836093180439 8808943655207754139770659)
                  ·
                    refine ⟨13213415482811631209655989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8808943655207754139770659 13213415482811631209655989)
                    ·
                      refine ⟨1238757701513590425905249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13213415482811631209655989 1238757701513590425905249)
                      ·
                        rfl

theorem cell23_2412472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_2412472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412472 prefixEnd_2412472 := by exact prefixLift 2412472
  have htrace : WordTrace (prefixWord ++ tailWord_2412472) baseStart_2412472 baseEnd_2412472 := by
    simpa [prefixWord, tailWord_2412472, baseEnd_2412472] using wordTrace_append hprefix tailTrace_2412472
  have hstable : (prefixWord ++ tailWord_2412472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412472).length < 2 ^ (prefixWord ++ tailWord_2412472).sum := by decide
  have hdescent : baseEnd_2412472 < baseStart_2412472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412475 : List Nat := [1, 1, 1, 1, 1, 2, 2, 14]
def baseStart_2412475 : Nat := 118140960795 + 2412475 * 2 ^ 59
def prefixEnd_2412475 : Nat := 4983230072969 + 3 ^ 40 * 2412475 * 2
def baseEnd_2412475 : Nat := 45879971924279774598805

theorem tailTrace_2412475 : CollatzResearch.WordTrace tailWord_2412475 prefixEnd_2412475 45879971924279774598805 := by
  unfold tailWord_2412475
  simp only [CollatzResearch.WordTrace]
  refine ⟨87990191935022567772686879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58660127956681711848457919 87990191935022567772686879)
  ·
    refine ⟨131985287902533851659030319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87990191935022567772686879 131985287902533851659030319)
    ·
      refine ⟨197977931853800777488545479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131985287902533851659030319 197977931853800777488545479)
      ·
        refine ⟨296966897780701166232818219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197977931853800777488545479 296966897780701166232818219)
        ·
          refine ⟨445450346671051749349227329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296966897780701166232818219 445450346671051749349227329)
          ·
            refine ⟨334087760003288812011920497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445450346671051749349227329 334087760003288812011920497)
            ·
              refine ⟨250565820002466609008940373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334087760003288812011920497 250565820002466609008940373)
              ·
                refine ⟨45879971924279774598805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 250565820002466609008940373 45879971924279774598805)
                ·
                  rfl

theorem cell23_2412475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 14].length) (baseStart_2412475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412475 prefixEnd_2412475 := by exact prefixLift 2412475
  have htrace : WordTrace (prefixWord ++ tailWord_2412475) baseStart_2412475 baseEnd_2412475 := by
    simpa [prefixWord, tailWord_2412475, baseEnd_2412475] using wordTrace_append hprefix tailTrace_2412475
  have hstable : (prefixWord ++ tailWord_2412475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412475).length < 2 ^ (prefixWord ++ tailWord_2412475).sum := by decide
  have hdescent : baseEnd_2412475 < baseStart_2412475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412479 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 2, 4]
def baseStart_2412479 : Nat := 118140960795 + 2412479 * 2 ^ 59
def prefixEnd_2412479 : Nat := 4983230072969 + 3 ^ 40 * 2412479 * 2
def baseEnd_2412479 : Nat := 412920431959390632839239

theorem tailTrace_2412479 : CollatzResearch.WordTrace tailWord_2412479 prefixEnd_2412479 412920431959390632839239 := by
  unfold tailWord_2412479
  simp only [CollatzResearch.WordTrace]
  refine ⟨87990337827008076455832491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58660225218005384303888327 87990337827008076455832491)
  ·
    refine ⟨131985506740512114683748737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87990337827008076455832491 131985506740512114683748737)
    ·
      refine ⟨98989130055384086012811553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131985506740512114683748737 98989130055384086012811553)
      ·
        refine ⟨74241847541538064509608665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98989130055384086012811553 74241847541538064509608665)
        ·
          refine ⟨55681385656153548382206499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74241847541538064509608665 55681385656153548382206499)
          ·
            refine ⟨83522078484230322573309749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55681385656153548382206499 83522078484230322573309749)
            ·
              refine ⟨7830194857896592741247789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83522078484230322573309749 7830194857896592741247789)
              ·
                refine ⟨2936323071711222277967921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7830194857896592741247789 2936323071711222277967921)
                ·
                  refine ⟨2202242303783416708475941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2936323071711222277967921 2202242303783416708475941)
                  ·
                    refine ⟨412920431959390632839239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2202242303783416708475941 412920431959390632839239)
                    ·
                      rfl

theorem cell23_2412479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2, 4].length) (baseStart_2412479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412479 prefixEnd_2412479 := by exact prefixLift 2412479
  have htrace : WordTrace (prefixWord ++ tailWord_2412479) baseStart_2412479 baseEnd_2412479 := by
    simpa [prefixWord, tailWord_2412479, baseEnd_2412479] using wordTrace_append hprefix tailTrace_2412479
  have hstable : (prefixWord ++ tailWord_2412479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412479).length < 2 ^ (prefixWord ++ tailWord_2412479).sum := by decide
  have hdescent : baseEnd_2412479 < baseStart_2412479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2412492 : List Nat := [2, 2, 1, 4, 1, 2, 2, 9]
def baseStart_2412492 : Nat := 118140960795 + 2412492 * 2 ^ 59
def prefixEnd_2412492 : Nat := 4983230072969 + 3 ^ 40 * 2412492 * 2
def baseEnd_2412492 : Nat := 45880295226914086950191

theorem tailTrace_2412492 : CollatzResearch.WordTrace tailWord_2412492 prefixEnd_2412492 45880295226914086950191 := by
  unfold tailWord_2412492
  simp only [CollatzResearch.WordTrace]
  refine ⟨43995405987980489838027865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58660541317307319784037153 43995405987980489838027865)
  ·
    refine ⟨32996554490985367378520899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43995405987980489838027865 32996554490985367378520899)
    ·
      refine ⟨49494831736478051067781349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32996554490985367378520899 49494831736478051067781349)
      ·
        refine ⟨9280280950589634575209003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49494831736478051067781349 9280280950589634575209003)
        ·
          refine ⟨13920421425884451862813505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9280280950589634575209003 13920421425884451862813505)
          ·
            refine ⟨10440316069413338897110129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13920421425884451862813505 10440316069413338897110129)
            ·
              refine ⟨7830237052060004172832597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10440316069413338897110129 7830237052060004172832597)
              ·
                refine ⟨45880295226914086950191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7830237052060004172832597 45880295226914086950191)
                ·
                  rfl

theorem cell23_2412492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 9].length) (baseStart_2412492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2412492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2412492 prefixEnd_2412492 := by exact prefixLift 2412492
  have htrace : WordTrace (prefixWord ++ tailWord_2412492) baseStart_2412492 baseEnd_2412492 := by
    simpa [prefixWord, tailWord_2412492, baseEnd_2412492] using wordTrace_append hprefix tailTrace_2412492
  have hstable : (prefixWord ++ tailWord_2412492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2412492).length < 2 ^ (prefixWord ++ tailWord_2412492).sum := by decide
  have hdescent : baseEnd_2412492 < baseStart_2412492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2412492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
