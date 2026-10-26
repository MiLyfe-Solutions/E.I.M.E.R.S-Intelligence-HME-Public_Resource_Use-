import V185TrunkScan19Chunk000

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_9629 : List Nat := [1, 4, 2, 1, 3, 1, 1, 6]
def baseStart_9629 : Nat := 118140960795 + 9629 * 2 ^ 59
def prefixEnd_9629 : Nat := 4983230072969 + 3 ^ 40 * 9629 * 2
def baseEnd_9629 : Nat := 2929958650221072707095

theorem tailTrace_9629 : CollatzResearch.WordTrace tailWord_9629 prefixEnd_9629 2929958650221072707095 := by
  unfold tailWord_9629
  simp only [CollatzResearch.WordTrace]
  refine ⟨351198482123252347383941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 234132321415501564922627 351198482123252347383941)
  ·
    refine ⟨65849715398109815134489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 351198482123252347383941 65849715398109815134489)
    ·
      refine ⟨49387286548582361350867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65849715398109815134489 49387286548582361350867)
      ·
        refine ⟨74080929822873542026301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49387286548582361350867 74080929822873542026301)
        ·
          refine ⟨27780348683577578259863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74080929822873542026301 27780348683577578259863)
          ·
            refine ⟨41670523025366367389795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27780348683577578259863 41670523025366367389795)
            ·
              refine ⟨62505784538049551084693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41670523025366367389795 62505784538049551084693)
              ·
                refine ⟨2929958650221072707095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62505784538049551084693 2929958650221072707095)
                ·
                  rfl

theorem cell19_9629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_9629 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9629 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9629 prefixEnd_9629 := by exact prefixLift 9629
  have htrace : WordTrace (prefixWord ++ tailWord_9629) baseStart_9629 baseEnd_9629 := by
    simpa [prefixWord, tailWord_9629, baseEnd_9629] using wordTrace_append hprefix tailTrace_9629
  have hstable : (prefixWord ++ tailWord_9629).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9629).length < 2 ^ (prefixWord ++ tailWord_9629).sum := by decide
  have hdescent : baseEnd_9629 < baseStart_9629 := by decide
  rcases family_descends (prefixWord ++ tailWord_9629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9703 : List Nat := [1, 1, 5, 2, 1, 3, 3, 3]
def baseStart_9703 : Nat := 118140960795 + 9703 * 2 ^ 59
def prefixEnd_9703 : Nat := 4983230072969 + 3 ^ 40 * 9703 * 2
def baseEnd_9703 : Nat := 2952475727810827062449

theorem tailTrace_9703 : CollatzResearch.WordTrace tailWord_9703 prefixEnd_9703 2952475727810827062449 := by
  unfold tailWord_9703
  simp only [CollatzResearch.WordTrace]
  refine ⟨353897483855162985577763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 235931655903441990385175 353897483855162985577763)
  ·
    refine ⟨530846225782744478366645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 353897483855162985577763 530846225782744478366645)
    ·
      refine ⟨49766833667132294846873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 530846225782744478366645 49766833667132294846873)
      ·
        refine ⟨37325125250349221135155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49766833667132294846873 37325125250349221135155)
        ·
          refine ⟨55987687875523831702733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37325125250349221135155 55987687875523831702733)
          ·
            refine ⟨20995382953321436888525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55987687875523831702733 20995382953321436888525)
            ·
              refine ⟨7873268607495538833197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20995382953321436888525 7873268607495538833197)
              ·
                refine ⟨2952475727810827062449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7873268607495538833197 2952475727810827062449)
                ·
                  rfl

theorem cell19_9703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 3].length) (baseStart_9703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9703 prefixEnd_9703 := by exact prefixLift 9703
  have htrace : WordTrace (prefixWord ++ tailWord_9703) baseStart_9703 baseEnd_9703 := by
    simpa [prefixWord, tailWord_9703, baseEnd_9703] using wordTrace_append hprefix tailTrace_9703
  have hstable : (prefixWord ++ tailWord_9703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9703).length < 2 ^ (prefixWord ++ tailWord_9703).sum := by decide
  have hdescent : baseEnd_9703 < baseStart_9703 := by decide
  rcases family_descends (prefixWord ++ tailWord_9703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9745 : List Nat := [1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_9745 : Nat := 118140960795 + 9745 * 2 ^ 59
def prefixEnd_9745 : Nat := 4983230072969 + 3 ^ 40 * 9745 * 2
def baseEnd_9745 : Nat := 2965255690767174129001

theorem tailTrace_9745 : CollatzResearch.WordTrace tailWord_9745 prefixEnd_9745 2965255690767174129001 := by
  unfold tailWord_9745
  simp only [CollatzResearch.WordTrace]
  refine ⟨355429349703004158606689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 236952899802002772404459 355429349703004158606689)
  ·
    refine ⟨266572012277253118955017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 355429349703004158606689 266572012277253118955017)
    ·
      refine ⟨199929009207939839216263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266572012277253118955017 199929009207939839216263)
      ·
        refine ⟨299893513811909758824395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199929009207939839216263 299893513811909758824395)
        ·
          refine ⟨449840270717864638236593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299893513811909758824395 449840270717864638236593)
          ·
            refine ⟨337380203038398478677445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449840270717864638236593 337380203038398478677445)
            ·
              refine ⟨63258788069699714752021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 337380203038398478677445 63258788069699714752021)
              ·
                refine ⟨2965255690767174129001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63258788069699714752021 2965255690767174129001)
                ·
                  rfl

theorem cell19_9745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_9745 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9745 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9745 prefixEnd_9745 := by exact prefixLift 9745
  have htrace : WordTrace (prefixWord ++ tailWord_9745) baseStart_9745 baseEnd_9745 := by
    simpa [prefixWord, tailWord_9745, baseEnd_9745] using wordTrace_append hprefix tailTrace_9745
  have hstable : (prefixWord ++ tailWord_9745).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9745).length < 2 ^ (prefixWord ++ tailWord_9745).sum := by decide
  have hdescent : baseEnd_9745 < baseStart_9745 := by decide
  rcases family_descends (prefixWord ++ tailWord_9745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9760 : List Nat := [2, 1, 1, 6, 1, 1, 4, 3]
def baseStart_9760 : Nat := 118140960795 + 9760 * 2 ^ 59
def prefixEnd_9760 : Nat := 4983230072969 + 3 ^ 40 * 9760 * 2
def baseEnd_9760 : Nat := 2969819963251583795627

theorem tailTrace_9760 : CollatzResearch.WordTrace tailWord_9760 prefixEnd_9760 2969819963251583795627 := by
  unfold tailWord_9760
  simp only [CollatzResearch.WordTrace]
  refine ⟨177988222324330860201367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 237317629765774480268489 177988222324330860201367)
  ·
    refine ⟨266982333486496290302051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177988222324330860201367 266982333486496290302051)
    ·
      refine ⟨400473500229744435453077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266982333486496290302051 400473500229744435453077)
      ·
        refine ⟨18772195323269270411863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 400473500229744435453077 18772195323269270411863)
        ·
          refine ⟨28158292984903905617795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18772195323269270411863 28158292984903905617795)
          ·
            refine ⟨42237439477355858426693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28158292984903905617795 42237439477355858426693)
            ·
              refine ⟨7919519902004223455005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42237439477355858426693 7919519902004223455005)
              ·
                refine ⟨2969819963251583795627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7919519902004223455005 2969819963251583795627)
                ·
                  rfl

theorem cell19_9760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_9760 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9760 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9760 prefixEnd_9760 := by exact prefixLift 9760
  have htrace : WordTrace (prefixWord ++ tailWord_9760) baseStart_9760 baseEnd_9760 := by
    simpa [prefixWord, tailWord_9760, baseEnd_9760] using wordTrace_append hprefix tailTrace_9760
  have hstable : (prefixWord ++ tailWord_9760).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9760).length < 2 ^ (prefixWord ++ tailWord_9760).sum := by decide
  have hdescent : baseEnd_9760 < baseStart_9760 := by decide
  rcases family_descends (prefixWord ++ tailWord_9760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9781 : List Nat := [1, 3, 3, 1, 1, 5, 5]
def baseStart_9781 : Nat := 118140960795 + 9781 * 2 ^ 59
def prefixEnd_9781 : Nat := 4983230072969 + 3 ^ 40 * 9781 * 2
def baseEnd_9781 : Nat := 992069981576585776301

theorem tailTrace_9781 : CollatzResearch.WordTrace tailWord_9781 prefixEnd_9781 992069981576585776301 := by
  unfold tailWord_9781
  simp only [CollatzResearch.WordTrace]
  refine ⟨356742377572582306917197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 237828251715054871278131 356742377572582306917197)
  ·
    refine ⟨133778391589718365093949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 356742377572582306917197 133778391589718365093949)
    ·
      refine ⟨50166896846144386910231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133778391589718365093949 50166896846144386910231)
      ·
        refine ⟨75250345269216580365347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50166896846144386910231 75250345269216580365347)
        ·
          refine ⟨112875517903824870548021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75250345269216580365347 112875517903824870548021)
          ·
            refine ⟨10582079803483581613877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112875517903824870548021 10582079803483581613877)
            ·
              refine ⟨992069981576585776301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10582079803483581613877 992069981576585776301)
              ·
                rfl

theorem cell19_9781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_9781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9781 prefixEnd_9781 := by exact prefixLift 9781
  have htrace : WordTrace (prefixWord ++ tailWord_9781) baseStart_9781 baseEnd_9781 := by
    simpa [prefixWord, tailWord_9781, baseEnd_9781] using wordTrace_append hprefix tailTrace_9781
  have hstable : (prefixWord ++ tailWord_9781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9781).length < 2 ^ (prefixWord ++ tailWord_9781).sum := by decide
  have hdescent : baseEnd_9781 < baseStart_9781 := by decide
  rcases family_descends (prefixWord ++ tailWord_9781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9783 : List Nat := [1, 1, 3, 1, 2, 4, 7]
def baseStart_9783 : Nat := 118140960795 + 9783 * 2 ^ 59
def prefixEnd_9783 : Nat := 4983230072969 + 3 ^ 40 * 9783 * 2
def baseEnd_9783 : Nat := 992272838131448428151

theorem tailTrace_9783 : CollatzResearch.WordTrace tailWord_9783 prefixEnd_9783 992272838131448428151 := by
  unfold tailWord_9783
  simp only [CollatzResearch.WordTrace]
  refine ⟨356815323565336648490003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 237876882376891098993335 356815323565336648490003)
  ·
    refine ⟨535222985348004972735005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 356815323565336648490003 535222985348004972735005)
    ·
      refine ⟨200708619505501864775627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 535222985348004972735005 200708619505501864775627)
      ·
        refine ⟨301062929258252797163441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200708619505501864775627 301062929258252797163441)
        ·
          refine ⟨225797196943689597872581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301062929258252797163441 225797196943689597872581)
          ·
            refine ⟨42336974426941799601109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225797196943689597872581 42336974426941799601109)
            ·
              refine ⟨992272838131448428151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 42336974426941799601109 992272838131448428151)
              ·
                rfl

theorem cell19_9783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_9783 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9783 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9783 prefixEnd_9783 := by exact prefixLift 9783
  have htrace : WordTrace (prefixWord ++ tailWord_9783) baseStart_9783 baseEnd_9783 := by
    simpa [prefixWord, tailWord_9783, baseEnd_9783] using wordTrace_append hprefix tailTrace_9783
  have hstable : (prefixWord ++ tailWord_9783).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9783).length < 2 ^ (prefixWord ++ tailWord_9783).sum := by decide
  have hdescent : baseEnd_9783 < baseStart_9783 := by decide
  rcases family_descends (prefixWord ++ tailWord_9783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9838 : List Nat := [4, 1, 2, 2, 3, 7]
def baseStart_9838 : Nat := 118140960795 + 9838 * 2 ^ 59
def prefixEnd_9838 : Nat := 4983230072969 + 3 ^ 40 * 9838 * 2
def baseEnd_9838 : Nat := 332617131130057118009

theorem tailTrace_9838 : CollatzResearch.WordTrace tailWord_9838 prefixEnd_9838 332617131130057118009 := by
  unfold tailWord_9838
  simp only [CollatzResearch.WordTrace]
  refine ⟨44852667295760130217771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 239214225577387361161445 44852667295760130217771)
  ·
    refine ⟨67279000943640195326657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44852667295760130217771 67279000943640195326657)
    ·
      refine ⟨50459250707730146494993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67279000943640195326657 50459250707730146494993)
      ·
        refine ⟨37844438030797609871245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50459250707730146494993 37844438030797609871245)
        ·
          refine ⟨14191664261549103701717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37844438030797609871245 14191664261549103701717)
          ·
            refine ⟨332617131130057118009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 14191664261549103701717 332617131130057118009)
            ·
              rfl

theorem cell19_9838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 7].length) (baseStart_9838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9838 prefixEnd_9838 := by exact prefixLift 9838
  have htrace : WordTrace (prefixWord ++ tailWord_9838) baseStart_9838 baseEnd_9838 := by
    simpa [prefixWord, tailWord_9838, baseEnd_9838] using wordTrace_append hprefix tailTrace_9838
  have hstable : (prefixWord ++ tailWord_9838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9838).length < 2 ^ (prefixWord ++ tailWord_9838).sum := by decide
  have hdescent : baseEnd_9838 < baseStart_9838 := by decide
  rcases family_descends (prefixWord ++ tailWord_9838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9840 : List Nat := [2, 1, 1, 1, 6, 8]
def baseStart_9840 : Nat := 118140960795 + 9840 * 2 ^ 59
def prefixEnd_9840 : Nat := 4983230072969 + 3 ^ 40 * 9840 * 2
def baseEnd_9840 : Nat := 332684749981678001959

theorem tailTrace_9840 : CollatzResearch.WordTrace tailWord_9840 prefixEnd_9840 332684749981678001959 := by
  unfold tailWord_9840
  simp only [CollatzResearch.WordTrace]
  refine ⟨179447142179417691657487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 239262856239223588876649 179447142179417691657487)
  ·
    refine ⟨269170713269126537486231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179447142179417691657487 269170713269126537486231)
    ·
      refine ⟨403756069903689806229347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269170713269126537486231 403756069903689806229347)
      ·
        refine ⟨605634104855534709344021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403756069903689806229347 605634104855534709344021)
        ·
          refine ⟨28389098665103189500501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 605634104855534709344021 28389098665103189500501)
          ·
            refine ⟨332684749981678001959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 28389098665103189500501 332684749981678001959)
            ·
              rfl

theorem cell19_9840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 8].length) (baseStart_9840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9840 prefixEnd_9840 := by exact prefixLift 9840
  have htrace : WordTrace (prefixWord ++ tailWord_9840) baseStart_9840 baseEnd_9840 := by
    simpa [prefixWord, tailWord_9840, baseEnd_9840] using wordTrace_append hprefix tailTrace_9840
  have hstable : (prefixWord ++ tailWord_9840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9840).length < 2 ^ (prefixWord ++ tailWord_9840).sum := by decide
  have hdescent : baseEnd_9840 < baseStart_9840 := by decide
  rcases family_descends (prefixWord ++ tailWord_9840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9857 : List Nat := [1, 2, 4, 2, 1, 2, 3, 4]
def baseStart_9857 : Nat := 118140960795 + 9857 * 2 ^ 59
def prefixEnd_9857 : Nat := 4983230072969 + 3 ^ 40 * 9857 * 2
def baseEnd_9857 : Nat := 2999335591984099639807

theorem tailTrace_9857 : CollatzResearch.WordTrace tailWord_9857 prefixEnd_9857 2999335591984099639807 := by
  unfold tailWord_9857
  simp only [CollatzResearch.WordTrace]
  refine ⟨359514325297247286683825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 239676216864831524455883 359514325297247286683825)
  ·
    refine ⟨269635743972935465012869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 359514325297247286683825 269635743972935465012869)
    ·
      refine ⟨50556701994925399689913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 269635743972935465012869 50556701994925399689913)
      ·
        refine ⟨37917526496194049767435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50556701994925399689913 37917526496194049767435)
        ·
          refine ⟨56876289744291074651153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37917526496194049767435 56876289744291074651153)
          ·
            refine ⟨42657217308218305988365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56876289744291074651153 42657217308218305988365)
            ·
              refine ⟨15996456490581864745637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42657217308218305988365 15996456490581864745637)
              ·
                refine ⟨2999335591984099639807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15996456490581864745637 2999335591984099639807)
                ·
                  rfl

theorem cell19_9857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_9857 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9857 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9857 prefixEnd_9857 := by exact prefixLift 9857
  have htrace : WordTrace (prefixWord ++ tailWord_9857) baseStart_9857 baseEnd_9857 := by
    simpa [prefixWord, tailWord_9857, baseEnd_9857] using wordTrace_append hprefix tailTrace_9857
  have hstable : (prefixWord ++ tailWord_9857).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9857).length < 2 ^ (prefixWord ++ tailWord_9857).sum := by decide
  have hdescent : baseEnd_9857 < baseStart_9857 := by decide
  rcases family_descends (prefixWord ++ tailWord_9857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9948 : List Nat := [2, 2, 5, 1, 3, 1, 5]
def baseStart_9948 : Nat := 118140960795 + 9948 * 2 ^ 59
def prefixEnd_9948 : Nat := 4983230072969 + 3 ^ 40 * 9948 * 2
def baseEnd_9948 : Nat := 1009008503907617205779

theorem tailTrace_9948 : CollatzResearch.WordTrace tailWord_9948 prefixEnd_9948 1009008503907617205779 := by
  unfold tailWord_9948
  simp only [CollatzResearch.WordTrace]
  refine ⟨181416683983784914123249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 241888911978379885497665 181416683983784914123249)
  ·
    refine ⟨136062512987838685592437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181416683983784914123249 136062512987838685592437)
    ·
      refine ⟨12755860592609876774291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136062512987838685592437 12755860592609876774291)
      ·
        refine ⟨19133790888914815161437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12755860592609876774291 19133790888914815161437)
        ·
          refine ⟨7175171583343055685539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19133790888914815161437 7175171583343055685539)
          ·
            refine ⟨10762757375014583528309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7175171583343055685539 10762757375014583528309)
            ·
              refine ⟨1009008503907617205779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10762757375014583528309 1009008503907617205779)
              ·
                rfl

theorem cell19_9948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 5].length) (baseStart_9948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9948 prefixEnd_9948 := by exact prefixLift 9948
  have htrace : WordTrace (prefixWord ++ tailWord_9948) baseStart_9948 baseEnd_9948 := by
    simpa [prefixWord, tailWord_9948, baseEnd_9948] using wordTrace_append hprefix tailTrace_9948
  have hstable : (prefixWord ++ tailWord_9948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9948).length < 2 ^ (prefixWord ++ tailWord_9948).sum := by decide
  have hdescent : baseEnd_9948 < baseStart_9948 := by decide
  rcases family_descends (prefixWord ++ tailWord_9948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_9992 : List Nat := [2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_9992 : Nat := 118140960795 + 9992 * 2 ^ 59
def prefixEnd_9992 : Nat := 4983230072969 + 3 ^ 40 * 9992 * 2
def baseEnd_9992 : Nat := 3040414044343786639439

theorem tailTrace_9992 : CollatzResearch.WordTrace tailWord_9992 prefixEnd_9992 3040414044343786639439 := by
  unfold tailWord_9992
  simp only [CollatzResearch.WordTrace]
  refine ⟨182219089904082671424115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 242958786538776895232153 182219089904082671424115)
  ·
    refine ⟨273328634856124007136173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182219089904082671424115 273328634856124007136173)
    ·
      refine ⟨102498238071046502676065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 273328634856124007136173 102498238071046502676065)
      ·
        refine ⟨76873678553284877007049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102498238071046502676065 76873678553284877007049)
        ·
          refine ⟨57655258914963657755287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76873678553284877007049 57655258914963657755287)
          ·
            refine ⟨86482888372445486632931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57655258914963657755287 86482888372445486632931)
            ·
              refine ⟨129724332558668229949397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86482888372445486632931 129724332558668229949397)
              ·
                refine ⟨3040414044343786639439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 129724332558668229949397 3040414044343786639439)
                ·
                  rfl

theorem cell19_9992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_9992 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_9992 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_9992 prefixEnd_9992 := by exact prefixLift 9992
  have htrace : WordTrace (prefixWord ++ tailWord_9992) baseStart_9992 baseEnd_9992 := by
    simpa [prefixWord, tailWord_9992, baseEnd_9992] using wordTrace_append hprefix tailTrace_9992
  have hstable : (prefixWord ++ tailWord_9992).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_9992).length < 2 ^ (prefixWord ++ tailWord_9992).sum := by decide
  have hdescent : baseEnd_9992 < baseStart_9992 := by decide
  rcases family_descends (prefixWord ++ tailWord_9992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10028 : List Nat := [2, 2, 1, 1, 1, 7, 1, 4]
def baseStart_10028 : Nat := 118140960795 + 10028 * 2 ^ 59
def prefixEnd_10028 : Nat := 4983230072969 + 3 ^ 40 * 10028 * 2
def baseEnd_10028 : Nat := 3051368298306369839341

theorem tailTrace_10028 : CollatzResearch.WordTrace tailWord_10028 prefixEnd_10028 3051368298306369839341 := by
  unfold tailWord_10028
  simp only [CollatzResearch.WordTrace]
  refine ⟨182875603838871745579369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 243834138451828994105825 182875603838871745579369)
  ·
    refine ⟨137156702879153809184527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182875603838871745579369 137156702879153809184527)
    ·
      refine ⟨205735054318730713776791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137156702879153809184527 205735054318730713776791)
      ·
        refine ⟨308602581478096070665187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205735054318730713776791 308602581478096070665187)
        ·
          refine ⟨462903872217144105997781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308602581478096070665187 462903872217144105997781)
          ·
            refine ⟨10849309505089314984323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 462903872217144105997781 10849309505089314984323)
            ·
              refine ⟨16273964257633972476485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10849309505089314984323 16273964257633972476485)
              ·
                refine ⟨3051368298306369839341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16273964257633972476485 3051368298306369839341)
                ·
                  rfl

theorem cell19_10028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_10028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10028 prefixEnd_10028 := by exact prefixLift 10028
  have htrace : WordTrace (prefixWord ++ tailWord_10028) baseStart_10028 baseEnd_10028 := by
    simpa [prefixWord, tailWord_10028, baseEnd_10028] using wordTrace_append hprefix tailTrace_10028
  have hstable : (prefixWord ++ tailWord_10028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10028).length < 2 ^ (prefixWord ++ tailWord_10028).sum := by decide
  have hdescent : baseEnd_10028 < baseStart_10028 := by decide
  rcases family_descends (prefixWord ++ tailWord_10028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10045 : List Nat := [1, 4, 1, 4, 1, 2, 3, 3]
def baseStart_10045 : Nat := 118140960795 + 10045 * 2 ^ 59
def prefixEnd_10045 : Nat := 4983230072969 + 3 ^ 40 * 10045 * 2
def baseEnd_10045 : Nat := 3056541140455367461517

theorem tailTrace_10045 : CollatzResearch.WordTrace tailWord_10045 prefixEnd_10045 3056541140455367461517 := by
  unfold tailWord_10045
  simp only [CollatzResearch.WordTrace]
  refine ⟨366371248616155394527589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 244247499077436929685059 366371248616155394527589)
  ·
    refine ⟨68694609115529136473923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 366371248616155394527589 68694609115529136473923)
    ·
      refine ⟨103041913673293704710885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68694609115529136473923 103041913673293704710885)
      ·
        refine ⟨19320358813742569633291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103041913673293704710885 19320358813742569633291)
        ·
          refine ⟨28980538220613854449937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19320358813742569633291 28980538220613854449937)
          ·
            refine ⟨21735403665460390837453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28980538220613854449937 21735403665460390837453)
            ·
              refine ⟨8150776374547646564045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21735403665460390837453 8150776374547646564045)
              ·
                refine ⟨3056541140455367461517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8150776374547646564045 3056541140455367461517)
                ·
                  rfl

theorem cell19_10045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 3].length) (baseStart_10045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10045 prefixEnd_10045 := by exact prefixLift 10045
  have htrace : WordTrace (prefixWord ++ tailWord_10045) baseStart_10045 baseEnd_10045 := by
    simpa [prefixWord, tailWord_10045, baseEnd_10045] using wordTrace_append hprefix tailTrace_10045
  have hstable : (prefixWord ++ tailWord_10045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10045).length < 2 ^ (prefixWord ++ tailWord_10045).sum := by decide
  have hdescent : baseEnd_10045 < baseStart_10045 := by decide
  rcases family_descends (prefixWord ++ tailWord_10045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10087 : List Nat := [1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_10087 : Nat := 118140960795 + 10087 * 2 ^ 59
def prefixEnd_10087 : Nat := 4983230072969 + 3 ^ 40 * 10087 * 2
def baseEnd_10087 : Nat := 3069321103411714528069

theorem tailTrace_10087 : CollatzResearch.WordTrace tailWord_10087 prefixEnd_10087 3069321103411714528069 := by
  unfold tailWord_10087
  simp only [CollatzResearch.WordTrace]
  refine ⟨367903114463996567556515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 245268742975997711704343 367903114463996567556515)
  ·
    refine ⟨551854671695994851334773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 367903114463996567556515 551854671695994851334773)
    ·
      refine ⟨51736375471499517312635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 551854671695994851334773 51736375471499517312635)
      ·
        refine ⟨77604563207249275968953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51736375471499517312635 77604563207249275968953)
        ·
          refine ⟨58203422405436956976715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77604563207249275968953 58203422405436956976715)
          ·
            refine ⟨87305133608155435465073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58203422405436956976715 87305133608155435465073)
            ·
              refine ⟨65478850206116576598805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87305133608155435465073 65478850206116576598805)
              ·
                refine ⟨3069321103411714528069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65478850206116576598805 3069321103411714528069)
                ·
                  rfl

theorem cell19_10087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_10087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10087 prefixEnd_10087 := by exact prefixLift 10087
  have htrace : WordTrace (prefixWord ++ tailWord_10087) baseStart_10087 baseEnd_10087 := by
    simpa [prefixWord, tailWord_10087, baseEnd_10087] using wordTrace_append hprefix tailTrace_10087
  have hstable : (prefixWord ++ tailWord_10087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10087).length < 2 ^ (prefixWord ++ tailWord_10087).sum := by decide
  have hdescent : baseEnd_10087 < baseStart_10087 := by decide
  rcases family_descends (prefixWord ++ tailWord_10087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10102 : List Nat := [5, 1, 1, 3, 2, 1, 1, 5]
def baseStart_10102 : Nat := 118140960795 + 10102 * 2 ^ 59
def prefixEnd_10102 : Nat := 4983230072969 + 3 ^ 40 * 10102 * 2
def baseEnd_10102 : Nat := 3073885375896124194695

theorem tailTrace_10102 : CollatzResearch.WordTrace tailWord_10102 prefixEnd_10102 3073885375896124194695 := by
  unfold tailWord_10102
  simp only [CollatzResearch.WordTrace]
  refine ⟨23028138088103383084535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 245633472939769419568373 23028138088103383084535)
  ·
    refine ⟨34542207132155074626803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23028138088103383084535 34542207132155074626803)
    ·
      refine ⟨51813310698232611940205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34542207132155074626803 51813310698232611940205)
      ·
        refine ⟨19429991511837229477577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51813310698232611940205 19429991511837229477577)
        ·
          refine ⟨14572493633877922108183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19429991511837229477577 14572493633877922108183)
          ·
            refine ⟨21858740450816883162275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14572493633877922108183 21858740450816883162275)
            ·
              refine ⟨32788110676225324743413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21858740450816883162275 32788110676225324743413)
              ·
                refine ⟨3073885375896124194695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32788110676225324743413 3073885375896124194695)
                ·
                  rfl

theorem cell19_10102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_10102 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10102 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10102 prefixEnd_10102 := by exact prefixLift 10102
  have htrace : WordTrace (prefixWord ++ tailWord_10102) baseStart_10102 baseEnd_10102 := by
    simpa [prefixWord, tailWord_10102, baseEnd_10102] using wordTrace_append hprefix tailTrace_10102
  have hstable : (prefixWord ++ tailWord_10102).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10102).length < 2 ^ (prefixWord ++ tailWord_10102).sum := by decide
  have hdescent : baseEnd_10102 < baseStart_10102 := by decide
  rcases family_descends (prefixWord ++ tailWord_10102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10218 : List Nat := [3, 1, 3, 1, 2, 1, 5, 3]
def baseStart_10218 : Nat := 118140960795 + 10218 * 2 ^ 59
def prefixEnd_10218 : Nat := 4983230072969 + 3 ^ 40 * 10218 * 2
def baseEnd_10218 : Nat := 3109182416442225616601

theorem tailTrace_10218 : CollatzResearch.WordTrace tailWord_10218 prefixEnd_10218 3109182416442225616601 := by
  unfold tailWord_10218
  simp only [CollatzResearch.WordTrace]
  refine ⟨93170269247351485143827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 248454051326270627050205 93170269247351485143827)
  ·
    refine ⟨139755403871027227715741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93170269247351485143827 139755403871027227715741)
    ·
      refine ⟨52408276451635210393403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139755403871027227715741 52408276451635210393403)
      ·
        refine ⟨78612414677452815590105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52408276451635210393403 78612414677452815590105)
        ·
          refine ⟨58959311008089611692579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78612414677452815590105 58959311008089611692579)
          ·
            refine ⟨88438966512134417538869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58959311008089611692579 88438966512134417538869)
            ·
              refine ⟨8291153110512601644269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88438966512134417538869 8291153110512601644269)
              ·
                refine ⟨3109182416442225616601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8291153110512601644269 3109182416442225616601)
                ·
                  rfl

theorem cell19_10218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_10218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10218 prefixEnd_10218 := by exact prefixLift 10218
  have htrace : WordTrace (prefixWord ++ tailWord_10218) baseStart_10218 baseEnd_10218 := by
    simpa [prefixWord, tailWord_10218, baseEnd_10218] using wordTrace_append hprefix tailTrace_10218
  have hstable : (prefixWord ++ tailWord_10218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10218).length < 2 ^ (prefixWord ++ tailWord_10218).sum := by decide
  have hdescent : baseEnd_10218 < baseStart_10218 := by decide
  rcases family_descends (prefixWord ++ tailWord_10218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10273 : List Nat := [1, 2, 3, 2, 4, 2, 2, 3]
def baseStart_10273 : Nat := 118140960795 + 10273 * 2 ^ 59
def prefixEnd_10273 : Nat := 4983230072969 + 3 ^ 40 * 10273 * 2
def baseEnd_10273 : Nat := 3125918082218394394229

theorem tailTrace_10273 : CollatzResearch.WordTrace tailWord_10273 prefixEnd_10273 3125918082218394394229 := by
  unfold tailWord_10273
  simp only [CollatzResearch.WordTrace]
  refine ⟨374687091790150333827473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 249791394526766889218315 374687091790150333827473)
  ·
    refine ⟨281015318842612750370605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 374687091790150333827473 281015318842612750370605)
    ·
      refine ⟨105380744565979781388977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281015318842612750370605 105380744565979781388977)
      ·
        refine ⟨79035558424484836041733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105380744565979781388977 79035558424484836041733)
        ·
          refine ⟨14819167204590906757825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79035558424484836041733 14819167204590906757825)
          ·
            refine ⟨11114375403443180068369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14819167204590906757825 11114375403443180068369)
            ·
              refine ⟨8335781552582385051277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11114375403443180068369 8335781552582385051277)
              ·
                refine ⟨3125918082218394394229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8335781552582385051277 3125918082218394394229)
                ·
                  rfl

theorem cell19_10273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 3].length) (baseStart_10273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10273 prefixEnd_10273 := by exact prefixLift 10273
  have htrace : WordTrace (prefixWord ++ tailWord_10273) baseStart_10273 baseEnd_10273 := by
    simpa [prefixWord, tailWord_10273, baseEnd_10273] using wordTrace_append hprefix tailTrace_10273
  have hstable : (prefixWord ++ tailWord_10273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10273).length < 2 ^ (prefixWord ++ tailWord_10273).sum := by decide
  have hdescent : baseEnd_10273 < baseStart_10273 := by decide
  rcases family_descends (prefixWord ++ tailWord_10273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10277 : List Nat := [1, 3, 1, 2, 2, 4, 1, 5]
def baseStart_10277 : Nat := 118140960795 + 10277 * 2 ^ 59
def prefixEnd_10277 : Nat := 4983230072969 + 3 ^ 40 * 10277 * 2
def baseEnd_10277 : Nat := 3127135221547570305329

theorem tailTrace_10277 : CollatzResearch.WordTrace tailWord_10277 prefixEnd_10277 3127135221547570305329 := by
  unfold tailWord_10277
  simp only [CollatzResearch.WordTrace]
  refine ⟨374832983775659016973085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 249888655850439344648723 374832983775659016973085)
  ·
    refine ⟨140562368915872131364907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 374832983775659016973085 140562368915872131364907)
    ·
      refine ⟨210843553373808197047361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140562368915872131364907 210843553373808197047361)
      ·
        refine ⟨158132665030356147785521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210843553373808197047361 158132665030356147785521)
        ·
          refine ⟨118599498772767110839141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158132665030356147785521 118599498772767110839141)
          ·
            refine ⟨22237406019893833282339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118599498772767110839141 22237406019893833282339)
            ·
              refine ⟨33356109029840749923509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22237406019893833282339 33356109029840749923509)
              ·
                refine ⟨3127135221547570305329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33356109029840749923509 3127135221547570305329)
                ·
                  rfl

theorem cell19_10277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_10277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10277 prefixEnd_10277 := by exact prefixLift 10277
  have htrace : WordTrace (prefixWord ++ tailWord_10277) baseStart_10277 baseEnd_10277 := by
    simpa [prefixWord, tailWord_10277, baseEnd_10277] using wordTrace_append hprefix tailTrace_10277
  have hstable : (prefixWord ++ tailWord_10277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10277).length < 2 ^ (prefixWord ++ tailWord_10277).sum := by decide
  have hdescent : baseEnd_10277 < baseStart_10277 := by decide
  rcases family_descends (prefixWord ++ tailWord_10277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10292 : List Nat := [2, 5, 1, 2, 2, 2, 5]
def baseStart_10292 : Nat := 118140960795 + 10292 * 2 ^ 59
def prefixEnd_10292 : Nat := 4983230072969 + 3 ^ 40 * 10292 * 2
def baseEnd_10292 : Nat := 1043899831343993323985

theorem tailTrace_10292 : CollatzResearch.WordTrace tailWord_10292 prefixEnd_10292 1043899831343993323985 := by
  unfold tailWord_10292
  simp only [CollatzResearch.WordTrace]
  refine ⟨187690039360658289384565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 250253385814211052512753 187690039360658289384565)
  ·
    refine ⟨17595941190061714629803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187690039360658289384565 17595941190061714629803)
    ·
      refine ⟨26393911785092571944705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17595941190061714629803 26393911785092571944705)
      ·
        refine ⟨19795433838819428958529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26393911785092571944705 19795433838819428958529)
        ·
          refine ⟨14846575379114571718897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19795433838819428958529 14846575379114571718897)
          ·
            refine ⟨11134931534335928789173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14846575379114571718897 11134931534335928789173)
            ·
              refine ⟨1043899831343993323985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11134931534335928789173 1043899831343993323985)
              ·
                rfl

theorem cell19_10292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_10292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10292 prefixEnd_10292 := by exact prefixLift 10292
  have htrace : WordTrace (prefixWord ++ tailWord_10292) baseStart_10292 baseEnd_10292 := by
    simpa [prefixWord, tailWord_10292, baseEnd_10292] using wordTrace_append hprefix tailTrace_10292
  have hstable : (prefixWord ++ tailWord_10292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10292).length < 2 ^ (prefixWord ++ tailWord_10292).sum := by decide
  have hdescent : baseEnd_10292 < baseStart_10292 := by decide
  rcases family_descends (prefixWord ++ tailWord_10292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10393 : List Nat := [1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_10393 : Nat := 118140960795 + 10393 * 2 ^ 59
def prefixEnd_10393 : Nat := 4983230072969 + 3 ^ 40 * 10393 * 2
def baseEnd_10393 : Nat := 3162432262093671727235

theorem tailTrace_10393 : CollatzResearch.WordTrace tailWord_10393 prefixEnd_10393 3162432262093671727235 := by
  unfold tailWord_10393
  simp only [CollatzResearch.WordTrace]
  refine ⟨379063851355410828195833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 252709234236940552130555 379063851355410828195833)
  ·
    refine ⟨284297888516558121146875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 379063851355410828195833 284297888516558121146875)
    ·
      refine ⟨426446832774837181720313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284297888516558121146875 426446832774837181720313)
      ·
        refine ⟨319835124581127886290235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426446832774837181720313 319835124581127886290235)
        ·
          refine ⟨479752686871691829435353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319835124581127886290235 479752686871691829435353)
          ·
            refine ⟨359814515153768872076515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479752686871691829435353 359814515153768872076515)
            ·
              refine ⟨539721772730653308114773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359814515153768872076515 539721772730653308114773)
              ·
                refine ⟨3162432262093671727235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 539721772730653308114773 3162432262093671727235)
                ·
                  rfl

theorem cell19_10393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_10393 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10393 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10393 prefixEnd_10393 := by exact prefixLift 10393
  have htrace : WordTrace (prefixWord ++ tailWord_10393) baseStart_10393 baseEnd_10393 := by
    simpa [prefixWord, tailWord_10393, baseEnd_10393] using wordTrace_append hprefix tailTrace_10393
  have hstable : (prefixWord ++ tailWord_10393).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10393).length < 2 ^ (prefixWord ++ tailWord_10393).sum := by decide
  have hdescent : baseEnd_10393 < baseStart_10393 := by decide
  rcases family_descends (prefixWord ++ tailWord_10393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10431 : List Nat := [1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_10431 : Nat := 118140960795 + 10431 * 2 ^ 59
def prefixEnd_10431 : Nat := 4983230072969 + 3 ^ 40 * 10431 * 2
def baseEnd_10431 : Nat := 3173995085720842882687

theorem tailTrace_10431 : CollatzResearch.WordTrace tailWord_10431 prefixEnd_10431 3173995085720842882687 := by
  unfold tailWord_10431
  simp only [CollatzResearch.WordTrace]
  refine ⟨380449825217743318079147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 253633216811828878719431 380449825217743318079147)
  ·
    refine ⟨570674737826614977118721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 380449825217743318079147 570674737826614977118721)
    ·
      refine ⟨428006053369961232839041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 570674737826614977118721 428006053369961232839041)
      ·
        refine ⟨321004540027470924629281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428006053369961232839041 321004540027470924629281)
        ·
          refine ⟨240753405020603193471961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321004540027470924629281 240753405020603193471961)
          ·
            refine ⟨180565053765452395103971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240753405020603193471961 180565053765452395103971)
            ·
              refine ⟨270847580648178592655957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180565053765452395103971 270847580648178592655957)
              ·
                refine ⟨3173995085720842882687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 270847580648178592655957 3173995085720842882687)
                ·
                  rfl

theorem cell19_10431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_10431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10431 prefixEnd_10431 := by exact prefixLift 10431
  have htrace : WordTrace (prefixWord ++ tailWord_10431) baseStart_10431 baseEnd_10431 := by
    simpa [prefixWord, tailWord_10431, baseEnd_10431] using wordTrace_append hprefix tailTrace_10431
  have hstable : (prefixWord ++ tailWord_10431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10431).length < 2 ^ (prefixWord ++ tailWord_10431).sum := by decide
  have hdescent : baseEnd_10431 < baseStart_10431 := by decide
  rcases family_descends (prefixWord ++ tailWord_10431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10446 : List Nat := [4, 1, 1, 1, 4, 1, 4, 3]
def baseStart_10446 : Nat := 118140960795 + 10446 * 2 ^ 59
def prefixEnd_10446 : Nat := 4983230072969 + 3 ^ 40 * 10446 * 2
def baseEnd_10446 : Nat := 3178559358205252549313

theorem tailTrace_10446 : CollatzResearch.WordTrace tailWord_10446 prefixEnd_10446 3178559358205252549313 := by
  unfold tailWord_10446
  simp only [CollatzResearch.WordTrace]
  refine ⟨47624615020425109984399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 253997946775600586583461 47624615020425109984399)
  ·
    refine ⟨71436922530637664976599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47624615020425109984399 71436922530637664976599)
    ·
      refine ⟨107155383795956497464899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71436922530637664976599 107155383795956497464899)
      ·
        refine ⟨160733075693934746197349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107155383795956497464899 160733075693934746197349)
        ·
          refine ⟨30137451692612764912003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160733075693934746197349 30137451692612764912003)
          ·
            refine ⟨45206177538919147368005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30137451692612764912003 45206177538919147368005)
            ·
              refine ⟨8476158288547340131501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45206177538919147368005 8476158288547340131501)
              ·
                refine ⟨3178559358205252549313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8476158288547340131501 3178559358205252549313)
                ·
                  rfl

theorem cell19_10446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_10446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10446 prefixEnd_10446 := by exact prefixLift 10446
  have htrace : WordTrace (prefixWord ++ tailWord_10446) baseStart_10446 baseEnd_10446 := by
    simpa [prefixWord, tailWord_10446, baseEnd_10446] using wordTrace_append hprefix tailTrace_10446
  have hstable : (prefixWord ++ tailWord_10446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10446).length < 2 ^ (prefixWord ++ tailWord_10446).sum := by decide
  have hdescent : baseEnd_10446 < baseStart_10446 := by decide
  rcases family_descends (prefixWord ++ tailWord_10446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10486 : List Nat := [5, 1, 1, 1, 1, 1, 3, 6]
def baseStart_10486 : Nat := 118140960795 + 10486 * 2 ^ 59
def prefixEnd_10486 : Nat := 4983230072969 + 3 ^ 40 * 10486 * 2
def baseEnd_10486 : Nat := 3190730751497011660315

theorem tailTrace_10486 : CollatzResearch.WordTrace tailWord_10486 prefixEnd_10486 3190730751497011660315 := by
  unfold tailWord_10486
  simp only [CollatzResearch.WordTrace]
  refine ⟨23903490001155481958207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 254970560012325140887541 23903490001155481958207)
  ·
    refine ⟨35855235001733222937311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23903490001155481958207 35855235001733222937311)
    ·
      refine ⟨53782852502599834405967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35855235001733222937311 53782852502599834405967)
      ·
        refine ⟨80674278753899751608951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53782852502599834405967 80674278753899751608951)
        ·
          refine ⟨121011418130849627413427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80674278753899751608951 121011418130849627413427)
          ·
            refine ⟨181517127196274441120141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121011418130849627413427 181517127196274441120141)
            ·
              refine ⟨68068922698602915420053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181517127196274441120141 68068922698602915420053)
              ·
                refine ⟨3190730751497011660315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68068922698602915420053 3190730751497011660315)
                ·
                  rfl

theorem cell19_10486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_10486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10486 prefixEnd_10486 := by exact prefixLift 10486
  have htrace : WordTrace (prefixWord ++ tailWord_10486) baseStart_10486 baseEnd_10486 := by
    simpa [prefixWord, tailWord_10486, baseEnd_10486] using wordTrace_append hprefix tailTrace_10486
  have hstable : (prefixWord ++ tailWord_10486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10486).length < 2 ^ (prefixWord ++ tailWord_10486).sum := by decide
  have hdescent : baseEnd_10486 < baseStart_10486 := by decide
  rcases family_descends (prefixWord ++ tailWord_10486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10507 : List Nat := [1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_10507 : Nat := 118140960795 + 10507 * 2 ^ 59
def prefixEnd_10507 : Nat := 4983230072969 + 3 ^ 40 * 10507 * 2
def baseEnd_10507 : Nat := 3197120732975185193591

theorem tailTrace_10507 : CollatzResearch.WordTrace tailWord_10507 prefixEnd_10507 3197120732975185193591 := by
  unfold tailWord_10507
  simp only [CollatzResearch.WordTrace]
  refine ⟨383221772942408297845775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 255481181961605531897183 383221772942408297845775)
  ·
    refine ⟨574832659413612446768663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 383221772942408297845775 574832659413612446768663)
    ·
      refine ⟨862248989120418670152995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 574832659413612446768663 862248989120418670152995)
      ·
        refine ⟨1293373483680628005229493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862248989120418670152995 1293373483680628005229493)
        ·
          refine ⟨121253764095058875490265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1293373483680628005229493 121253764095058875490265)
          ·
            refine ⟨90940323071294156617699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121253764095058875490265 90940323071294156617699)
            ·
              refine ⟨136410484606941234926549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90940323071294156617699 136410484606941234926549)
              ·
                refine ⟨3197120732975185193591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 136410484606941234926549 3197120732975185193591)
                ·
                  rfl

theorem cell19_10507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_10507 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10507 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10507 prefixEnd_10507 := by exact prefixLift 10507
  have htrace : WordTrace (prefixWord ++ tailWord_10507) baseStart_10507 baseEnd_10507 := by
    simpa [prefixWord, tailWord_10507, baseEnd_10507] using wordTrace_append hprefix tailTrace_10507
  have hstable : (prefixWord ++ tailWord_10507).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10507).length < 2 ^ (prefixWord ++ tailWord_10507).sum := by decide
  have hdescent : baseEnd_10507 < baseStart_10507 := by decide
  rcases family_descends (prefixWord ++ tailWord_10507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10535 : List Nat := [1, 1, 8, 1, 2, 1, 1, 4]
def baseStart_10535 : Nat := 118140960795 + 10535 * 2 ^ 59
def prefixEnd_10535 : Nat := 4983230072969 + 3 ^ 40 * 10535 * 2
def baseEnd_10535 : Nat := 3205640708279416571293

theorem tailTrace_10535 : CollatzResearch.WordTrace tailWord_10535 prefixEnd_10535 3205640708279416571293 := by
  unfold tailWord_10535
  simp only [CollatzResearch.WordTrace]
  refine ⟨384243016840969079865059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 256162011227312719910039 384243016840969079865059)
  ·
    refine ⟨576364525261453619797589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384243016840969079865059 576364525261453619797589)
    ·
      refine ⟨6754271780407659607003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 576364525261453619797589 6754271780407659607003)
      ·
        refine ⟨10131407670611489410505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6754271780407659607003 10131407670611489410505)
        ·
          refine ⟨7598555752958617057879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10131407670611489410505 7598555752958617057879)
          ·
            refine ⟨11397833629437925586819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7598555752958617057879 11397833629437925586819)
            ·
              refine ⟨17096750444156888380229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11397833629437925586819 17096750444156888380229)
              ·
                refine ⟨3205640708279416571293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17096750444156888380229 3205640708279416571293)
                ·
                  rfl

theorem cell19_10535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 4].length) (baseStart_10535 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10535 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10535 prefixEnd_10535 := by exact prefixLift 10535
  have htrace : WordTrace (prefixWord ++ tailWord_10535) baseStart_10535 baseEnd_10535 := by
    simpa [prefixWord, tailWord_10535, baseEnd_10535] using wordTrace_append hprefix tailTrace_10535
  have hstable : (prefixWord ++ tailWord_10535).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10535).length < 2 ^ (prefixWord ++ tailWord_10535).sum := by decide
  have hdescent : baseEnd_10535 < baseStart_10535 := by decide
  rcases family_descends (prefixWord ++ tailWord_10535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10581 : List Nat := [1, 3, 2, 2, 4, 1, 6]
def baseStart_10581 : Nat := 118140960795 + 10581 * 2 ^ 59
def prefixEnd_10581 : Nat := 4983230072969 + 3 ^ 40 * 10581 * 2
def baseEnd_10581 : Nat := 1073212603521646516315

theorem tailTrace_10581 : CollatzResearch.WordTrace tailWord_10581 prefixEnd_10581 1073212603521646516315 := by
  unfold tailWord_10581
  simp only [CollatzResearch.WordTrace]
  refine ⟨385920774674318936039597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 257280516449545957359731 385920774674318936039597)
  ·
    refine ⟨144720290502869601014849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 385920774674318936039597 144720290502869601014849)
    ·
      refine ⟨108540217877152200761137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144720290502869601014849 108540217877152200761137)
      ·
        refine ⟨81405163407864150570853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108540217877152200761137 81405163407864150570853)
        ·
          refine ⟨15263468138974528232035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81405163407864150570853 15263468138974528232035)
          ·
            refine ⟨22895202208461792348053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15263468138974528232035 22895202208461792348053)
            ·
              refine ⟨1073212603521646516315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22895202208461792348053 1073212603521646516315)
              ·
                rfl

theorem cell19_10581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_10581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10581 prefixEnd_10581 := by exact prefixLift 10581
  have htrace : WordTrace (prefixWord ++ tailWord_10581) baseStart_10581 baseEnd_10581 := by
    simpa [prefixWord, tailWord_10581, baseEnd_10581] using wordTrace_append hprefix tailTrace_10581
  have hstable : (prefixWord ++ tailWord_10581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10581).length < 2 ^ (prefixWord ++ tailWord_10581).sum := by decide
  have hdescent : baseEnd_10581 < baseStart_10581 := by decide
  rcases family_descends (prefixWord ++ tailWord_10581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10583 : List Nat := [1, 1, 3, 2, 3, 1, 8]
def baseStart_10583 : Nat := 118140960795 + 10583 * 2 ^ 59
def prefixEnd_10583 : Nat := 4983230072969 + 3 ^ 40 * 10583 * 2
def baseEnd_10583 : Nat := 1073415460076509168165

theorem tailTrace_10583 : CollatzResearch.WordTrace tailWord_10583 prefixEnd_10583 1073415460076509168165 := by
  unfold tailWord_10583
  simp only [CollatzResearch.WordTrace]
  refine ⟨385993720667073277612403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 257329147111382185074935 385993720667073277612403)
  ·
    refine ⟨578990581000609916418605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 385993720667073277612403 578990581000609916418605)
    ·
      refine ⟨217121467875228718656977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 578990581000609916418605 217121467875228718656977)
      ·
        refine ⟨162841100906421538992733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217121467875228718656977 162841100906421538992733)
        ·
          refine ⟨61065412839908077122275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162841100906421538992733 61065412839908077122275)
          ·
            refine ⟨91598119259862115683413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61065412839908077122275 91598119259862115683413)
            ·
              refine ⟨1073415460076509168165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 91598119259862115683413 1073415460076509168165)
              ·
                rfl

theorem cell19_10583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_10583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10583 prefixEnd_10583 := by exact prefixLift 10583
  have htrace : WordTrace (prefixWord ++ tailWord_10583) baseStart_10583 baseEnd_10583 := by
    simpa [prefixWord, tailWord_10583, baseEnd_10583] using wordTrace_append hprefix tailTrace_10583
  have hstable : (prefixWord ++ tailWord_10583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10583).length < 2 ^ (prefixWord ++ tailWord_10583).sum := by decide
  have hdescent : baseEnd_10583 < baseStart_10583 := by decide
  rcases family_descends (prefixWord ++ tailWord_10583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10619 : List Nat := [1, 1, 1, 1, 1, 7, 4, 3]
def baseStart_10619 : Nat := 118140960795 + 10619 * 2 ^ 59
def prefixEnd_10619 : Nat := 4983230072969 + 3 ^ 40 * 10619 * 2
def baseEnd_10619 : Nat := 3231200634192110704397

theorem tailTrace_10619 : CollatzResearch.WordTrace tailWord_10619 prefixEnd_10619 3231200634192110704397 := by
  unfold tailWord_10619
  simp only [CollatzResearch.WordTrace]
  refine ⟨387306748536651425922911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 258204499024434283948607 387306748536651425922911)
  ·
    refine ⟨580960122804977138884367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 387306748536651425922911 580960122804977138884367)
    ·
      refine ⟨871440184207465708326551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 580960122804977138884367 871440184207465708326551)
      ·
        refine ⟨1307160276311198562489827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871440184207465708326551 1307160276311198562489827)
        ·
          refine ⟨1960740414466797843734741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1307160276311198562489827 1960740414466797843734741)
          ·
            refine ⟨45954853464065574462533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1960740414466797843734741 45954853464065574462533)
            ·
              refine ⟨8616535024512295211725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45954853464065574462533 8616535024512295211725)
              ·
                refine ⟨3231200634192110704397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8616535024512295211725 3231200634192110704397)
                ·
                  rfl

theorem cell19_10619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 3].length) (baseStart_10619 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10619 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10619 prefixEnd_10619 := by exact prefixLift 10619
  have htrace : WordTrace (prefixWord ++ tailWord_10619) baseStart_10619 baseEnd_10619 := by
    simpa [prefixWord, tailWord_10619, baseEnd_10619] using wordTrace_append hprefix tailTrace_10619
  have hstable : (prefixWord ++ tailWord_10619).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10619).length < 2 ^ (prefixWord ++ tailWord_10619).sum := by decide
  have hdescent : baseEnd_10619 < baseStart_10619 := by decide
  rcases family_descends (prefixWord ++ tailWord_10619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10634 : List Nat := [3, 1, 2, 5, 2, 1, 5]
def baseStart_10634 : Nat := 118140960795 + 10634 * 2 ^ 59
def prefixEnd_10634 : Nat := 4983230072969 + 3 ^ 40 * 10634 * 2
def baseEnd_10634 : Nat := 1078588302225506790341

theorem tailTrace_10634 : CollatzResearch.WordTrace tailWord_10634 prefixEnd_10634 1078588302225506790341 := by
  unfold tailWord_10634
  simp only [CollatzResearch.WordTrace]
  refine ⟨96963460870577246929739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 258569228988205991812637 96963460870577246929739)
  ·
    refine ⟨145445191305865870394609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96963460870577246929739 145445191305865870394609)
    ·
      refine ⟨109083893479399402795957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145445191305865870394609 109083893479399402795957)
      ·
        refine ⟨10226615013693694012121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109083893479399402795957 10226615013693694012121)
        ·
          refine ⟨7669961260270270509091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10226615013693694012121 7669961260270270509091)
          ·
            refine ⟨11504941890405405763637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669961260270270509091 11504941890405405763637)
            ·
              refine ⟨1078588302225506790341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11504941890405405763637 1078588302225506790341)
              ·
                rfl

theorem cell19_10634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 5].length) (baseStart_10634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10634 prefixEnd_10634 := by exact prefixLift 10634
  have htrace : WordTrace (prefixWord ++ tailWord_10634) baseStart_10634 baseEnd_10634 := by
    simpa [prefixWord, tailWord_10634, baseEnd_10634] using wordTrace_append hprefix tailTrace_10634
  have hstable : (prefixWord ++ tailWord_10634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10634).length < 2 ^ (prefixWord ++ tailWord_10634).sum := by decide
  have hdescent : baseEnd_10634 < baseStart_10634 := by decide
  rcases family_descends (prefixWord ++ tailWord_10634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10638 : List Nat := [4, 1, 1, 4, 1, 1, 7]
def baseStart_10638 : Nat := 118140960795 + 10638 * 2 ^ 59
def prefixEnd_10638 : Nat := 4983230072969 + 3 ^ 40 * 10638 * 2
def baseEnd_10638 : Nat := 1078994015335232094041

theorem tailTrace_10638 : CollatzResearch.WordTrace tailWord_10638 prefixEnd_10638 1078994015335232094041 := by
  unfold tailWord_10638
  simp only [CollatzResearch.WordTrace]
  refine ⟨48499966933477208858071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 258666490311878447243045 48499966933477208858071)
  ·
    refine ⟨72749950400215813287107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48499966933477208858071 72749950400215813287107)
    ·
      refine ⟨109124925600323719930661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72749950400215813287107 109124925600323719930661)
      ·
        refine ⟨20460923550060697486999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109124925600323719930661 20460923550060697486999)
        ·
          refine ⟨30691385325091046230499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20460923550060697486999 30691385325091046230499)
          ·
            refine ⟨46037077987636569345749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30691385325091046230499 46037077987636569345749)
            ·
              refine ⟨1078994015335232094041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46037077987636569345749 1078994015335232094041)
              ·
                rfl

theorem cell19_10638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_10638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10638 prefixEnd_10638 := by exact prefixLift 10638
  have htrace : WordTrace (prefixWord ++ tailWord_10638) baseStart_10638 baseEnd_10638 := by
    simpa [prefixWord, tailWord_10638, baseEnd_10638] using wordTrace_append hprefix tailTrace_10638
  have hstable : (prefixWord ++ tailWord_10638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10638).length < 2 ^ (prefixWord ++ tailWord_10638).sum := by decide
  have hdescent : baseEnd_10638 < baseStart_10638 := by decide
  rcases family_descends (prefixWord ++ tailWord_10638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10659 : List Nat := [1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_10659 : Nat := 118140960795 + 10659 * 2 ^ 59
def prefixEnd_10659 : Nat := 4983230072969 + 3 ^ 40 * 10659 * 2
def baseEnd_10659 : Nat := 3243372027483869815399

theorem tailTrace_10659 : CollatzResearch.WordTrace tailWord_10659 prefixEnd_10659 3243372027483869815399 := by
  unfold tailWord_10659
  simp only [CollatzResearch.WordTrace]
  refine ⟨388765668391738257379031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 259177112261158838252687 388765668391738257379031)
  ·
    refine ⟨583148502587607386068547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 388765668391738257379031 583148502587607386068547)
    ·
      refine ⟨874722753881411079102821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 583148502587607386068547 874722753881411079102821)
      ·
        refine ⟨164010516352764577331779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 874722753881411079102821 164010516352764577331779)
        ·
          refine ⟨246015774529146865997669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164010516352764577331779 246015774529146865997669)
          ·
            refine ⟨46127957724215037374563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246015774529146865997669 46127957724215037374563)
            ·
              refine ⟨69191936586322556061845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46127957724215037374563 69191936586322556061845)
              ·
                refine ⟨3243372027483869815399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69191936586322556061845 3243372027483869815399)
                ·
                  rfl

theorem cell19_10659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_10659 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10659 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10659 prefixEnd_10659 := by exact prefixLift 10659
  have htrace : WordTrace (prefixWord ++ tailWord_10659) baseStart_10659 baseEnd_10659 := by
    simpa [prefixWord, tailWord_10659, baseEnd_10659] using wordTrace_append hprefix tailTrace_10659
  have hstable : (prefixWord ++ tailWord_10659).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10659).length < 2 ^ (prefixWord ++ tailWord_10659).sum := by decide
  have hdescent : baseEnd_10659 < baseStart_10659 := by decide
  rcases family_descends (prefixWord ++ tailWord_10659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10773 : List Nat := [1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_10773 : Nat := 118140960795 + 10773 * 2 ^ 59
def prefixEnd_10773 : Nat := 4983230072969 + 3 ^ 40 * 10773 * 2
def baseEnd_10773 : Nat := 3278060498365383281755

theorem tailTrace_10773 : CollatzResearch.WordTrace tailWord_10773 prefixEnd_10773 3278060498365383281755 := by
  unfold tailWord_10773
  simp only [CollatzResearch.WordTrace]
  refine ⟨392923589978735727028973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 261949059985823818019315 392923589978735727028973)
  ·
    refine ⟨147346346242025897635865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 392923589978735727028973 147346346242025897635865)
    ·
      refine ⟨110509759681519423226899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147346346242025897635865 110509759681519423226899)
      ·
        refine ⟨165764639522279134840349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110509759681519423226899 165764639522279134840349)
        ·
          refine ⟨62161739820854675565131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165764639522279134840349 62161739820854675565131)
          ·
            refine ⟨93242609731282013347697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62161739820854675565131 93242609731282013347697)
            ·
              refine ⟨69931957298461510010773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93242609731282013347697 69931957298461510010773)
              ·
                refine ⟨3278060498365383281755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69931957298461510010773 3278060498365383281755)
                ·
                  rfl

theorem cell19_10773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_10773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10773 prefixEnd_10773 := by exact prefixLift 10773
  have htrace : WordTrace (prefixWord ++ tailWord_10773) baseStart_10773 baseEnd_10773 := by
    simpa [prefixWord, tailWord_10773, baseEnd_10773] using wordTrace_append hprefix tailTrace_10773
  have hstable : (prefixWord ++ tailWord_10773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10773).length < 2 ^ (prefixWord ++ tailWord_10773).sum := by decide
  have hdescent : baseEnd_10773 < baseStart_10773 := by decide
  rcases family_descends (prefixWord ++ tailWord_10773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10788 : List Nat := [2, 3, 1, 5, 1, 1, 1, 5]
def baseStart_10788 : Nat := 118140960795 + 10788 * 2 ^ 59
def prefixEnd_10788 : Nat := 4983230072969 + 3 ^ 40 * 10788 * 2
def baseEnd_10788 : Nat := 3282624770849792948381

theorem tailTrace_10788 : CollatzResearch.WordTrace tailWord_10788 prefixEnd_10788 3282624770849792948381 := by
  unfold tailWord_10788
  simp only [CollatzResearch.WordTrace]
  refine ⟨196735342462196644412509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 262313789949595525883345 196735342462196644412509)
  ·
    refine ⟨73775753423323741654691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 196735342462196644412509 73775753423323741654691)
    ·
      refine ⟨110663630134985612482037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73775753423323741654691 110663630134985612482037)
      ·
        refine ⟨10374715325154901170191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110663630134985612482037 10374715325154901170191)
        ·
          refine ⟨15562072987732351755287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10374715325154901170191 15562072987732351755287)
          ·
            refine ⟨23343109481598527632931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15562072987732351755287 23343109481598527632931)
            ·
              refine ⟨35014664222397791449397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23343109481598527632931 35014664222397791449397)
              ·
                refine ⟨3282624770849792948381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35014664222397791449397 3282624770849792948381)
                ·
                  rfl

theorem cell19_10788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_10788 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10788 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10788 prefixEnd_10788 := by exact prefixLift 10788
  have htrace : WordTrace (prefixWord ++ tailWord_10788) baseStart_10788 baseEnd_10788 := by
    simpa [prefixWord, tailWord_10788, baseEnd_10788] using wordTrace_append hprefix tailTrace_10788
  have hstable : (prefixWord ++ tailWord_10788).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10788).length < 2 ^ (prefixWord ++ tailWord_10788).sum := by decide
  have hdescent : baseEnd_10788 < baseStart_10788 := by decide
  rcases family_descends (prefixWord ++ tailWord_10788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10830 : List Nat := [4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_10830 : Nat := 118140960795 + 10830 * 2 ^ 59
def prefixEnd_10830 : Nat := 4983230072969 + 3 ^ 40 * 10830 * 2
def baseEnd_10830 : Nat := 3295404733806140014933

theorem tailTrace_10830 : CollatzResearch.WordTrace tailWord_10830 prefixEnd_10830 3295404733806140014933 := by
  unfold tailWord_10830
  simp only [CollatzResearch.WordTrace]
  refine ⟨49375318846529307731743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 263335033848156307902629 49375318846529307731743)
  ·
    refine ⟨74062978269793961597615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49375318846529307731743 74062978269793961597615)
    ·
      refine ⟨111094467404690942396423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74062978269793961597615 111094467404690942396423)
      ·
        refine ⟨166641701107036413594635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111094467404690942396423 166641701107036413594635)
        ·
          refine ⟨249962551660554620391953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166641701107036413594635 249962551660554620391953)
          ·
            refine ⟨187471913745415965293965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249962551660554620391953 187471913745415965293965)
            ·
              refine ⟨70301967654530986985237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187471913745415965293965 70301967654530986985237)
              ·
                refine ⟨3295404733806140014933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70301967654530986985237 3295404733806140014933)
                ·
                  rfl

theorem cell19_10830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_10830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10830 prefixEnd_10830 := by exact prefixLift 10830
  have htrace : WordTrace (prefixWord ++ tailWord_10830) baseStart_10830 baseEnd_10830 := by
    simpa [prefixWord, tailWord_10830, baseEnd_10830] using wordTrace_append hprefix tailTrace_10830
  have hstable : (prefixWord ++ tailWord_10830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10830).length < 2 ^ (prefixWord ++ tailWord_10830).sum := by decide
  have hdescent : baseEnd_10830 < baseStart_10830 := by decide
  rcases family_descends (prefixWord ++ tailWord_10830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10849 : List Nat := [1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_10849 : Nat := 118140960795 + 10849 * 2 ^ 59
def prefixEnd_10849 : Nat := 4983230072969 + 3 ^ 40 * 10849 * 2
def baseEnd_10849 : Nat := 3301186145619725592659

theorem tailTrace_10849 : CollatzResearch.WordTrace tailWord_10849 prefixEnd_10849 3301186145619725592659 := by
  unfold tailWord_10849
  simp only [CollatzResearch.WordTrace]
  refine ⟨395695537703400706795601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 263797025135600471197067 395695537703400706795601)
  ·
    refine ⟨296771653277550530096701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 395695537703400706795601 296771653277550530096701)
    ·
      refine ⟨111289369979081448786263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 296771653277550530096701 111289369979081448786263)
      ·
        refine ⟨166934054968622173179395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111289369979081448786263 166934054968622173179395)
        ·
          refine ⟨250401082452933259769093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166934054968622173179395 250401082452933259769093)
          ·
            refine ⟨46950202959924986206705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250401082452933259769093 46950202959924986206705)
            ·
              refine ⟨35212652219943739655029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46950202959924986206705 35212652219943739655029)
              ·
                refine ⟨3301186145619725592659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35212652219943739655029 3301186145619725592659)
                ·
                  rfl

theorem cell19_10849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_10849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10849 prefixEnd_10849 := by exact prefixLift 10849
  have htrace : WordTrace (prefixWord ++ tailWord_10849) baseStart_10849 baseEnd_10849 := by
    simpa [prefixWord, tailWord_10849, baseEnd_10849] using wordTrace_append hprefix tailTrace_10849
  have hstable : (prefixWord ++ tailWord_10849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10849).length < 2 ^ (prefixWord ++ tailWord_10849).sum := by decide
  have hdescent : baseEnd_10849 < baseStart_10849 := by decide
  rcases family_descends (prefixWord ++ tailWord_10849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10866 : List Nat := [3, 2, 1, 2, 5, 6]
def baseStart_10866 : Nat := 118140960795 + 10866 * 2 ^ 59
def prefixEnd_10866 : Nat := 4983230072969 + 3 ^ 40 * 10866 * 2
def baseEnd_10866 : Nat := 367373220863191468315

theorem tailTrace_10866 : CollatzResearch.WordTrace tailWord_10866 prefixEnd_10866 367373220863191468315 := by
  unfold tailWord_10866
  simp only [CollatzResearch.WordTrace]
  refine ⟨99078894660453152541113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 264210385761208406776301 99078894660453152541113)
  ·
    refine ⟨74309170995339864405835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99078894660453152541113 74309170995339864405835)
    ·
      refine ⟨111463756493009796608753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74309170995339864405835 111463756493009796608753)
      ·
        refine ⟨83597817369757347456565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111463756493009796608753 83597817369757347456565)
        ·
          refine ⟨7837295378414751324053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83597817369757347456565 7837295378414751324053)
          ·
            refine ⟨367373220863191468315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7837295378414751324053 367373220863191468315)
            ·
              rfl

theorem cell19_10866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 6].length) (baseStart_10866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10866 prefixEnd_10866 := by exact prefixLift 10866
  have htrace : WordTrace (prefixWord ++ tailWord_10866) baseStart_10866 baseEnd_10866 := by
    simpa [prefixWord, tailWord_10866, baseEnd_10866] using wordTrace_append hprefix tailTrace_10866
  have hstable : (prefixWord ++ tailWord_10866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10866).length < 2 ^ (prefixWord ++ tailWord_10866).sum := by decide
  have hdescent : baseEnd_10866 < baseStart_10866 := by decide
  rcases family_descends (prefixWord ++ tailWord_10866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10885 : List Nat := [1, 3, 1, 1, 4, 4, 1, 4]
def baseStart_10885 : Nat := 118140960795 + 10885 * 2 ^ 59
def prefixEnd_10885 : Nat := 4983230072969 + 3 ^ 40 * 10885 * 2
def baseEnd_10885 : Nat := 3312140399582308792561

theorem tailTrace_10885 : CollatzResearch.WordTrace tailWord_10885 prefixEnd_10885 3312140399582308792561 := by
  unfold tailWord_10885
  simp only [CollatzResearch.WordTrace]
  refine ⟨397008565572978855106109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 264672377048652570070739 397008565572978855106109)
  ·
    refine ⟨148878212089867070664791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 397008565572978855106109 148878212089867070664791)
    ·
      refine ⟨223317318134800605997187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148878212089867070664791 223317318134800605997187)
      ·
        refine ⟨334975977202200908995781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223317318134800605997187 334975977202200908995781)
        ·
          refine ⟨62807995725412670436709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 334975977202200908995781 62807995725412670436709)
          ·
            refine ⟨11776499198514875706883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62807995725412670436709 11776499198514875706883)
            ·
              refine ⟨17664748797772313560325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11776499198514875706883 17664748797772313560325)
              ·
                refine ⟨3312140399582308792561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17664748797772313560325 3312140399582308792561)
                ·
                  rfl

theorem cell19_10885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_10885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10885 prefixEnd_10885 := by exact prefixLift 10885
  have htrace : WordTrace (prefixWord ++ tailWord_10885) baseStart_10885 baseEnd_10885 := by
    simpa [prefixWord, tailWord_10885, baseEnd_10885] using wordTrace_append hprefix tailTrace_10885
  have hstable : (prefixWord ++ tailWord_10885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10885).length < 2 ^ (prefixWord ++ tailWord_10885).sum := by decide
  have hdescent : baseEnd_10885 < baseStart_10885 := by decide
  rcases family_descends (prefixWord ++ tailWord_10885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_10904 : List Nat := [2, 1, 2, 4, 1, 1, 5, 3]
def baseStart_10904 : Nat := 118140960795 + 10904 * 2 ^ 59
def prefixEnd_10904 : Nat := 4983230072969 + 3 ^ 40 * 10904 * 2
def baseEnd_10904 : Nat := 3317921811395894370287

theorem tailTrace_10904 : CollatzResearch.WordTrace tailWord_10904 prefixEnd_10904 3317921811395894370287 := by
  unfold tailWord_10904
  simp only [CollatzResearch.WordTrace]
  refine ⟨198850776252072550023883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 265134368336096733365177 198850776252072550023883)
  ·
    refine ⟨298276164378108825035825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198850776252072550023883 298276164378108825035825)
    ·
      refine ⟨223707123283581618776869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298276164378108825035825 223707123283581618776869)
      ·
        refine ⟨41945085615671553520663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223707123283581618776869 41945085615671553520663)
        ·
          refine ⟨62917628423507330280995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41945085615671553520663 62917628423507330280995)
          ·
            refine ⟨94376442635260995421493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62917628423507330280995 94376442635260995421493)
            ·
              refine ⟨8847791497055718320765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94376442635260995421493 8847791497055718320765)
              ·
                refine ⟨3317921811395894370287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8847791497055718320765 3317921811395894370287)
                ·
                  rfl

theorem cell19_10904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_10904 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_10904 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_10904 prefixEnd_10904 := by exact prefixLift 10904
  have htrace : WordTrace (prefixWord ++ tailWord_10904) baseStart_10904 baseEnd_10904 := by
    simpa [prefixWord, tailWord_10904, baseEnd_10904] using wordTrace_append hprefix tailTrace_10904
  have hstable : (prefixWord ++ tailWord_10904).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_10904).length < 2 ^ (prefixWord ++ tailWord_10904).sum := by decide
  have hdescent : baseEnd_10904 < baseStart_10904 := by decide
  rcases family_descends (prefixWord ++ tailWord_10904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11037 : List Nat := [1, 4, 2, 4, 1, 7]
def baseStart_11037 : Nat := 118140960795 + 11037 * 2 ^ 59
def prefixEnd_11037 : Nat := 4983230072969 + 3 ^ 40 * 11037 * 2
def baseEnd_11037 : Nat := 373154632676777046041

theorem tailTrace_11037 : CollatzResearch.WordTrace tailWord_11037 prefixEnd_11037 373154632676777046041 := by
  unfold tailWord_11037
  simp only [CollatzResearch.WordTrace]
  refine ⟨402552461022308814639365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 268368307348205876426243 402552461022308814639365)
  ·
    refine ⟨75478586441682902744881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 402552461022308814639365 75478586441682902744881)
    ·
      refine ⟨56608939831262177058661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75478586441682902744881 56608939831262177058661)
      ·
        refine ⟨10614176218361658198499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56608939831262177058661 10614176218361658198499)
        ·
          refine ⟨15921264327542487297749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10614176218361658198499 15921264327542487297749)
          ·
            refine ⟨373154632676777046041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15921264327542487297749 373154632676777046041)
            ·
              rfl

theorem cell19_11037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 7].length) (baseStart_11037 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11037 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11037 prefixEnd_11037 := by exact prefixLift 11037
  have htrace : WordTrace (prefixWord ++ tailWord_11037) baseStart_11037 baseEnd_11037 := by
    simpa [prefixWord, tailWord_11037, baseEnd_11037] using wordTrace_append hprefix tailTrace_11037
  have hstable : (prefixWord ++ tailWord_11037).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11037).length < 2 ^ (prefixWord ++ tailWord_11037).sum := by decide
  have hdescent : baseEnd_11037 < baseStart_11037 := by decide
  rcases family_descends (prefixWord ++ tailWord_11037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11054 : List Nat := [4, 1, 3, 2, 1, 3, 1, 4]
def baseStart_11054 : Nat := 118140960795 + 11054 * 2 ^ 59
def prefixEnd_11054 : Nat := 4983230072969 + 3 ^ 40 * 11054 * 2
def baseEnd_11054 : Nat := 3363564536239991036545

theorem tailTrace_11054 : CollatzResearch.WordTrace tailWord_11054 prefixEnd_11054 3363564536239991036545 := by
  unfold tailWord_11054
  simp only [CollatzResearch.WordTrace]
  refine ⟨50396562745090089751027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 268781667973813812005477 50396562745090089751027)
  ·
    refine ⟨75594844117635134626541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50396562745090089751027 75594844117635134626541)
    ·
      refine ⟨28348066544113175484953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75594844117635134626541 28348066544113175484953)
      ·
        refine ⟨21261049908084881613715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28348066544113175484953 21261049908084881613715)
        ·
          refine ⟨31891574862127322420573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21261049908084881613715 31891574862127322420573)
          ·
            refine ⟨11959340573297745907715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31891574862127322420573 11959340573297745907715)
            ·
              refine ⟨17939010859946618861573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11959340573297745907715 17939010859946618861573)
              ·
                refine ⟨3363564536239991036545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17939010859946618861573 3363564536239991036545)
                ·
                  rfl

theorem cell19_11054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_11054 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11054 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11054 prefixEnd_11054 := by exact prefixLift 11054
  have htrace : WordTrace (prefixWord ++ tailWord_11054) baseStart_11054 baseEnd_11054 := by
    simpa [prefixWord, tailWord_11054, baseEnd_11054] using wordTrace_append hprefix tailTrace_11054
  have hstable : (prefixWord ++ tailWord_11054).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11054).length < 2 ^ (prefixWord ++ tailWord_11054).sum := by decide
  have hdescent : baseEnd_11054 < baseStart_11054 := by decide
  rcases family_descends (prefixWord ++ tailWord_11054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11170 : List Nat := [3, 3, 1, 2, 2, 2, 2, 4]
def baseStart_11170 : Nat := 118140960795 + 11170 * 2 ^ 59
def prefixEnd_11170 : Nat := 4983230072969 + 3 ^ 40 * 11170 * 2
def baseEnd_11170 : Nat := 3398861576786092458451

theorem tailTrace_11170 : CollatzResearch.WordTrace tailWord_11170 prefixEnd_11170 3398861576786092458451 := by
  unfold tailWord_11170
  simp only [CollatzResearch.WordTrace]
  refine ⟨101850842385118132307741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 271602246360315019487309 101850842385118132307741)
  ·
    refine ⟨38194065894419299615403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101850842385118132307741 38194065894419299615403)
    ·
      refine ⟨57291098841628949423105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38194065894419299615403 57291098841628949423105)
      ·
        refine ⟨42968324131221712067329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57291098841628949423105 42968324131221712067329)
        ·
          refine ⟨32226243098416284050497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42968324131221712067329 32226243098416284050497)
          ·
            refine ⟨24169682323812213037873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32226243098416284050497 24169682323812213037873)
            ·
              refine ⟨18127261742859159778405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24169682323812213037873 18127261742859159778405)
              ·
                refine ⟨3398861576786092458451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18127261742859159778405 3398861576786092458451)
                ·
                  rfl

theorem cell19_11170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_11170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11170 prefixEnd_11170 := by exact prefixLift 11170
  have htrace : WordTrace (prefixWord ++ tailWord_11170) baseStart_11170 baseEnd_11170 := by
    simpa [prefixWord, tailWord_11170, baseEnd_11170] using wordTrace_append hprefix tailTrace_11170
  have hstable : (prefixWord ++ tailWord_11170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11170).length < 2 ^ (prefixWord ++ tailWord_11170).sum := by decide
  have hdescent : baseEnd_11170 < baseStart_11170 := by decide
  rcases family_descends (prefixWord ++ tailWord_11170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11172 : List Nat := [2, 3, 1, 2, 1, 2, 4, 4]
def baseStart_11172 : Nat := 118140960795 + 11172 * 2 ^ 59
def prefixEnd_11172 : Nat := 4983230072969 + 3 ^ 40 * 11172 * 2
def baseEnd_11172 : Nat := 3399470146450680414001

theorem tailTrace_11172 : CollatzResearch.WordTrace tailWord_11172 prefixEnd_11172 3399470146450680414001 := by
  unfold tailWord_11172
  simp only [CollatzResearch.WordTrace]
  refine ⟨203738157766613435401885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 271650877022151247202513 203738157766613435401885)
  ·
    refine ⟨76401809162480038275707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 203738157766613435401885 76401809162480038275707)
    ·
      refine ⟨114602713743720057413561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76401809162480038275707 114602713743720057413561)
      ·
        refine ⟨85952035307790043060171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114602713743720057413561 85952035307790043060171)
        ·
          refine ⟨128928052961685064590257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85952035307790043060171 128928052961685064590257)
          ·
            refine ⟨96696039721263798442693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128928052961685064590257 96696039721263798442693)
            ·
              refine ⟨18130507447736962208005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96696039721263798442693 18130507447736962208005)
              ·
                refine ⟨3399470146450680414001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18130507447736962208005 3399470146450680414001)
                ·
                  rfl

theorem cell19_11172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_11172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11172 prefixEnd_11172 := by exact prefixLift 11172
  have htrace : WordTrace (prefixWord ++ tailWord_11172) baseStart_11172 baseEnd_11172 := by
    simpa [prefixWord, tailWord_11172, baseEnd_11172] using wordTrace_append hprefix tailTrace_11172
  have hstable : (prefixWord ++ tailWord_11172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11172).length < 2 ^ (prefixWord ++ tailWord_11172).sum := by decide
  have hdescent : baseEnd_11172 < baseStart_11172 := by decide
  rcases family_descends (prefixWord ++ tailWord_11172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11269 : List Nat := [1, 3, 1, 1, 2, 3, 8]
def baseStart_11269 : Nat := 118140960795 + 11269 * 2 ^ 59
def prefixEnd_11269 : Nat := 4983230072969 + 3 ^ 40 * 11269 * 2
def baseEnd_11269 : Nat := 1142995258394398752727

theorem tailTrace_11269 : CollatzResearch.WordTrace tailWord_11269 prefixEnd_11269 1142995258394398752727 := by
  unfold tailWord_11269
  simp only [CollatzResearch.WordTrace]
  refine ⟨411014196181812437084861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 274009464121208291389907 411014196181812437084861)
  ·
    refine ⟨154130323568179663906823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 411014196181812437084861 154130323568179663906823)
    ·
      refine ⟨231195485352269495860235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154130323568179663906823 231195485352269495860235)
      ·
        refine ⟨346793228028404243790353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231195485352269495860235 346793228028404243790353)
        ·
          refine ⟨260094921021303182842765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346793228028404243790353 260094921021303182842765)
          ·
            refine ⟨97535595382988693566037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260094921021303182842765 97535595382988693566037)
            ·
              refine ⟨1142995258394398752727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 97535595382988693566037 1142995258394398752727)
              ·
                rfl

theorem cell19_11269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_11269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11269 prefixEnd_11269 := by exact prefixLift 11269
  have htrace : WordTrace (prefixWord ++ tailWord_11269) baseStart_11269 baseEnd_11269 := by
    simpa [prefixWord, tailWord_11269, baseEnd_11269] using wordTrace_append hprefix tailTrace_11269
  have hstable : (prefixWord ++ tailWord_11269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11269).length < 2 ^ (prefixWord ++ tailWord_11269).sum := by decide
  have hdescent : baseEnd_11269 < baseStart_11269 := by decide
  rcases family_descends (prefixWord ++ tailWord_11269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11303 : List Nat := [1, 1, 7, 1, 1, 2, 1, 5]
def baseStart_11303 : Nat := 118140960795 + 11303 * 2 ^ 59
def prefixEnd_11303 : Nat := 4983230072969 + 3 ^ 40 * 11303 * 2
def baseEnd_11303 : Nat := 3439331459481191502533

theorem tailTrace_11303 : CollatzResearch.WordTrace tailWord_11303 prefixEnd_11303 3439331459481191502533 := by
  unfold tailWord_11303
  simp only [CollatzResearch.WordTrace]
  refine ⟨412254278058636243822563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 274836185372424162548375 412254278058636243822563)
  ·
    refine ⟨618381417087954365733845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 412254278058636243822563 618381417087954365733845)
    ·
      refine ⟨14493314462998930446887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 618381417087954365733845 14493314462998930446887)
      ·
        refine ⟨21739971694498395670331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14493314462998930446887 21739971694498395670331)
        ·
          refine ⟨32609957541747593505497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21739971694498395670331 32609957541747593505497)
          ·
            refine ⟨24457468156310695129123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32609957541747593505497 24457468156310695129123)
            ·
              refine ⟨36686202234466042693685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24457468156310695129123 36686202234466042693685)
              ·
                refine ⟨3439331459481191502533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36686202234466042693685 3439331459481191502533)
                ·
                  rfl

theorem cell19_11303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_11303 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11303 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11303 prefixEnd_11303 := by exact prefixLift 11303
  have htrace : WordTrace (prefixWord ++ tailWord_11303) baseStart_11303 baseEnd_11303 := by
    simpa [prefixWord, tailWord_11303, baseEnd_11303] using wordTrace_append hprefix tailTrace_11303
  have hstable : (prefixWord ++ tailWord_11303).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11303).length < 2 ^ (prefixWord ++ tailWord_11303).sum := by decide
  have hdescent : baseEnd_11303 < baseStart_11303 := by decide
  rcases family_descends (prefixWord ++ tailWord_11303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11307 : List Nat := [1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_11307 : Nat := 118140960795 + 11307 * 2 ^ 59
def prefixEnd_11307 : Nat := 4983230072969 + 3 ^ 40 * 11307 * 2
def baseEnd_11307 : Nat := 3440548598810367413633

theorem tailTrace_11307 : CollatzResearch.WordTrace tailWord_11307 prefixEnd_11307 3440548598810367413633 := by
  unfold tailWord_11307
  simp only [CollatzResearch.WordTrace]
  refine ⟨412400170044144926968175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 274933446696096617978783 412400170044144926968175)
  ·
    refine ⟨618600255066217390452263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 412400170044144926968175 618600255066217390452263)
    ·
      refine ⟨927900382599326085678395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618600255066217390452263 927900382599326085678395)
      ·
        refine ⟨1391850573898989128517593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927900382599326085678395 1391850573898989128517593)
        ·
          refine ⟨1043887930424241846388195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1391850573898989128517593 1043887930424241846388195)
          ·
            refine ⟨1565831895636362769582293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043887930424241846388195 1565831895636362769582293)
            ·
              refine ⟨36699185053977252412085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1565831895636362769582293 36699185053977252412085)
              ·
                refine ⟨3440548598810367413633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36699185053977252412085 3440548598810367413633)
                ·
                  rfl

theorem cell19_11307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_11307 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11307 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11307 prefixEnd_11307 := by exact prefixLift 11307
  have htrace : WordTrace (prefixWord ++ tailWord_11307) baseStart_11307 baseEnd_11307 := by
    simpa [prefixWord, tailWord_11307, baseEnd_11307] using wordTrace_append hprefix tailTrace_11307
  have hstable : (prefixWord ++ tailWord_11307).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11307).length < 2 ^ (prefixWord ++ tailWord_11307).sum := by decide
  have hdescent : baseEnd_11307 < baseStart_11307 := by decide
  rcases family_descends (prefixWord ++ tailWord_11307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11324 : List Nat := [2, 2, 2, 2, 2, 4, 5]
def baseStart_11324 : Nat := 118140960795 + 11324 * 2 ^ 59
def prefixEnd_11324 : Nat := 4983230072969 + 3 ^ 40 * 11324 * 2
def baseEnd_11324 : Nat := 1148573813653121678603

theorem tailTrace_11324 : CollatzResearch.WordTrace tailWord_11324 prefixEnd_11324 1148573813653121678603 := by
  unfold tailWord_11324
  simp only [CollatzResearch.WordTrace]
  refine ⟨206510105491278415168513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 275346807321704553558017 206510105491278415168513)
  ·
    refine ⟨154882579118458811376385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206510105491278415168513 154882579118458811376385)
    ·
      refine ⟨116161934338844108532289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154882579118458811376385 116161934338844108532289)
      ·
        refine ⟨87121450754133081399217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116161934338844108532289 87121450754133081399217)
        ·
          refine ⟨65341088065599811049413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87121450754133081399217 65341088065599811049413)
          ·
            refine ⟨12251454012299964571765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65341088065599811049413 12251454012299964571765)
            ·
              refine ⟨1148573813653121678603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12251454012299964571765 1148573813653121678603)
              ·
                rfl

theorem cell19_11324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_11324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11324 prefixEnd_11324 := by exact prefixLift 11324
  have htrace : WordTrace (prefixWord ++ tailWord_11324) baseStart_11324 baseEnd_11324 := by
    simpa [prefixWord, tailWord_11324, baseEnd_11324] using wordTrace_append hprefix tailTrace_11324
  have hstable : (prefixWord ++ tailWord_11324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11324).length < 2 ^ (prefixWord ++ tailWord_11324).sum := by decide
  have hdescent : baseEnd_11324 < baseStart_11324 := by decide
  rcases family_descends (prefixWord ++ tailWord_11324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11341 : List Nat := [1, 6, 1, 1, 1, 3, 2, 4]
def baseStart_11341 : Nat := 118140960795 + 11341 * 2 ^ 59
def prefixEnd_11341 : Nat := 4983230072969 + 3 ^ 40 * 11341 * 2
def baseEnd_11341 : Nat := 3450894283108362657985

theorem tailTrace_11341 : CollatzResearch.WordTrace tailWord_11341 prefixEnd_11341 3450894283108362657985 := by
  unfold tailWord_11341
  simp only [CollatzResearch.WordTrace]
  refine ⟨413640251920968733705877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 275760167947312489137251 413640251920968733705877)
  ·
    refine ⟨19389386808795409392463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 413640251920968733705877 19389386808795409392463)
    ·
      refine ⟨29084080213193114088695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19389386808795409392463 29084080213193114088695)
      ·
        refine ⟨43626120319789671133043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29084080213193114088695 43626120319789671133043)
        ·
          refine ⟨65439180479684506699565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43626120319789671133043 65439180479684506699565)
          ·
            refine ⟨24539692679881690012337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65439180479684506699565 24539692679881690012337)
            ·
              refine ⟨18404769509911267509253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24539692679881690012337 18404769509911267509253)
              ·
                refine ⟨3450894283108362657985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18404769509911267509253 3450894283108362657985)
                ·
                  rfl

theorem cell19_11341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_11341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11341 prefixEnd_11341 := by exact prefixLift 11341
  have htrace : WordTrace (prefixWord ++ tailWord_11341) baseStart_11341 baseEnd_11341 := by
    simpa [prefixWord, tailWord_11341, baseEnd_11341] using wordTrace_append hprefix tailTrace_11341
  have hstable : (prefixWord ++ tailWord_11341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11341).length < 2 ^ (prefixWord ++ tailWord_11341).sum := by decide
  have hdescent : baseEnd_11341 < baseStart_11341 := by decide
  rcases family_descends (prefixWord ++ tailWord_11341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11345 : List Nat := [1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_11345 : Nat := 118140960795 + 11345 * 2 ^ 59
def prefixEnd_11345 : Nat := 4983230072969 + 3 ^ 40 * 11345 * 2
def baseEnd_11345 : Nat := 3452111422437538569085

theorem tailTrace_11345 : CollatzResearch.WordTrace tailWord_11345 prefixEnd_11345 3452111422437538569085 := by
  unfold tailWord_11345
  simp only [CollatzResearch.WordTrace]
  refine ⟨413786143906477416851489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 275857429270984944567659 413786143906477416851489)
  ·
    refine ⟨310339607929858062638617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 413786143906477416851489 310339607929858062638617)
    ·
      refine ⟨232754705947393546978963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310339607929858062638617 232754705947393546978963)
      ·
        refine ⟨349132058921090320468445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232754705947393546978963 349132058921090320468445)
        ·
          refine ⟨130924522095408870175667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349132058921090320468445 130924522095408870175667)
          ·
            refine ⟨196386783143113305263501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130924522095408870175667 196386783143113305263501)
            ·
              refine ⟨73645043678667489473813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196386783143113305263501 73645043678667489473813)
              ·
                refine ⟨3452111422437538569085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73645043678667489473813 3452111422437538569085)
                ·
                  rfl

theorem cell19_11345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_11345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11345 prefixEnd_11345 := by exact prefixLift 11345
  have htrace : WordTrace (prefixWord ++ tailWord_11345) baseStart_11345 baseEnd_11345 := by
    simpa [prefixWord, tailWord_11345, baseEnd_11345] using wordTrace_append hprefix tailTrace_11345
  have hstable : (prefixWord ++ tailWord_11345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11345).length < 2 ^ (prefixWord ++ tailWord_11345).sum := by decide
  have hdescent : baseEnd_11345 < baseStart_11345 := by decide
  rcases family_descends (prefixWord ++ tailWord_11345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11358 : List Nat := [4, 4, 1, 1, 1, 1, 2, 5]
def baseStart_11358 : Nat := 118140960795 + 11358 * 2 ^ 59
def prefixEnd_11358 : Nat := 4983230072969 + 3 ^ 40 * 11358 * 2
def baseEnd_11358 : Nat := 3456067125257360280161

theorem tailTrace_11358 : CollatzResearch.WordTrace tailWord_11358 prefixEnd_11358 3456067125257360280161 := by
  unfold tailWord_11358
  simp only [CollatzResearch.WordTrace]
  refine ⟨51782536607422579634341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 276173528572920424716485 51782536607422579634341)
  ·
    refine ⟨9709225613891733681439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51782536607422579634341 9709225613891733681439)
    ·
      refine ⟨14563838420837600522159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9709225613891733681439 14563838420837600522159)
      ·
        refine ⟨21845757631256400783239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14563838420837600522159 21845757631256400783239)
        ·
          refine ⟨32768636446884601174859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21845757631256400783239 32768636446884601174859)
          ·
            refine ⟨49152954670326901762289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32768636446884601174859 49152954670326901762289)
            ·
              refine ⟨36864716002745176321717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49152954670326901762289 36864716002745176321717)
              ·
                refine ⟨3456067125257360280161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36864716002745176321717 3456067125257360280161)
                ·
                  rfl

theorem cell19_11358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_11358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11358 prefixEnd_11358 := by exact prefixLift 11358
  have htrace : WordTrace (prefixWord ++ tailWord_11358) baseStart_11358 baseEnd_11358 := by
    simpa [prefixWord, tailWord_11358, baseEnd_11358] using wordTrace_append hprefix tailTrace_11358
  have hstable : (prefixWord ++ tailWord_11358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11358).length < 2 ^ (prefixWord ++ tailWord_11358).sum := by decide
  have hdescent : baseEnd_11358 < baseStart_11358 := by decide
  rcases family_descends (prefixWord ++ tailWord_11358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11381 : List Nat := [1, 3, 4, 3, 8]
def baseStart_11381 : Nat := 118140960795 + 11381 * 2 ^ 59
def prefixEnd_11381 : Nat := 4983230072969 + 3 ^ 40 * 11381 * 2
def baseEnd_11381 : Nat := 128261691718523028481

theorem tailTrace_11381 : CollatzResearch.WordTrace tailWord_11381 prefixEnd_11381 128261691718523028481 := by
  unfold tailWord_11381
  simp only [CollatzResearch.WordTrace]
  refine ⟨415099171776055565161997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 276732781184037043441331 415099171776055565161997)
  ·
    refine ⟨155662189416020836935749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 415099171776055565161997 155662189416020836935749)
    ·
      refine ⟨29186660515503906925453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155662189416020836935749 29186660515503906925453)
      ·
        refine ⟨10944997693313965097045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29186660515503906925453 10944997693313965097045)
        ·
          refine ⟨128261691718523028481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 10944997693313965097045 128261691718523028481)
          ·
            rfl

theorem cell19_11381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 8].length) (baseStart_11381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11381 prefixEnd_11381 := by exact prefixLift 11381
  have htrace : WordTrace (prefixWord ++ tailWord_11381) baseStart_11381 baseEnd_11381 := by
    simpa [prefixWord, tailWord_11381, baseEnd_11381] using wordTrace_append hprefix tailTrace_11381
  have hstable : (prefixWord ++ tailWord_11381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11381).length < 2 ^ (prefixWord ++ tailWord_11381).sum := by decide
  have hdescent : baseEnd_11381 < baseStart_11381 := by decide
  rcases family_descends (prefixWord ++ tailWord_11381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11493 : List Nat := [1, 3, 1, 4, 4, 1, 5]
def baseStart_11493 : Nat := 118140960795 + 11493 * 2 ^ 59
def prefixEnd_11493 : Nat := 4983230072969 + 3 ^ 40 * 11493 * 2
def baseEnd_11493 : Nat := 1165715192539015759931

theorem tailTrace_11493 : CollatzResearch.WordTrace tailWord_11493 prefixEnd_11493 1165715192539015759931 := by
  unfold tailWord_11493
  simp only [CollatzResearch.WordTrace]
  refine ⟨419184147370298693239133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 279456098246865795492755 419184147370298693239133)
  ·
    refine ⟨157194055263862009964675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 419184147370298693239133 157194055263862009964675)
    ·
      refine ⟨235791082895793014947013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157194055263862009964675 235791082895793014947013)
      ·
        refine ⟨44210828042961190302565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235791082895793014947013 44210828042961190302565)
        ·
          refine ⟨8289530258055223181731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44210828042961190302565 8289530258055223181731)
          ·
            refine ⟨12434295387082834772597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8289530258055223181731 12434295387082834772597)
            ·
              refine ⟨1165715192539015759931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12434295387082834772597 1165715192539015759931)
              ·
                rfl

theorem cell19_11493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 5].length) (baseStart_11493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11493 prefixEnd_11493 := by exact prefixLift 11493
  have htrace : WordTrace (prefixWord ++ tailWord_11493) baseStart_11493 baseEnd_11493 := by
    simpa [prefixWord, tailWord_11493, baseEnd_11493] using wordTrace_append hprefix tailTrace_11493
  have hstable : (prefixWord ++ tailWord_11493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11493).length < 2 ^ (prefixWord ++ tailWord_11493).sum := by decide
  have hdescent : baseEnd_11493 < baseStart_11493 := by decide
  rcases family_descends (prefixWord ++ tailWord_11493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11508 : List Nat := [2, 6, 1, 2, 1, 1, 2, 4]
def baseStart_11508 : Nat := 118140960795 + 11508 * 2 ^ 59
def prefixEnd_11508 : Nat := 4983230072969 + 3 ^ 40 * 11508 * 2
def baseEnd_11508 : Nat := 3501709850101456946419

theorem tailTrace_11508 : CollatzResearch.WordTrace tailWord_11508 prefixEnd_11508 3501709850101456946419 := by
  unfold tailWord_11508
  simp only [CollatzResearch.WordTrace]
  refine ⟨209865621157978127517589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 279820828210637503356785 209865621157978127517589)
  ·
    refine ⟨9837450991780224727387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 209865621157978127517589 9837450991780224727387)
    ·
      refine ⟨14756176487670337091081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9837450991780224727387 14756176487670337091081)
      ·
        refine ⟨11067132365752752818311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14756176487670337091081 11067132365752752818311)
        ·
          refine ⟨16600698548629129227467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11067132365752752818311 16600698548629129227467)
          ·
            refine ⟨24901047822943693841201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16600698548629129227467 24901047822943693841201)
            ·
              refine ⟨18675785867207770380901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24901047822943693841201 18675785867207770380901)
              ·
                refine ⟨3501709850101456946419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18675785867207770380901 3501709850101456946419)
                ·
                  rfl

theorem cell19_11508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_11508 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11508 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11508 prefixEnd_11508 := by exact prefixLift 11508
  have htrace : WordTrace (prefixWord ++ tailWord_11508) baseStart_11508 baseEnd_11508 := by
    simpa [prefixWord, tailWord_11508, baseEnd_11508] using wordTrace_append hprefix tailTrace_11508
  have hstable : (prefixWord ++ tailWord_11508).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11508).length < 2 ^ (prefixWord ++ tailWord_11508).sum := by decide
  have hdescent : baseEnd_11508 < baseStart_11508 := by decide
  rcases family_descends (prefixWord ++ tailWord_11508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11550 : List Nat := [4, 3, 2, 1, 2, 7]
def baseStart_11550 : Nat := 118140960795 + 11550 * 2 ^ 59
def prefixEnd_11550 : Nat := 4983230072969 + 3 ^ 40 * 11550 * 2
def baseEnd_11550 : Nat := 390498868117533779219

theorem tailTrace_11550 : CollatzResearch.WordTrace tailWord_11550 prefixEnd_11550 390498868117533779219 := by
  unfold tailWord_11550
  simp only [CollatzResearch.WordTrace]
  refine ⟨52657888520474678508013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 280842072109198285376069 52657888520474678508013)
  ·
    refine ⟨19746708195178004440505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52657888520474678508013 19746708195178004440505)
    ·
      refine ⟨14810031146383503330379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19746708195178004440505 14810031146383503330379)
      ·
        refine ⟨22215046719575254995569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14810031146383503330379 22215046719575254995569)
        ·
          refine ⟨16661285039681441246677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22215046719575254995569 16661285039681441246677)
          ·
            refine ⟨390498868117533779219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16661285039681441246677 390498868117533779219)
            ·
              rfl

theorem cell19_11550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 7].length) (baseStart_11550 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11550 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11550 prefixEnd_11550 := by exact prefixLift 11550
  have htrace : WordTrace (prefixWord ++ tailWord_11550) baseStart_11550 baseEnd_11550 := by
    simpa [prefixWord, tailWord_11550, baseEnd_11550] using wordTrace_append hprefix tailTrace_11550
  have hstable : (prefixWord ++ tailWord_11550).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11550).length < 2 ^ (prefixWord ++ tailWord_11550).sum := by decide
  have hdescent : baseEnd_11550 < baseStart_11550 := by decide
  rcases family_descends (prefixWord ++ tailWord_11550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11552 : List Nat := [2, 1, 1, 5, 4, 6]
def baseStart_11552 : Nat := 118140960795 + 11552 * 2 ^ 59
def prefixEnd_11552 : Nat := 4983230072969 + 3 ^ 40 * 11552 * 2
def baseEnd_11552 : Nat := 390566486969154663169

theorem tailTrace_11552 : CollatzResearch.WordTrace tailWord_11552 prefixEnd_11552 390566486969154663169 := by
  unfold tailWord_11552
  simp only [CollatzResearch.WordTrace]
  refine ⟨210668027078275884818455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 280890702771034513091273 210668027078275884818455)
  ·
    refine ⟨316002040617413827227683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210668027078275884818455 316002040617413827227683)
    ·
      refine ⟨474003060926120740841525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316002040617413827227683 474003060926120740841525)
      ·
        refine ⟨44437786961823819453893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 474003060926120740841525 44437786961823819453893)
        ·
          refine ⟨8332085055341966147605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44437786961823819453893 8332085055341966147605)
          ·
            refine ⟨390566486969154663169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8332085055341966147605 390566486969154663169)
            ·
              rfl

theorem cell19_11552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 6].length) (baseStart_11552 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11552 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11552 prefixEnd_11552 := by exact prefixLift 11552
  have htrace : WordTrace (prefixWord ++ tailWord_11552) baseStart_11552 baseEnd_11552 := by
    simpa [prefixWord, tailWord_11552, baseEnd_11552] using wordTrace_append hprefix tailTrace_11552
  have hstable : (prefixWord ++ tailWord_11552).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11552).length < 2 ^ (prefixWord ++ tailWord_11552).sum := by decide
  have hdescent : baseEnd_11552 < baseStart_11552 := by decide
  rcases family_descends (prefixWord ++ tailWord_11552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11554 : List Nat := [3, 3, 1, 1, 11]
def baseStart_11554 : Nat := 118140960795 + 11554 * 2 ^ 59
def prefixEnd_11554 : Nat := 4983230072969 + 3 ^ 40 * 11554 * 2
def baseEnd_11554 : Nat := 130211368606925182373

theorem tailTrace_11554 : CollatzResearch.WordTrace tailWord_11554 prefixEnd_11554 130211368606925182373 := by
  unfold tailWord_11554
  simp only [CollatzResearch.WordTrace]
  refine ⟨105352250037326527802429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 280939333432870740806477 105352250037326527802429)
  ·
    refine ⟨39507093763997447925911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105352250037326527802429 39507093763997447925911)
    ·
      refine ⟨59260640645996171888867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39507093763997447925911 59260640645996171888867)
      ·
        refine ⟨88890960968994257833301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59260640645996171888867 88890960968994257833301)
        ·
          refine ⟨130211368606925182373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 88890960968994257833301 130211368606925182373)
          ·
            rfl

theorem cell19_11554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 11].length) (baseStart_11554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11554 prefixEnd_11554 := by exact prefixLift 11554
  have htrace : WordTrace (prefixWord ++ tailWord_11554) baseStart_11554 baseEnd_11554 := by
    simpa [prefixWord, tailWord_11554, baseEnd_11554] using wordTrace_append hprefix tailTrace_11554
  have hstable : (prefixWord ++ tailWord_11554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11554).length < 2 ^ (prefixWord ++ tailWord_11554).sum := by decide
  have hdescent : baseEnd_11554 < baseStart_11554 := by decide
  rcases family_descends (prefixWord ++ tailWord_11554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11571 : List Nat := [1, 1, 1, 2, 5, 4, 1, 4]
def baseStart_11571 : Nat := 118140960795 + 11571 * 2 ^ 59
def prefixEnd_11571 : Nat := 4983230072969 + 3 ^ 40 * 11571 * 2
def baseEnd_11571 : Nat := 3520879794535977546247

theorem tailTrace_11571 : CollatzResearch.WordTrace tailWord_11571 prefixEnd_11571 3520879794535977546247 := by
  unfold tailWord_11571
  simp only [CollatzResearch.WordTrace]
  refine ⟨422029041087718014578567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 281352694058478676385711 422029041087718014578567)
  ·
    refine ⟨633043561631577021867851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 422029041087718014578567 633043561631577021867851)
    ·
      refine ⟨949565342447365532801777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 633043561631577021867851 949565342447365532801777)
      ·
        refine ⟨712174006835524149601333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 949565342447365532801777 712174006835524149601333)
        ·
          refine ⟨66766313140830389025125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 712174006835524149601333 66766313140830389025125)
          ·
            refine ⟨12518683713905697942211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66766313140830389025125 12518683713905697942211)
            ·
              refine ⟨18778025570858546913317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12518683713905697942211 18778025570858546913317)
              ·
                refine ⟨3520879794535977546247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18778025570858546913317 3520879794535977546247)
                ·
                  rfl

theorem cell19_11571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_11571 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11571 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11571 prefixEnd_11571 := by exact prefixLift 11571
  have htrace : WordTrace (prefixWord ++ tailWord_11571) baseStart_11571 baseEnd_11571 := by
    simpa [prefixWord, tailWord_11571, baseEnd_11571] using wordTrace_append hprefix tailTrace_11571
  have hstable : (prefixWord ++ tailWord_11571).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11571).length < 2 ^ (prefixWord ++ tailWord_11571).sum := by decide
  have hdescent : baseEnd_11571 < baseStart_11571 := by decide
  rcases family_descends (prefixWord ++ tailWord_11571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11761 : List Nat := [1, 2, 2, 2, 3, 3, 3, 3]
def baseStart_11761 : Nat := 118140960795 + 11761 * 2 ^ 59
def prefixEnd_11761 : Nat := 4983230072969 + 3 ^ 40 * 11761 * 2
def baseEnd_11761 : Nat := 3578693912671833323507

theorem tailTrace_11761 : CollatzResearch.WordTrace tailWord_11761 prefixEnd_11761 3578693912671833323507 := by
  unfold tailWord_11761
  simp only [CollatzResearch.WordTrace]
  refine ⟨428958910399380463995137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 285972606932920309330091 428958910399380463995137)
  ·
    refine ⟨321719182799535347996353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 428958910399380463995137 321719182799535347996353)
    ·
      refine ⟨241289387099651510997265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 321719182799535347996353 241289387099651510997265)
      ·
        refine ⟨180967040324738633247949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241289387099651510997265 180967040324738633247949)
        ·
          refine ⟨67862640121776987467981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180967040324738633247949 67862640121776987467981)
          ·
            refine ⟨25448490045666370300493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67862640121776987467981 25448490045666370300493)
            ·
              refine ⟨9543183767124888862685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25448490045666370300493 9543183767124888862685)
              ·
                refine ⟨3578693912671833323507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9543183767124888862685 3578693912671833323507)
                ·
                  rfl

theorem cell19_11761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3].length) (baseStart_11761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11761 prefixEnd_11761 := by exact prefixLift 11761
  have htrace : WordTrace (prefixWord ++ tailWord_11761) baseStart_11761 baseEnd_11761 := by
    simpa [prefixWord, tailWord_11761, baseEnd_11761] using wordTrace_append hprefix tailTrace_11761
  have hstable : (prefixWord ++ tailWord_11761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11761).length < 2 ^ (prefixWord ++ tailWord_11761).sum := by decide
  have hdescent : baseEnd_11761 < baseStart_11761 := by decide
  rcases family_descends (prefixWord ++ tailWord_11761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11780 : List Nat := [2, 3, 2, 3, 2, 1, 6]
def baseStart_11780 : Nat := 118140960795 + 11780 * 2 ^ 59
def prefixEnd_11780 : Nat := 4983230072969 + 3 ^ 40 * 11780 * 2
def baseEnd_11780 : Nat := 1194825108161806300411

theorem tailTrace_11780 : CollatzResearch.WordTrace tailWord_11780 prefixEnd_11780 1194825108161806300411 := by
  unfold tailWord_11780
  simp only [CollatzResearch.WordTrace]
  refine ⟨214825948665273354468397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 286434598220364472624529 214825948665273354468397)
  ·
    refine ⟨80559730749477507925649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 214825948665273354468397 80559730749477507925649)
    ·
      refine ⟨60419798062108130944237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80559730749477507925649 60419798062108130944237)
      ·
        refine ⟨22657424273290549104089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60419798062108130944237 22657424273290549104089)
        ·
          refine ⟨16993068204967911828067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22657424273290549104089 16993068204967911828067)
          ·
            refine ⟨25489602307451867742101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16993068204967911828067 25489602307451867742101)
            ·
              refine ⟨1194825108161806300411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25489602307451867742101 1194825108161806300411)
              ·
                rfl

theorem cell19_11780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_11780 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11780 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11780 prefixEnd_11780 := by exact prefixLift 11780
  have htrace : WordTrace (prefixWord ++ tailWord_11780) baseStart_11780 baseEnd_11780 := by
    simpa [prefixWord, tailWord_11780, baseEnd_11780] using wordTrace_append hprefix tailTrace_11780
  have hstable : (prefixWord ++ tailWord_11780).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11780).length < 2 ^ (prefixWord ++ tailWord_11780).sum := by decide
  have hdescent : baseEnd_11780 < baseStart_11780 := by decide
  rcases family_descends (prefixWord ++ tailWord_11780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11837 : List Nat := [1, 4, 1, 3, 3, 2, 5]
def baseStart_11837 : Nat := 118140960795 + 11837 * 2 ^ 59
def prefixEnd_11837 : Nat := 4983230072969 + 3 ^ 40 * 11837 * 2
def baseEnd_11837 : Nat := 1200606519975391878137

theorem tailTrace_11837 : CollatzResearch.WordTrace tailWord_11837 prefixEnd_11837 1200606519975391878137 := by
  unfold tailWord_11837
  simp only [CollatzResearch.WordTrace]
  refine ⟨431730858124045443761765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 287820572082696962507843 431730858124045443761765)
  ·
    refine ⟨80949535898258520705331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 431730858124045443761765 80949535898258520705331)
    ·
      refine ⟨121424303847387781057997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80949535898258520705331 121424303847387781057997)
      ·
        refine ⟨45534113942770417896749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121424303847387781057997 45534113942770417896749)
        ·
          refine ⟨17075292728538906711281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45534113942770417896749 17075292728538906711281)
          ·
            refine ⟨12806469546404180033461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17075292728538906711281 12806469546404180033461)
            ·
              refine ⟨1200606519975391878137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12806469546404180033461 1200606519975391878137)
              ·
                rfl

theorem cell19_11837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_11837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11837 prefixEnd_11837 := by exact prefixLift 11837
  have htrace : WordTrace (prefixWord ++ tailWord_11837) baseStart_11837 baseEnd_11837 := by
    simpa [prefixWord, tailWord_11837, baseEnd_11837] using wordTrace_append hprefix tailTrace_11837
  have hstable : (prefixWord ++ tailWord_11837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11837).length < 2 ^ (prefixWord ++ tailWord_11837).sum := by decide
  have hdescent : baseEnd_11837 < baseStart_11837 := by decide
  rcases family_descends (prefixWord ++ tailWord_11837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11839 : List Nat := [1, 1, 2, 2, 3, 5, 5]
def baseStart_11839 : Nat := 118140960795 + 11839 * 2 ^ 59
def prefixEnd_11839 : Nat := 4983230072969 + 3 ^ 40 * 11839 * 2
def baseEnd_11839 : Nat := 1200809376530254529987

theorem tailTrace_11839 : CollatzResearch.WordTrace tailWord_11839 prefixEnd_11839 1200809376530254529987 := by
  unfold tailWord_11839
  simp only [CollatzResearch.WordTrace]
  refine ⟨431803804116799785334571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 287869202744533190223047 431803804116799785334571)
  ·
    refine ⟨647705706175199678001857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 431803804116799785334571 647705706175199678001857)
    ·
      refine ⟨485779279631399758501393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 647705706175199678001857 485779279631399758501393)
      ·
        refine ⟨364334459723549818876045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 485779279631399758501393 364334459723549818876045)
        ·
          refine ⟨136625422396331182078517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364334459723549818876045 136625422396331182078517)
          ·
            refine ⟨12808633349656048319861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136625422396331182078517 12808633349656048319861)
            ·
              refine ⟨1200809376530254529987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12808633349656048319861 1200809376530254529987)
              ·
                rfl

theorem cell19_11839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_11839 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11839 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11839 prefixEnd_11839 := by exact prefixLift 11839
  have htrace : WordTrace (prefixWord ++ tailWord_11839) baseStart_11839 baseEnd_11839 := by
    simpa [prefixWord, tailWord_11839, baseEnd_11839] using wordTrace_append hprefix tailTrace_11839
  have hstable : (prefixWord ++ tailWord_11839).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11839).length < 2 ^ (prefixWord ++ tailWord_11839).sum := by decide
  have hdescent : baseEnd_11839 < baseStart_11839 := by decide
  rcases family_descends (prefixWord ++ tailWord_11839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11858 : List Nat := [3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_11858 : Nat := 118140960795 + 11858 * 2 ^ 59
def prefixEnd_11858 : Nat := 4983230072969 + 3 ^ 40 * 11858 * 2
def baseEnd_11858 : Nat := 3608209541404349167687

theorem tailTrace_11858 : CollatzResearch.WordTrace tailWord_11858 prefixEnd_11858 3608209541404349167687 := by
  unfold tailWord_11858
  simp only [CollatzResearch.WordTrace]
  refine ⟨108124197761991507569057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 288331194031977353517485 108124197761991507569057)
  ·
    refine ⟨81093148321493630676793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108124197761991507569057 81093148321493630676793)
    ·
      refine ⟨60819861241120223007595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81093148321493630676793 60819861241120223007595)
      ·
        refine ⟨91229791861680334511393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60819861241120223007595 91229791861680334511393)
        ·
          refine ⟨68422343896260250883545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91229791861680334511393 68422343896260250883545)
          ·
            refine ⟨51316757922195188162659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68422343896260250883545 51316757922195188162659)
            ·
              refine ⟨76975136883292782243989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51316757922195188162659 76975136883292782243989)
              ·
                refine ⟨3608209541404349167687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76975136883292782243989 3608209541404349167687)
                ·
                  rfl

theorem cell19_11858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_11858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11858 prefixEnd_11858 := by exact prefixLift 11858
  have htrace : WordTrace (prefixWord ++ tailWord_11858) baseStart_11858 baseEnd_11858 := by
    simpa [prefixWord, tailWord_11858, baseEnd_11858] using wordTrace_append hprefix tailTrace_11858
  have hstable : (prefixWord ++ tailWord_11858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11858).length < 2 ^ (prefixWord ++ tailWord_11858).sum := by decide
  have hdescent : baseEnd_11858 < baseStart_11858 := by decide
  rcases family_descends (prefixWord ++ tailWord_11858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11877 : List Nat := [1, 3, 1, 3, 3, 1, 2, 5]
def baseStart_11877 : Nat := 118140960795 + 11877 * 2 ^ 59
def prefixEnd_11877 : Nat := 4983230072969 + 3 ^ 40 * 11877 * 2
def baseEnd_11877 : Nat := 3613990953217934745413

theorem tailTrace_11877 : CollatzResearch.WordTrace tailWord_11877 prefixEnd_11877 3613990953217934745413 := by
  unfold tailWord_11877
  simp only [CollatzResearch.WordTrace]
  refine ⟨433189777979132275217885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 288793185319421516811923 433189777979132275217885)
  ·
    refine ⟨162446166742174603206707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 433189777979132275217885 162446166742174603206707)
    ·
      refine ⟨243669250113261904810061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162446166742174603206707 243669250113261904810061)
      ·
        refine ⟨91375968792473214303773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243669250113261904810061 91375968792473214303773)
        ·
          refine ⟨34265988297177455363915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91375968792473214303773 34265988297177455363915)
          ·
            refine ⟨51398982445766183045873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34265988297177455363915 51398982445766183045873)
            ·
              refine ⟨38549236834324637284405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51398982445766183045873 38549236834324637284405)
              ·
                refine ⟨3613990953217934745413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38549236834324637284405 3613990953217934745413)
                ·
                  rfl

theorem cell19_11877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_11877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11877 prefixEnd_11877 := by exact prefixLift 11877
  have htrace : WordTrace (prefixWord ++ tailWord_11877) baseStart_11877 baseEnd_11877 := by
    simpa [prefixWord, tailWord_11877, baseEnd_11877] using wordTrace_append hprefix tailTrace_11877
  have hstable : (prefixWord ++ tailWord_11877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11877).length < 2 ^ (prefixWord ++ tailWord_11877).sum := by decide
  have hdescent : baseEnd_11877 < baseStart_11877 := by decide
  rcases family_descends (prefixWord ++ tailWord_11877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11955 : List Nat := [1, 1, 1, 2, 3, 3, 8]
def baseStart_11955 : Nat := 118140960795 + 11955 * 2 ^ 59
def prefixEnd_11955 : Nat := 4983230072969 + 3 ^ 40 * 11955 * 2
def baseEnd_11955 : Nat := 1212575056712288337289

theorem tailTrace_11955 : CollatzResearch.WordTrace tailWord_11955 prefixEnd_11955 1212575056712288337289 := by
  unfold tailWord_11955
  simp only [CollatzResearch.WordTrace]
  refine ⟨436034671696551596557319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 290689781131034397704879 436034671696551596557319)
  ·
    refine ⟨654052007544827394835979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 436034671696551596557319 654052007544827394835979)
    ·
      refine ⟨981078011317241092253969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 654052007544827394835979 981078011317241092253969)
      ·
        refine ⟨735808508487930819190477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 981078011317241092253969 735808508487930819190477)
        ·
          refine ⟨275928190682974057196429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 735808508487930819190477 275928190682974057196429)
          ·
            refine ⟨103473071506115271448661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 275928190682974057196429 103473071506115271448661)
            ·
              refine ⟨1212575056712288337289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 103473071506115271448661 1212575056712288337289)
              ·
                rfl

theorem cell19_11955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_11955 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11955 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11955 prefixEnd_11955 := by exact prefixLift 11955
  have htrace : WordTrace (prefixWord ++ tailWord_11955) baseStart_11955 baseEnd_11955 := by
    simpa [prefixWord, tailWord_11955, baseEnd_11955] using wordTrace_append hprefix tailTrace_11955
  have hstable : (prefixWord ++ tailWord_11955).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11955).length < 2 ^ (prefixWord ++ tailWord_11955).sum := by decide
  have hdescent : baseEnd_11955 < baseStart_11955 := by decide
  rcases family_descends (prefixWord ++ tailWord_11955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_11972 : List Nat := [2, 3, 3, 1, 1, 1, 2, 6]
def baseStart_11972 : Nat := 118140960795 + 11972 * 2 ^ 59
def prefixEnd_11972 : Nat := 4983230072969 + 3 ^ 40 * 11972 * 2
def baseEnd_11972 : Nat := 3642898012285862634043

theorem tailTrace_11972 : CollatzResearch.WordTrace tailWord_11972 prefixEnd_11972 3642898012285862634043 := by
  unfold tailWord_11972
  simp only [CollatzResearch.WordTrace]
  refine ⟨218327356317481749963085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 291103141756642333284113 218327356317481749963085)
  ·
    refine ⟨81872758619055656236157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 218327356317481749963085 81872758619055656236157)
    ·
      refine ⟨30702284482145871088559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81872758619055656236157 30702284482145871088559)
      ·
        refine ⟨46053426723218806632839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30702284482145871088559 46053426723218806632839)
        ·
          refine ⟨69080140084828209949259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46053426723218806632839 69080140084828209949259)
          ·
            refine ⟨103620210127242314923889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69080140084828209949259 103620210127242314923889)
            ·
              refine ⟨77715157595431736192917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103620210127242314923889 77715157595431736192917)
              ·
                refine ⟨3642898012285862634043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77715157595431736192917 3642898012285862634043)
                ·
                  rfl

theorem cell19_11972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_11972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_11972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_11972 prefixEnd_11972 := by exact prefixLift 11972
  have htrace : WordTrace (prefixWord ++ tailWord_11972) baseStart_11972 baseEnd_11972 := by
    simpa [prefixWord, tailWord_11972, baseEnd_11972] using wordTrace_append hprefix tailTrace_11972
  have hstable : (prefixWord ++ tailWord_11972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_11972).length < 2 ^ (prefixWord ++ tailWord_11972).sum := by decide
  have hdescent : baseEnd_11972 < baseStart_11972 := by decide
  rcases family_descends (prefixWord ++ tailWord_11972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12012 : List Nat := [2, 2, 1, 1, 2, 2, 9]
def baseStart_12012 : Nat := 118140960795 + 12012 * 2 ^ 59
def prefixEnd_12012 : Nat := 4983230072969 + 3 ^ 40 * 12012 * 2
def baseEnd_12012 : Nat := 1218356468525873915015

theorem tailTrace_12012 : CollatzResearch.WordTrace tailWord_12012 prefixEnd_12012 1218356468525873915015 := by
  unfold tailWord_12012
  simp only [CollatzResearch.WordTrace]
  refine ⟨219056816245025165691145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 292075754993366887588193 219056816245025165691145)
  ·
    refine ⟨164292612183768874268359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 219056816245025165691145 164292612183768874268359)
    ·
      refine ⟨246438918275653311402539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164292612183768874268359 246438918275653311402539)
      ·
        refine ⟨369658377413479967103809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246438918275653311402539 369658377413479967103809)
        ·
          refine ⟨277243783060109975327857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369658377413479967103809 277243783060109975327857)
          ·
            refine ⟨207932837295082481495893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 277243783060109975327857 207932837295082481495893)
            ·
              refine ⟨1218356468525873915015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 207932837295082481495893 1218356468525873915015)
              ·
                rfl

theorem cell19_12012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_12012 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12012 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12012 prefixEnd_12012 := by exact prefixLift 12012
  have htrace : WordTrace (prefixWord ++ tailWord_12012) baseStart_12012 baseEnd_12012 := by
    simpa [prefixWord, tailWord_12012, baseEnd_12012] using wordTrace_append hprefix tailTrace_12012
  have hstable : (prefixWord ++ tailWord_12012).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12012).length < 2 ^ (prefixWord ++ tailWord_12012).sum := by decide
  have hdescent : baseEnd_12012 < baseStart_12012 := by decide
  rcases family_descends (prefixWord ++ tailWord_12012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12031 : List Nat := [1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_12031 : Nat := 118140960795 + 12031 * 2 ^ 59
def prefixEnd_12031 : Nat := 4983230072969 + 3 ^ 40 * 12031 * 2
def baseEnd_12031 : Nat := 3660850817391207322771

theorem tailTrace_12031 : CollatzResearch.WordTrace tailWord_12031 prefixEnd_12031 3660850817391207322771 := by
  unfold tailWord_12031
  simp only [CollatzResearch.WordTrace]
  refine ⟨438806619421216576323947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 292537746280811050882631 438806619421216576323947)
  ·
    refine ⟨658209929131824864485921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 438806619421216576323947 658209929131824864485921)
    ·
      refine ⟨493657446848868648364441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 658209929131824864485921 493657446848868648364441)
      ·
        refine ⟨370243085136651486273331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493657446848868648364441 370243085136651486273331)
        ·
          refine ⟨555364627704977229409997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370243085136651486273331 555364627704977229409997)
          ·
            refine ⟨208261735389366461028749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 555364627704977229409997 208261735389366461028749)
            ·
              refine ⟨78098150771012422885781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 208261735389366461028749 78098150771012422885781)
              ·
                refine ⟨3660850817391207322771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78098150771012422885781 3660850817391207322771)
                ·
                  rfl

theorem cell19_12031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_12031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12031 prefixEnd_12031 := by exact prefixLift 12031
  have htrace : WordTrace (prefixWord ++ tailWord_12031) baseStart_12031 baseEnd_12031 := by
    simpa [prefixWord, tailWord_12031, baseEnd_12031] using wordTrace_append hprefix tailTrace_12031
  have hstable : (prefixWord ++ tailWord_12031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12031).length < 2 ^ (prefixWord ++ tailWord_12031).sum := by decide
  have hdescent : baseEnd_12031 < baseStart_12031 := by decide
  rcases family_descends (prefixWord ++ tailWord_12031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12069 : List Nat := [1, 3, 1, 2, 3, 9]
def baseStart_12069 : Nat := 118140960795 + 12069 * 2 ^ 59
def prefixEnd_12069 : Nat := 4983230072969 + 3 ^ 40 * 12069 * 2
def baseEnd_12069 : Nat := 408045960113153164247

theorem tailTrace_12069 : CollatzResearch.WordTrace tailWord_12069 prefixEnd_12069 408045960113153164247 := by
  unfold tailWord_12069
  simp only [CollatzResearch.WordTrace]
  refine ⟨440192593283549066207261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 293461728855699377471507 440192593283549066207261)
  ·
    refine ⟨165072222481330899827723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 440192593283549066207261 165072222481330899827723)
    ·
      refine ⟨247608333721996349741585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165072222481330899827723 247608333721996349741585)
      ·
        refine ⟨185706250291497262306189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247608333721996349741585 185706250291497262306189)
        ·
          refine ⟨69639843859311473364821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185706250291497262306189 69639843859311473364821)
          ·
            refine ⟨408045960113153164247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 69639843859311473364821 408045960113153164247)
            ·
              rfl

theorem cell19_12069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 9].length) (baseStart_12069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12069 prefixEnd_12069 := by exact prefixLift 12069
  have htrace : WordTrace (prefixWord ++ tailWord_12069) baseStart_12069 baseEnd_12069 := by
    simpa [prefixWord, tailWord_12069, baseEnd_12069] using wordTrace_append hprefix tailTrace_12069
  have hstable : (prefixWord ++ tailWord_12069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12069).length < 2 ^ (prefixWord ++ tailWord_12069).sum := by decide
  have hdescent : baseEnd_12069 < baseStart_12069 := by decide
  rcases family_descends (prefixWord ++ tailWord_12069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12084 : List Nat := [2, 5, 1, 1, 2, 1, 3, 4]
def baseStart_12084 : Nat := 118140960795 + 12084 * 2 ^ 59
def prefixEnd_12084 : Nat := 4983230072969 + 3 ^ 40 * 12084 * 2
def baseEnd_12084 : Nat := 3676977913502788144849

theorem tailTrace_12084 : CollatzResearch.WordTrace tailWord_12084 prefixEnd_12084 3676977913502788144849 := by
  unfold tailWord_12084
  simp only [CollatzResearch.WordTrace]
  refine ⟨220369844114603314001653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 293826458819471085335537 220369844114603314001653)
  ·
    refine ⟨20659672885744060687655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220369844114603314001653 20659672885744060687655)
    ·
      refine ⟨30989509328616091031483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20659672885744060687655 30989509328616091031483)
      ·
        refine ⟨46484263992924136547225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30989509328616091031483 46484263992924136547225)
        ·
          refine ⟨34863197994693102410419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46484263992924136547225 34863197994693102410419)
          ·
            refine ⟨52294796992039653615629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34863197994693102410419 52294796992039653615629)
            ·
              refine ⟨19610548872014870105861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52294796992039653615629 19610548872014870105861)
              ·
                refine ⟨3676977913502788144849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19610548872014870105861 3676977913502788144849)
                ·
                  rfl

theorem cell19_12084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_12084 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12084 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12084 prefixEnd_12084 := by exact prefixLift 12084
  have htrace : WordTrace (prefixWord ++ tailWord_12084) baseStart_12084 baseEnd_12084 := by
    simpa [prefixWord, tailWord_12084, baseEnd_12084] using wordTrace_append hprefix tailTrace_12084
  have hstable : (prefixWord ++ tailWord_12084).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12084).length < 2 ^ (prefixWord ++ tailWord_12084).sum := by decide
  have hdescent : baseEnd_12084 < baseStart_12084 := by decide
  rcases family_descends (prefixWord ++ tailWord_12084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12105 : List Nat := [1, 2, 1, 1, 2, 4, 5, 3]
def baseStart_12105 : Nat := 118140960795 + 12105 * 2 ^ 59
def prefixEnd_12105 : Nat := 4983230072969 + 3 ^ 40 * 12105 * 2
def baseEnd_12105 : Nat := 3683367894980961678125

theorem tailTrace_12105 : CollatzResearch.WordTrace tailWord_12105 prefixEnd_12105 3683367894980961678125 := by
  unfold tailWord_12105
  simp only [CollatzResearch.WordTrace]
  refine ⟨441505621153127214517769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 294337080768751476345179 441505621153127214517769)
  ·
    refine ⟨331129215864845410888327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 441505621153127214517769 331129215864845410888327)
    ·
      refine ⟨496693823797268116332491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331129215864845410888327 496693823797268116332491)
      ·
        refine ⟨745040735695902174498737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496693823797268116332491 745040735695902174498737)
        ·
          refine ⟨558780551771926630874053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745040735695902174498737 558780551771926630874053)
          ·
            refine ⟨104771353457236243288885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 558780551771926630874053 104771353457236243288885)
            ·
              refine ⟨9822314386615897808333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104771353457236243288885 9822314386615897808333)
              ·
                refine ⟨3683367894980961678125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9822314386615897808333 3683367894980961678125)
                ·
                  rfl

theorem cell19_12105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 3].length) (baseStart_12105 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12105 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12105 prefixEnd_12105 := by exact prefixLift 12105
  have htrace : WordTrace (prefixWord ++ tailWord_12105) baseStart_12105 baseEnd_12105 := by
    simpa [prefixWord, tailWord_12105, baseEnd_12105] using wordTrace_append hprefix tailTrace_12105
  have hstable : (prefixWord ++ tailWord_12105).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12105).length < 2 ^ (prefixWord ++ tailWord_12105).sum := by decide
  have hdescent : baseEnd_12105 < baseStart_12105 := by decide
  rcases family_descends (prefixWord ++ tailWord_12105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12145 : List Nat := [1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_12145 : Nat := 118140960795 + 12145 * 2 ^ 59
def prefixEnd_12145 : Nat := 4983230072969 + 3 ^ 40 * 12145 * 2
def baseEnd_12145 : Nat := 3695539288272720789127

theorem tailTrace_12145 : CollatzResearch.WordTrace tailWord_12145 prefixEnd_12145 3695539288272720789127 := by
  unfold tailWord_12145
  simp only [CollatzResearch.WordTrace]
  refine ⟨442964541008214045973889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 295309694005476030649259 442964541008214045973889)
  ·
    refine ⟨332223405756160534480417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 442964541008214045973889 332223405756160534480417)
    ·
      refine ⟨249167554317120400860313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332223405756160534480417 249167554317120400860313)
      ·
        refine ⟨186875665737840300645235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249167554317120400860313 186875665737840300645235)
        ·
          refine ⟨280313498606760450967853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186875665737840300645235 280313498606760450967853)
          ·
            refine ⟨105117561977535169112945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280313498606760450967853 105117561977535169112945)
            ·
              refine ⟨78838171483151376834709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105117561977535169112945 78838171483151376834709)
              ·
                refine ⟨3695539288272720789127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78838171483151376834709 3695539288272720789127)
                ·
                  rfl

theorem cell19_12145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_12145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12145 prefixEnd_12145 := by exact prefixLift 12145
  have htrace : WordTrace (prefixWord ++ tailWord_12145) baseStart_12145 baseEnd_12145 := by
    simpa [prefixWord, tailWord_12145, baseEnd_12145] using wordTrace_append hprefix tailTrace_12145
  have hstable : (prefixWord ++ tailWord_12145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12145).length < 2 ^ (prefixWord ++ tailWord_12145).sum := by decide
  have hdescent : baseEnd_12145 < baseStart_12145 := by decide
  rcases family_descends (prefixWord ++ tailWord_12145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12158 : List Nat := [4, 2, 3, 1, 1, 1, 4, 3]
def baseStart_12158 : Nat := 118140960795 + 12158 * 2 ^ 59
def prefixEnd_12158 : Nat := 4983230072969 + 3 ^ 40 * 12158 * 2
def baseEnd_12158 : Nat := 3699494991092542500203

theorem tailTrace_12158 : CollatzResearch.WordTrace tailWord_12158 prefixEnd_12158 3699494991092542500203 := by
  unfold tailWord_12158
  simp only [CollatzResearch.WordTrace]
  refine ⟨55429836245139658274641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 295625793307411510798085 55429836245139658274641)
  ·
    refine ⟨41572377183854743705981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55429836245139658274641 41572377183854743705981)
    ·
      refine ⟨15589641443945528889743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41572377183854743705981 15589641443945528889743)
      ·
        refine ⟨23384462165918293334615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15589641443945528889743 23384462165918293334615)
        ·
          refine ⟨35076693248877440001923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23384462165918293334615 35076693248877440001923)
          ·
            refine ⟨52615039873316160002885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35076693248877440001923 52615039873316160002885)
            ·
              refine ⟨9865319976246780000541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52615039873316160002885 9865319976246780000541)
              ·
                refine ⟨3699494991092542500203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9865319976246780000541 3699494991092542500203)
                ·
                  rfl

theorem cell19_12158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_12158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12158 prefixEnd_12158 := by exact prefixLift 12158
  have htrace : WordTrace (prefixWord ++ tailWord_12158) baseStart_12158 baseEnd_12158 := by
    simpa [prefixWord, tailWord_12158, baseEnd_12158] using wordTrace_append hprefix tailTrace_12158
  have hstable : (prefixWord ++ tailWord_12158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12158).length < 2 ^ (prefixWord ++ tailWord_12158).sum := by decide
  have hdescent : baseEnd_12158 < baseStart_12158 := by decide
  rcases family_descends (prefixWord ++ tailWord_12158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12183 : List Nat := [1, 1, 3, 3, 1, 3, 7]
def baseStart_12183 : Nat := 118140960795 + 12183 * 2 ^ 59
def prefixEnd_12183 : Nat := 4983230072969 + 3 ^ 40 * 12183 * 2
def baseEnd_12183 : Nat := 1235700703966630648193

theorem tailTrace_12183 : CollatzResearch.WordTrace tailWord_12183 prefixEnd_12183 1235700703966630648193 := by
  unfold tailWord_12183
  simp only [CollatzResearch.WordTrace]
  refine ⟨444350514870546535857203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 296233676580364357238135 444350514870546535857203)
  ·
    refine ⟨666525772305819803785805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 444350514870546535857203 666525772305819803785805)
    ·
      refine ⟨249947164614682426419677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 666525772305819803785805 249947164614682426419677)
      ·
        refine ⟨93730186730505909907379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249947164614682426419677 93730186730505909907379)
        ·
          refine ⟨140595280095758864861069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93730186730505909907379 140595280095758864861069)
          ·
            refine ⟨52723230035909574322901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140595280095758864861069 52723230035909574322901)
            ·
              refine ⟨1235700703966630648193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 52723230035909574322901 1235700703966630648193)
              ·
                rfl

theorem cell19_12183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_12183 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12183 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12183 prefixEnd_12183 := by exact prefixLift 12183
  have htrace : WordTrace (prefixWord ++ tailWord_12183) baseStart_12183 baseEnd_12183 := by
    simpa [prefixWord, tailWord_12183, baseEnd_12183] using wordTrace_append hprefix tailTrace_12183
  have hstable : (prefixWord ++ tailWord_12183).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12183).length < 2 ^ (prefixWord ++ tailWord_12183).sum := by decide
  have hdescent : baseEnd_12183 < baseStart_12183 := by decide
  rcases family_descends (prefixWord ++ tailWord_12183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12253 : List Nat := [1, 4, 3, 1, 4, 1, 1, 4]
def baseStart_12253 : Nat := 118140960795 + 12253 * 2 ^ 59
def prefixEnd_12253 : Nat := 4983230072969 + 3 ^ 40 * 12253 * 2
def baseEnd_12253 : Nat := 3728402050160470388833

theorem tailTrace_12253 : CollatzResearch.WordTrace tailWord_12253 prefixEnd_12253 3728402050160470388833 := by
  unfold tailWord_12253
  simp only [CollatzResearch.WordTrace]
  refine ⟨446903624616948490905413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 297935749744632327270275 446903624616948490905413)
  ·
    refine ⟨83794429615677842044765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 446903624616948490905413 83794429615677842044765)
    ·
      refine ⟨31422911105879190766787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83794429615677842044765 31422911105879190766787)
      ·
        refine ⟨47134366658818786150181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31422911105879190766787 47134366658818786150181)
        ·
          refine ⟨8837693748528522403159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47134366658818786150181 8837693748528522403159)
          ·
            refine ⟨13256540622792783604739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8837693748528522403159 13256540622792783604739)
            ·
              refine ⟨19884810934189175407109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13256540622792783604739 19884810934189175407109)
              ·
                refine ⟨3728402050160470388833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19884810934189175407109 3728402050160470388833)
                ·
                  rfl

theorem cell19_12253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 4].length) (baseStart_12253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12253 prefixEnd_12253 := by exact prefixLift 12253
  have htrace : WordTrace (prefixWord ++ tailWord_12253) baseStart_12253 baseEnd_12253 := by
    simpa [prefixWord, tailWord_12253, baseEnd_12253] using wordTrace_append hprefix tailTrace_12253
  have hstable : (prefixWord ++ tailWord_12253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12253).length < 2 ^ (prefixWord ++ tailWord_12253).sum := by decide
  have hdescent : baseEnd_12253 < baseStart_12253 := by decide
  rcases family_descends (prefixWord ++ tailWord_12253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12327 : List Nat := [1, 1, 7, 1, 3, 1, 2, 3]
def baseStart_12327 : Nat := 118140960795 + 12327 * 2 ^ 59
def prefixEnd_12327 : Nat := 4983230072969 + 3 ^ 40 * 12327 * 2
def baseEnd_12327 : Nat := 3750919127750224744187

theorem tailTrace_12327 : CollatzResearch.WordTrace tailWord_12327 prefixEnd_12327 3750919127750224744187 := by
  unfold tailWord_12327
  simp only [CollatzResearch.WordTrace]
  refine ⟨449602626348859129099235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 299735084232572752732823 449602626348859129099235)
  ·
    refine ⟨674403939523288693648853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 449602626348859129099235 674403939523288693648853)
    ·
      refine ⟨15806342332577078757395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 674403939523288693648853 15806342332577078757395)
      ·
        refine ⟨23709513498865618136093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15806342332577078757395 23709513498865618136093)
        ·
          refine ⟨8891067562074606801035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23709513498865618136093 8891067562074606801035)
          ·
            refine ⟨13336601343111910201553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8891067562074606801035 13336601343111910201553)
            ·
              refine ⟨10002451007333932651165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13336601343111910201553 10002451007333932651165)
              ·
                refine ⟨3750919127750224744187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10002451007333932651165 3750919127750224744187)
                ·
                  rfl

theorem cell19_12327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 3].length) (baseStart_12327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12327 prefixEnd_12327 := by exact prefixLift 12327
  have htrace : WordTrace (prefixWord ++ tailWord_12327) baseStart_12327 baseEnd_12327 := by
    simpa [prefixWord, tailWord_12327, baseEnd_12327] using wordTrace_append hprefix tailTrace_12327
  have hstable : (prefixWord ++ tailWord_12327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12327).length < 2 ^ (prefixWord ++ tailWord_12327).sum := by decide
  have hdescent : baseEnd_12327 < baseStart_12327 := by decide
  rcases family_descends (prefixWord ++ tailWord_12327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12350 : List Nat := [4, 2, 1, 3, 2, 2, 5]
def baseStart_12350 : Nat := 118140960795 + 12350 * 2 ^ 59
def prefixEnd_12350 : Nat := 4983230072969 + 3 ^ 40 * 12350 * 2
def baseEnd_12350 : Nat := 1252639226297662077671

theorem tailTrace_12350 : CollatzResearch.WordTrace tailWord_12350 prefixEnd_12350 1252639226297662077671 := by
  unfold tailWord_12350
  simp only [CollatzResearch.WordTrace]
  refine ⟨56305188158191757148313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 300294336843689371457669 56305188158191757148313)
  ·
    refine ⟨42228891118643817861235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56305188158191757148313 42228891118643817861235)
    ·
      refine ⟨63343336677965726791853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42228891118643817861235 63343336677965726791853)
      ·
        refine ⟨23753751254237147546945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63343336677965726791853 23753751254237147546945)
        ·
          refine ⟨17815313440677860660209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23753751254237147546945 17815313440677860660209)
          ·
            refine ⟨13361485080508395495157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17815313440677860660209 13361485080508395495157)
            ·
              refine ⟨1252639226297662077671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13361485080508395495157 1252639226297662077671)
              ·
                rfl

theorem cell19_12350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_12350 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12350 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12350 prefixEnd_12350 := by exact prefixLift 12350
  have htrace : WordTrace (prefixWord ++ tailWord_12350) baseStart_12350 baseEnd_12350 := by
    simpa [prefixWord, tailWord_12350, baseEnd_12350] using wordTrace_append hprefix tailTrace_12350
  have hstable : (prefixWord ++ tailWord_12350).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12350).length < 2 ^ (prefixWord ++ tailWord_12350).sum := by decide
  have hdescent : baseEnd_12350 < baseStart_12350 := by decide
  rcases family_descends (prefixWord ++ tailWord_12350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12373 : List Nat := [1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_12373 : Nat := 118140960795 + 12373 * 2 ^ 59
def prefixEnd_12373 : Nat := 4983230072969 + 3 ^ 40 * 12373 * 2
def baseEnd_12373 : Nat := 3764916230035747721839

theorem tailTrace_12373 : CollatzResearch.WordTrace tailWord_12373 prefixEnd_12373 3764916230035747721839 := by
  unfold tailWord_12373
  simp only [CollatzResearch.WordTrace]
  refine ⟨451280384182208985273773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 300853589454805990182515 451280384182208985273773)
  ·
    refine ⟨169230144068328369477665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 451280384182208985273773 169230144068328369477665)
    ·
      refine ⟨126922608051246277108249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169230144068328369477665 126922608051246277108249)
      ·
        refine ⟨95191956038434707831187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126922608051246277108249 95191956038434707831187)
        ·
          refine ⟨142787934057652061746781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95191956038434707831187 142787934057652061746781)
          ·
            refine ⟨53545475271619523155043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142787934057652061746781 53545475271619523155043)
            ·
              refine ⟨80318212907429284732565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53545475271619523155043 80318212907429284732565)
              ·
                refine ⟨3764916230035747721839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80318212907429284732565 3764916230035747721839)
                ·
                  rfl

theorem cell19_12373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_12373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12373 prefixEnd_12373 := by exact prefixLift 12373
  have htrace : WordTrace (prefixWord ++ tailWord_12373) baseStart_12373 baseEnd_12373 := by
    simpa [prefixWord, tailWord_12373, baseEnd_12373] using wordTrace_append hprefix tailTrace_12373
  have hstable : (prefixWord ++ tailWord_12373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12373).length < 2 ^ (prefixWord ++ tailWord_12373).sum := by decide
  have hdescent : baseEnd_12373 < baseStart_12373 := by decide
  rcases family_descends (prefixWord ++ tailWord_12373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12502 : List Nat := [5, 2, 1, 2, 1, 2, 1, 5]
def baseStart_12502 : Nat := 118140960795 + 12502 * 2 ^ 59
def prefixEnd_12502 : Nat := 4983230072969 + 3 ^ 40 * 12502 * 2
def baseEnd_12502 : Nat := 3804168973401670854821

theorem tailTrace_12502 : CollatzResearch.WordTrace tailWord_12502 prefixEnd_12502 3804168973401670854821 := by
  unfold tailWord_12502
  simp only [CollatzResearch.WordTrace]
  refine ⟨28499087544679001044985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 303990267143242677813173 28499087544679001044985)
  ·
    refine ⟨21374315658509250783739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28499087544679001044985 21374315658509250783739)
    ·
      refine ⟨32061473487763876175609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21374315658509250783739 32061473487763876175609)
      ·
        refine ⟨24046105115822907131707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32061473487763876175609 24046105115822907131707)
        ·
          refine ⟨36069157673734360697561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24046105115822907131707 36069157673734360697561)
          ·
            refine ⟨27051868255300770523171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36069157673734360697561 27051868255300770523171)
            ·
              refine ⟨40577802382951155784757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27051868255300770523171 40577802382951155784757)
              ·
                refine ⟨3804168973401670854821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40577802382951155784757 3804168973401670854821)
                ·
                  rfl

theorem cell19_12502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_12502 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12502 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12502 prefixEnd_12502 := by exact prefixLift 12502
  have htrace : WordTrace (prefixWord ++ tailWord_12502) baseStart_12502 baseEnd_12502 := by
    simpa [prefixWord, tailWord_12502, baseEnd_12502] using wordTrace_append hprefix tailTrace_12502
  have hstable : (prefixWord ++ tailWord_12502).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12502).length < 2 ^ (prefixWord ++ tailWord_12502).sum := by decide
  have hdescent : baseEnd_12502 < baseStart_12502 := by decide
  rcases family_descends (prefixWord ++ tailWord_12502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12504 : List Nat := [2, 1, 2, 2, 4, 1, 4, 3]
def baseStart_12504 : Nat := 118140960795 + 12504 * 2 ^ 59
def prefixEnd_12504 : Nat := 4983230072969 + 3 ^ 40 * 12504 * 2
def baseEnd_12504 : Nat := 3804777543066258810371

theorem tailTrace_12504 : CollatzResearch.WordTrace tailWord_12504 prefixEnd_12504 3804777543066258810371 := by
  unfold tailWord_12504
  simp only [CollatzResearch.WordTrace]
  refine ⟨228029173353809179146283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 304038897805078905528377 228029173353809179146283)
  ·
    refine ⟨342043760030713768719425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228029173353809179146283 342043760030713768719425)
    ·
      refine ⟨256532820023035326539569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 342043760030713768719425 256532820023035326539569)
      ·
        refine ⟨192399615017276494904677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256532820023035326539569 192399615017276494904677)
        ·
          refine ⟨36074927815739342794627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192399615017276494904677 36074927815739342794627)
          ·
            refine ⟨54112391723609014191941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36074927815739342794627 54112391723609014191941)
            ·
              refine ⟨10146073448176690160989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54112391723609014191941 10146073448176690160989)
              ·
                refine ⟨3804777543066258810371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10146073448176690160989 3804777543066258810371)
                ·
                  rfl

theorem cell19_12504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_12504 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12504 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12504 prefixEnd_12504 := by exact prefixLift 12504
  have htrace : WordTrace (prefixWord ++ tailWord_12504) baseStart_12504 baseEnd_12504 := by
    simpa [prefixWord, tailWord_12504, baseEnd_12504] using wordTrace_append hprefix tailTrace_12504
  have hstable : (prefixWord ++ tailWord_12504).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12504).length < 2 ^ (prefixWord ++ tailWord_12504).sum := by decide
  have hdescent : baseEnd_12504 < baseStart_12504 := by decide
  rcases family_descends (prefixWord ++ tailWord_12504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12542 : List Nat := [4, 2, 2, 1, 1, 1, 4, 4]
def baseStart_12542 : Nat := 118140960795 + 12542 * 2 ^ 59
def prefixEnd_12542 : Nat := 4983230072969 + 3 ^ 40 * 12542 * 2
def baseEnd_12542 : Nat := 3816340366693429965823

theorem tailTrace_12542 : CollatzResearch.WordTrace tailWord_12542 prefixEnd_12542 3816340366693429965823 := by
  unfold tailWord_12542
  simp only [CollatzResearch.WordTrace]
  refine ⟨57180540071243856021985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 304962880379967232117253 57180540071243856021985)
  ·
    refine ⟨42885405053432892016489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57180540071243856021985 42885405053432892016489)
    ·
      refine ⟨32164053790074669012367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42885405053432892016489 32164053790074669012367)
      ·
        refine ⟨48246080685112003518551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32164053790074669012367 48246080685112003518551)
        ·
          refine ⟨72369121027668005277827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48246080685112003518551 72369121027668005277827)
          ·
            refine ⟨108553681541502007916741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72369121027668005277827 108553681541502007916741)
            ·
              refine ⟨20353815289031626484389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108553681541502007916741 20353815289031626484389)
              ·
                refine ⟨3816340366693429965823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20353815289031626484389 3816340366693429965823)
                ·
                  rfl

theorem cell19_12542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_12542 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12542 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12542 prefixEnd_12542 := by exact prefixLift 12542
  have htrace : WordTrace (prefixWord ++ tailWord_12542) baseStart_12542 baseEnd_12542 := by
    simpa [prefixWord, tailWord_12542, baseEnd_12542] using wordTrace_append hprefix tailTrace_12542
  have hstable : (prefixWord ++ tailWord_12542).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12542).length < 2 ^ (prefixWord ++ tailWord_12542).sum := by decide
  have hdescent : baseEnd_12542 < baseStart_12542 := by decide
  rcases family_descends (prefixWord ++ tailWord_12542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12673 : List Nat := [1, 2, 4, 3, 1, 3, 2, 3]
def baseStart_12673 : Nat := 118140960795 + 12673 * 2 ^ 59
def prefixEnd_12673 : Nat := 4983230072969 + 3 ^ 40 * 12673 * 2
def baseEnd_12673 : Nat := 3856201679723941054355

theorem tailTrace_12673 : CollatzResearch.WordTrace tailWord_12673 prefixEnd_12673 3856201679723941054355 := by
  unfold tailWord_12673
  simp only [CollatzResearch.WordTrace]
  refine ⟨462222283095360221194673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 308148188730240147463115 462222283095360221194673)
  ·
    refine ⟨346666712321520165896005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 462222283095360221194673 346666712321520165896005)
    ·
      refine ⟨65000008560285031105501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 346666712321520165896005 65000008560285031105501)
      ·
        refine ⟨24375003210106886664563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65000008560285031105501 24375003210106886664563)
        ·
          refine ⟨36562504815160329996845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24375003210106886664563 36562504815160329996845)
          ·
            refine ⟨13710939305685123748817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36562504815160329996845 13710939305685123748817)
            ·
              refine ⟨10283204479263842811613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13710939305685123748817 10283204479263842811613)
              ·
                refine ⟨3856201679723941054355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10283204479263842811613 3856201679723941054355)
                ·
                  rfl

theorem cell19_12673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 3].length) (baseStart_12673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12673 prefixEnd_12673 := by exact prefixLift 12673
  have htrace : WordTrace (prefixWord ++ tailWord_12673) baseStart_12673 baseEnd_12673 := by
    simpa [prefixWord, tailWord_12673, baseEnd_12673] using wordTrace_append hprefix tailTrace_12673
  have hstable : (prefixWord ++ tailWord_12673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12673).length < 2 ^ (prefixWord ++ tailWord_12673).sum := by decide
  have hdescent : baseEnd_12673 < baseStart_12673 := by decide
  rcases family_descends (prefixWord ++ tailWord_12673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12692 : List Nat := [2, 4, 2, 1, 4, 1, 5]
def baseStart_12692 : Nat := 118140960795 + 12692 * 2 ^ 59
def prefixEnd_12692 : Nat := 4983230072969 + 3 ^ 40 * 12692 * 2
def baseEnd_12692 : Nat := 1287327697179175544027

theorem tailTrace_12692 : CollatzResearch.WordTrace tailWord_12692 prefixEnd_12692 1287327697179175544027 := by
  unfold tailWord_12692
  simp only [CollatzResearch.WordTrace]
  refine ⟨231457635013263233068165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 308610180017684310757553 231457635013263233068165)
  ·
    refine ⟨43398306564986856200281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231457635013263233068165 43398306564986856200281)
    ·
      refine ⟨32548729923740142150211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43398306564986856200281 32548729923740142150211)
      ·
        refine ⟨48823094885610213225317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32548729923740142150211 48823094885610213225317)
        ·
          refine ⟨9154330291051914979747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48823094885610213225317 9154330291051914979747)
          ·
            refine ⟨13731495436577872469621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9154330291051914979747 13731495436577872469621)
            ·
              refine ⟨1287327697179175544027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13731495436577872469621 1287327697179175544027)
              ·
                rfl

theorem cell19_12692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 5].length) (baseStart_12692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12692 prefixEnd_12692 := by exact prefixLift 12692
  have htrace : WordTrace (prefixWord ++ tailWord_12692) baseStart_12692 baseEnd_12692 := by
    simpa [prefixWord, tailWord_12692, baseEnd_12692] using wordTrace_append hprefix tailTrace_12692
  have hstable : (prefixWord ++ tailWord_12692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12692).length < 2 ^ (prefixWord ++ tailWord_12692).sum := by decide
  have hdescent : baseEnd_12692 < baseStart_12692 := by decide
  rcases family_descends (prefixWord ++ tailWord_12692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12696 : List Nat := [2, 1, 2, 5, 1, 1, 7]
def baseStart_12696 : Nat := 118140960795 + 12696 * 2 ^ 59
def prefixEnd_12696 : Nat := 4983230072969 + 3 ^ 40 * 12696 * 2
def baseEnd_12696 : Nat := 1287733410288900847727

theorem tailTrace_12696 : CollatzResearch.WordTrace tailWord_12696 prefixEnd_12696 1287733410288900847727 := by
  unfold tailWord_12696
  simp only [CollatzResearch.WordTrace]
  refine ⟨231530581006017574640971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 308707441341356766187961 231530581006017574640971)
  ·
    refine ⟨347295871509026361961457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231530581006017574640971 347295871509026361961457)
    ·
      refine ⟨260471903631769771471093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347295871509026361961457 260471903631769771471093)
      ·
        refine ⟨24419240965478416075415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 260471903631769771471093 24419240965478416075415)
        ·
          refine ⟨36628861448217624113123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24419240965478416075415 36628861448217624113123)
          ·
            refine ⟨54943292172326436169685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36628861448217624113123 54943292172326436169685)
            ·
              refine ⟨1287733410288900847727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54943292172326436169685 1287733410288900847727)
              ·
                rfl

theorem cell19_12696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_12696 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12696 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12696 prefixEnd_12696 := by exact prefixLift 12696
  have htrace : WordTrace (prefixWord ++ tailWord_12696) baseStart_12696 baseEnd_12696 := by
    simpa [prefixWord, tailWord_12696, baseEnd_12696] using wordTrace_append hprefix tailTrace_12696
  have hstable : (prefixWord ++ tailWord_12696).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12696).length < 2 ^ (prefixWord ++ tailWord_12696).sum := by decide
  have hdescent : baseEnd_12696 < baseStart_12696 := by decide
  rcases family_descends (prefixWord ++ tailWord_12696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12734 : List Nat := [4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_12734 : Nat := 118140960795 + 12734 * 2 ^ 59
def prefixEnd_12734 : Nat := 4983230072969 + 3 ^ 40 * 12734 * 2
def baseEnd_12734 : Nat := 3874763054493873698633

theorem tailTrace_12734 : CollatzResearch.WordTrace tailWord_12734 prefixEnd_12734 3874763054493873698633 := by
  unfold tailWord_12734
  simp only [CollatzResearch.WordTrace]
  refine ⟨58055891984295954895657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 309631423916245092776837 58055891984295954895657)
  ·
    refine ⟨43541918988221966171743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58055891984295954895657 43541918988221966171743)
    ·
      refine ⟨65312878482332949257615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43541918988221966171743 65312878482332949257615)
      ·
        refine ⟨97969317723499423886423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65312878482332949257615 97969317723499423886423)
        ·
          refine ⟨146953976585249135829635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97969317723499423886423 146953976585249135829635)
          ·
            refine ⟨220430964877873703744453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146953976585249135829635 220430964877873703744453)
            ·
              refine ⟨41330805914601319452085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220430964877873703744453 41330805914601319452085)
              ·
                refine ⟨3874763054493873698633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41330805914601319452085 3874763054493873698633)
                ·
                  rfl

theorem cell19_12734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_12734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12734 prefixEnd_12734 := by exact prefixLift 12734
  have htrace : WordTrace (prefixWord ++ tailWord_12734) baseStart_12734 baseEnd_12734 := by
    simpa [prefixWord, tailWord_12734, baseEnd_12734] using wordTrace_append hprefix tailTrace_12734
  have hstable : (prefixWord ++ tailWord_12734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12734).length < 2 ^ (prefixWord ++ tailWord_12734).sum := by decide
  have hdescent : baseEnd_12734 < baseStart_12734 := by decide
  rcases family_descends (prefixWord ++ tailWord_12734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12793 : List Nat := [1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_12793 : Nat := 118140960795 + 12793 * 2 ^ 59
def prefixEnd_12793 : Nat := 4983230072969 + 3 ^ 40 * 12793 * 2
def baseEnd_12793 : Nat := 3892715859599218387361

theorem tailTrace_12793 : CollatzResearch.WordTrace tailWord_12793 prefixEnd_12793 3892715859599218387361 := by
  unfold tailWord_12793
  simp only [CollatzResearch.WordTrace]
  refine ⟨466599042660620715563033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 311066028440413810375355 466599042660620715563033)
  ·
    refine ⟨349949281995465536672275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 466599042660620715563033 349949281995465536672275)
    ·
      refine ⟨524923922993198305008413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349949281995465536672275 524923922993198305008413)
      ·
        refine ⟨196846471122449364378155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 524923922993198305008413 196846471122449364378155)
        ·
          refine ⟨295269706683674046567233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196846471122449364378155 295269706683674046567233)
          ·
            refine ⟨221452280012755534925425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295269706683674046567233 221452280012755534925425)
            ·
              refine ⟨166089210009566651194069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221452280012755534925425 166089210009566651194069)
              ·
                refine ⟨3892715859599218387361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 166089210009566651194069 3892715859599218387361)
                ·
                  rfl

theorem cell19_12793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_12793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12793 prefixEnd_12793 := by exact prefixLift 12793
  have htrace : WordTrace (prefixWord ++ tailWord_12793) baseStart_12793 baseEnd_12793 := by
    simpa [prefixWord, tailWord_12793, baseEnd_12793] using wordTrace_append hprefix tailTrace_12793
  have hstable : (prefixWord ++ tailWord_12793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12793).length < 2 ^ (prefixWord ++ tailWord_12793).sum := by decide
  have hdescent : baseEnd_12793 < baseStart_12793 := by decide
  rcases family_descends (prefixWord ++ tailWord_12793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12831 : List Nat := [1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_12831 : Nat := 118140960795 + 12831 * 2 ^ 59
def prefixEnd_12831 : Nat := 4983230072969 + 3 ^ 40 * 12831 * 2
def baseEnd_12831 : Nat := 3904278683226389542813

theorem tailTrace_12831 : CollatzResearch.WordTrace tailWord_12831 prefixEnd_12831 3904278683226389542813 := by
  unfold tailWord_12831
  simp only [CollatzResearch.WordTrace]
  refine ⟨467985016522953205446347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 311990011015302136964231 467985016522953205446347)
  ·
    refine ⟨701977524784429808169521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 467985016522953205446347 701977524784429808169521)
    ·
      refine ⟨526483143588322356127141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 701977524784429808169521 526483143588322356127141)
      ·
        refine ⟨98715589422810441773839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 526483143588322356127141 98715589422810441773839)
        ·
          refine ⟨148073384134215662660759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98715589422810441773839 148073384134215662660759)
          ·
            refine ⟨222110076201323493991139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148073384134215662660759 222110076201323493991139)
            ·
              refine ⟨333165114301985240986709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222110076201323493991139 333165114301985240986709)
              ·
                refine ⟨3904278683226389542813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 333165114301985240986709 3904278683226389542813)
                ·
                  rfl

theorem cell19_12831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_12831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12831 prefixEnd_12831 := by exact prefixLift 12831
  have htrace : WordTrace (prefixWord ++ tailWord_12831) baseStart_12831 baseEnd_12831 := by
    simpa [prefixWord, tailWord_12831, baseEnd_12831] using wordTrace_append hprefix tailTrace_12831
  have hstable : (prefixWord ++ tailWord_12831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12831).length < 2 ^ (prefixWord ++ tailWord_12831).sum := by decide
  have hdescent : baseEnd_12831 < baseStart_12831 := by decide
  rcases family_descends (prefixWord ++ tailWord_12831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12846 : List Nat := [4, 1, 3, 1, 3, 1, 1, 5]
def baseStart_12846 : Nat := 118140960795 + 12846 * 2 ^ 59
def prefixEnd_12846 : Nat := 4983230072969 + 3 ^ 40 * 12846 * 2
def baseEnd_12846 : Nat := 3908842955710799209439

theorem tailTrace_12846 : CollatzResearch.WordTrace tailWord_12846 prefixEnd_12846 3908842955710799209439 := by
  unfold tailWord_12846
  simp only [CollatzResearch.WordTrace]
  refine ⟨58566513933576345905299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 312354740979073844828261 58566513933576345905299)
  ·
    refine ⟨87849770900364518857949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58566513933576345905299 87849770900364518857949)
    ·
      refine ⟨32943664087636694571731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87849770900364518857949 32943664087636694571731)
      ·
        refine ⟨49415496131455041857597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32943664087636694571731 49415496131455041857597)
        ·
          refine ⟨18530811049295640696599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49415496131455041857597 18530811049295640696599)
          ·
            refine ⟨27796216573943461044899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18530811049295640696599 27796216573943461044899)
            ·
              refine ⟨41694324860915191567349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27796216573943461044899 41694324860915191567349)
              ·
                refine ⟨3908842955710799209439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41694324860915191567349 3908842955710799209439)
                ·
                  rfl

theorem cell19_12846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_12846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12846 prefixEnd_12846 := by exact prefixLift 12846
  have htrace : WordTrace (prefixWord ++ tailWord_12846) baseStart_12846 baseEnd_12846 := by
    simpa [prefixWord, tailWord_12846, baseEnd_12846] using wordTrace_append hprefix tailTrace_12846
  have hstable : (prefixWord ++ tailWord_12846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12846).length < 2 ^ (prefixWord ++ tailWord_12846).sum := by decide
  have hdescent : baseEnd_12846 < baseStart_12846 := by decide
  rcases family_descends (prefixWord ++ tailWord_12846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12848 : List Nat := [2, 1, 1, 1, 2, 3, 6, 3]
def baseStart_12848 : Nat := 118140960795 + 12848 * 2 ^ 59
def prefixEnd_12848 : Nat := 4983230072969 + 3 ^ 40 * 12848 * 2
def baseEnd_12848 : Nat := 3909451525375387164989

theorem tailTrace_12848 : CollatzResearch.WordTrace tailWord_12848 prefixEnd_12848 3909451525375387164989 := by
  unfold tailWord_12848
  simp only [CollatzResearch.WordTrace]
  refine ⟨234302528730682554407599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 312403371640910072543465 234302528730682554407599)
  ·
    refine ⟨351453793096023831611399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234302528730682554407599 351453793096023831611399)
    ·
      refine ⟨527180689644035747417099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351453793096023831611399 527180689644035747417099)
      ·
        refine ⟨790771034466053621125649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527180689644035747417099 790771034466053621125649)
        ·
          refine ⟨593078275849540215844237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790771034466053621125649 593078275849540215844237)
          ·
            refine ⟨222404353443577580941589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 593078275849540215844237 222404353443577580941589)
            ·
              refine ⟨10425204067667699106637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222404353443577580941589 10425204067667699106637)
              ·
                refine ⟨3909451525375387164989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10425204067667699106637 3909451525375387164989)
                ·
                  rfl

theorem cell19_12848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_12848 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12848 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12848 prefixEnd_12848 := by exact prefixLift 12848
  have htrace : WordTrace (prefixWord ++ tailWord_12848) baseStart_12848 baseEnd_12848 := by
    simpa [prefixWord, tailWord_12848, baseEnd_12848] using wordTrace_append hprefix tailTrace_12848
  have hstable : (prefixWord ++ tailWord_12848).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12848).length < 2 ^ (prefixWord ++ tailWord_12848).sum := by decide
  have hdescent : baseEnd_12848 < baseStart_12848 := by decide
  rcases family_descends (prefixWord ++ tailWord_12848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12869 : List Nat := [1, 3, 1, 1, 1, 5, 7]
def baseStart_12869 : Nat := 118140960795 + 12869 * 2 ^ 59
def prefixEnd_12869 : Nat := 4983230072969 + 3 ^ 40 * 12869 * 2
def baseEnd_12869 : Nat := 1305280502284520232755

theorem tailTrace_12869 : CollatzResearch.WordTrace tailWord_12869 prefixEnd_12869 1305280502284520232755 := by
  unfold tailWord_12869
  simp only [CollatzResearch.WordTrace]
  refine ⟨469370990385285695329661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 312913993590190463553107 469370990385285695329661)
  ·
    refine ⟨176014121394482135748623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 469370990385285695329661 176014121394482135748623)
    ·
      refine ⟨264021182091723203622935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176014121394482135748623 264021182091723203622935)
      ·
        refine ⟨396031773137584805434403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264021182091723203622935 396031773137584805434403)
        ·
          refine ⟨594047659706377208151605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396031773137584805434403 594047659706377208151605)
          ·
            refine ⟨55691968097472863264213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 594047659706377208151605 55691968097472863264213)
            ·
              refine ⟨1305280502284520232755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55691968097472863264213 1305280502284520232755)
              ·
                rfl

theorem cell19_12869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_12869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12869 prefixEnd_12869 := by exact prefixLift 12869
  have htrace : WordTrace (prefixWord ++ tailWord_12869) baseStart_12869 baseEnd_12869 := by
    simpa [prefixWord, tailWord_12869, baseEnd_12869] using wordTrace_append hprefix tailTrace_12869
  have hstable : (prefixWord ++ tailWord_12869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12869).length < 2 ^ (prefixWord ++ tailWord_12869).sum := by decide
  have hdescent : baseEnd_12869 < baseStart_12869 := by decide
  rcases family_descends (prefixWord ++ tailWord_12869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12888 : List Nat := [2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_12888 : Nat := 118140960795 + 12888 * 2 ^ 59
def prefixEnd_12888 : Nat := 4983230072969 + 3 ^ 40 * 12888 * 2
def baseEnd_12888 : Nat := 3921622918667146275991

theorem tailTrace_12888 : CollatzResearch.WordTrace tailWord_12888 prefixEnd_12888 3921622918667146275991 := by
  unfold tailWord_12888
  simp only [CollatzResearch.WordTrace]
  refine ⟨235031988658225970135659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 313375984877634626847545 235031988658225970135659)
  ·
    refine ⟨352547982987338955203489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235031988658225970135659 352547982987338955203489)
    ·
      refine ⟨264410987240504216402617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352547982987338955203489 264410987240504216402617)
      ·
        refine ⟨198308240430378162301963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264410987240504216402617 198308240430378162301963)
        ·
          refine ⟨297462360645567243452945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198308240430378162301963 297462360645567243452945)
          ·
            refine ⟨223096770484175432589709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297462360645567243452945 223096770484175432589709)
            ·
              refine ⟨83661288931565787221141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223096770484175432589709 83661288931565787221141)
              ·
                refine ⟨3921622918667146275991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83661288931565787221141 3921622918667146275991)
                ·
                  rfl

theorem cell19_12888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_12888 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12888 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12888 prefixEnd_12888 := by exact prefixLift 12888
  have htrace : WordTrace (prefixWord ++ tailWord_12888) baseStart_12888 baseEnd_12888 := by
    simpa [prefixWord, tailWord_12888, baseEnd_12888] using wordTrace_append hprefix tailTrace_12888
  have hstable : (prefixWord ++ tailWord_12888).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12888).length < 2 ^ (prefixWord ++ tailWord_12888).sum := by decide
  have hdescent : baseEnd_12888 < baseStart_12888 := by decide
  rcases family_descends (prefixWord ++ tailWord_12888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12926 : List Nat := [4, 2, 13]
def baseStart_12926 : Nat := 118140960795 + 12926 * 2 ^ 59
def prefixEnd_12926 : Nat := 4983230072969 + 3 ^ 40 * 12926 * 2
def baseEnd_12926 : Nat := 16185949556766738401

theorem tailTrace_12926 : CollatzResearch.WordTrace tailWord_12926 prefixEnd_12926 16185949556766738401 := by
  unfold tailWord_12926
  simp only [CollatzResearch.WordTrace]
  refine ⟨58931243897348053769329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 314299967452522953436421 58931243897348053769329)
  ·
    refine ⟨44198432923011040326997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58931243897348053769329 44198432923011040326997)
    ·
      refine ⟨16185949556766738401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 44198432923011040326997 16185949556766738401)
      ·
        rfl

theorem cell19_12926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 13].length) (baseStart_12926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12926 prefixEnd_12926 := by exact prefixLift 12926
  have htrace : WordTrace (prefixWord ++ tailWord_12926) baseStart_12926 baseEnd_12926 := by
    simpa [prefixWord, tailWord_12926, baseEnd_12926] using wordTrace_append hprefix tailTrace_12926
  have hstable : (prefixWord ++ tailWord_12926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12926).length < 2 ^ (prefixWord ++ tailWord_12926).sum := by decide
  have hdescent : baseEnd_12926 < baseStart_12926 := by decide
  rcases family_descends (prefixWord ++ tailWord_12926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12960 : List Nat := [2, 1, 1, 4, 4, 1, 3, 3]
def baseStart_12960 : Nat := 118140960795 + 12960 * 2 ^ 59
def prefixEnd_12960 : Nat := 4983230072969 + 3 ^ 40 * 12960 * 2
def baseEnd_12960 : Nat := 3943531426592312675795

theorem tailTrace_12960 : CollatzResearch.WordTrace tailWord_12960 prefixEnd_12960 3943531426592312675795 := by
  unfold tailWord_12960
  simp only [CollatzResearch.WordTrace]
  refine ⟨236345016527804118446167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 315126688703738824594889 236345016527804118446167)
  ·
    refine ⟨354517524791706177669251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236345016527804118446167 354517524791706177669251)
    ·
      refine ⟨531776287187559266503877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 354517524791706177669251 531776287187559266503877)
      ·
        refine ⟨99708053847667362469477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 531776287187559266503877 99708053847667362469477)
        ·
          refine ⟨18695260096437630463027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99708053847667362469477 18695260096437630463027)
          ·
            refine ⟨28042890144656445694541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18695260096437630463027 28042890144656445694541)
            ·
              refine ⟨10516083804246167135453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28042890144656445694541 10516083804246167135453)
              ·
                refine ⟨3943531426592312675795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10516083804246167135453 3943531426592312675795)
                ·
                  rfl

theorem cell19_12960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_12960 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12960 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12960 prefixEnd_12960 := by exact prefixLift 12960
  have htrace : WordTrace (prefixWord ++ tailWord_12960) baseStart_12960 baseEnd_12960 := by
    simpa [prefixWord, tailWord_12960, baseEnd_12960] using wordTrace_append hprefix tailTrace_12960
  have hstable : (prefixWord ++ tailWord_12960).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12960).length < 2 ^ (prefixWord ++ tailWord_12960).sum := by decide
  have hdescent : baseEnd_12960 < baseStart_12960 := by decide
  rcases family_descends (prefixWord ++ tailWord_12960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_12981 : List Nat := [1, 3, 3, 3, 1, 2, 6]
def baseStart_12981 : Nat := 118140960795 + 12981 * 2 ^ 59
def prefixEnd_12981 : Nat := 4983230072969 + 3 ^ 40 * 12981 * 2
def baseEnd_12981 : Nat := 1316640469356828736357

theorem tailTrace_12981 : CollatzResearch.WordTrace tailWord_12981 prefixEnd_12981 1316640469356828736357 := by
  unfold tailWord_12981
  simp only [CollatzResearch.WordTrace]
  refine ⟨473455965979528823406797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 315637310653019215604531 473455965979528823406797)
  ·
    refine ⟨177545987242323308777549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 473455965979528823406797 177545987242323308777549)
    ·
      refine ⟨66579745215871240791581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177545987242323308777549 66579745215871240791581)
      ·
        refine ⟨24967404455951715296843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66579745215871240791581 24967404455951715296843)
        ·
          refine ⟨37451106683927572945265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24967404455951715296843 37451106683927572945265)
          ·
            refine ⟨28088330012945679708949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37451106683927572945265 28088330012945679708949)
            ·
              refine ⟨1316640469356828736357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28088330012945679708949 1316640469356828736357)
              ·
                rfl

theorem cell19_12981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_12981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_12981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_12981 prefixEnd_12981 := by exact prefixLift 12981
  have htrace : WordTrace (prefixWord ++ tailWord_12981) baseStart_12981 baseEnd_12981 := by
    simpa [prefixWord, tailWord_12981, baseEnd_12981] using wordTrace_append hprefix tailTrace_12981
  have hstable : (prefixWord ++ tailWord_12981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_12981).length < 2 ^ (prefixWord ++ tailWord_12981).sum := by decide
  have hdescent : baseEnd_12981 < baseStart_12981 := by decide
  rcases family_descends (prefixWord ++ tailWord_12981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13013 : List Nat := [1, 3, 2, 5, 2, 1, 2, 3]
def baseStart_13013 : Nat := 118140960795 + 13013 * 2 ^ 59
def prefixEnd_13013 : Nat := 4983230072969 + 3 ^ 40 * 13013 * 2
def baseEnd_13013 : Nat := 3959658522703893497873

theorem tailTrace_13013 : CollatzResearch.WordTrace tailWord_13013 prefixEnd_13013 3959658522703893497873 := by
  unfold tailWord_13013
  simp only [CollatzResearch.WordTrace]
  refine ⟨474623101863598288571693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 316415401242398859047795 474623101863598288571693)
  ·
    refine ⟨177983663198849358214385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 474623101863598288571693 177983663198849358214385)
    ·
      refine ⟨133487747399137018660789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177983663198849358214385 133487747399137018660789)
      ·
        refine ⟨12514476318669095499449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133487747399137018660789 12514476318669095499449)
        ·
          refine ⟨9385857239001821624587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12514476318669095499449 9385857239001821624587)
          ·
            refine ⟨14078785858502732436881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9385857239001821624587 14078785858502732436881)
            ·
              refine ⟨10559089393877049327661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14078785858502732436881 10559089393877049327661)
              ·
                refine ⟨3959658522703893497873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10559089393877049327661 3959658522703893497873)
                ·
                  rfl

theorem cell19_13013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 3].length) (baseStart_13013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13013 prefixEnd_13013 := by exact prefixLift 13013
  have htrace : WordTrace (prefixWord ++ tailWord_13013) baseStart_13013 baseEnd_13013 := by
    simpa [prefixWord, tailWord_13013, baseEnd_13013] using wordTrace_append hprefix tailTrace_13013
  have hstable : (prefixWord ++ tailWord_13013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13013).length < 2 ^ (prefixWord ++ tailWord_13013).sum := by decide
  have hdescent : baseEnd_13013 < baseStart_13013 := by decide
  rcases family_descends (prefixWord ++ tailWord_13013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13038 : List Nat := [4, 1, 2, 1, 1, 5, 5]
def baseStart_13038 : Nat := 118140960795 + 13038 * 2 ^ 59
def prefixEnd_13038 : Nat := 4983230072969 + 3 ^ 40 * 13038 * 2
def baseEnd_13038 : Nat := 1322421881170414314083

theorem tailTrace_13038 : CollatzResearch.WordTrace tailWord_13038 prefixEnd_13038 1322421881170414314083 := by
  unfold tailWord_13038
  simp only [CollatzResearch.WordTrace]
  refine ⟨59441865846628444778971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 317023284515351705487845 59441865846628444778971)
  ·
    refine ⟨89162798769942667168457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59441865846628444778971 89162798769942667168457)
    ·
      refine ⟨66872099077457000376343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89162798769942667168457 66872099077457000376343)
      ·
        refine ⟨100308148616185500564515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66872099077457000376343 100308148616185500564515)
        ·
          refine ⟨150462222924278250846773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100308148616185500564515 150462222924278250846773)
          ·
            refine ⟨14105833399151086016885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150462222924278250846773 14105833399151086016885)
            ·
              refine ⟨1322421881170414314083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14105833399151086016885 1322421881170414314083)
              ·
                rfl

theorem cell19_13038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_13038 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13038 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13038 prefixEnd_13038 := by exact prefixLift 13038
  have htrace : WordTrace (prefixWord ++ tailWord_13038) baseStart_13038 baseEnd_13038 := by
    simpa [prefixWord, tailWord_13038, baseEnd_13038] using wordTrace_append hprefix tailTrace_13038
  have hstable : (prefixWord ++ tailWord_13038).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13038).length < 2 ^ (prefixWord ++ tailWord_13038).sum := by decide
  have hdescent : baseEnd_13038 < baseStart_13038 := by decide
  rcases family_descends (prefixWord ++ tailWord_13038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13110 : List Nat := [5, 1, 2, 2, 2, 2, 1, 4]
def baseStart_13110 : Nat := 118140960795 + 13110 * 2 ^ 59
def prefixEnd_13110 : Nat := 4983230072969 + 3 ^ 40 * 13110 * 2
def baseEnd_13110 : Nat := 3989174151436409342053

theorem tailTrace_13110 : CollatzResearch.WordTrace tailWord_13110 prefixEnd_13110 3989174151436409342053 := by
  unfold tailWord_13110
  simp only [CollatzResearch.WordTrace]
  refine ⟨29885061407011490928299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 318773988341455903235189 29885061407011490928299)
  ·
    refine ⟨44827592110517236392449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29885061407011490928299 44827592110517236392449)
    ·
      refine ⟨33620694082887927294337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44827592110517236392449 33620694082887927294337)
      ·
        refine ⟨25215520562165945470753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33620694082887927294337 25215520562165945470753)
        ·
          refine ⟨18911640421624459103065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25215520562165945470753 18911640421624459103065)
          ·
            refine ⟨14183730316218344327299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18911640421624459103065 14183730316218344327299)
            ·
              refine ⟨21275595474327516490949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14183730316218344327299 21275595474327516490949)
              ·
                refine ⟨3989174151436409342053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21275595474327516490949 3989174151436409342053)
                ·
                  rfl

theorem cell19_13110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_13110 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13110 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13110 prefixEnd_13110 := by exact prefixLift 13110
  have htrace : WordTrace (prefixWord ++ tailWord_13110) baseStart_13110 baseEnd_13110 := by
    simpa [prefixWord, tailWord_13110, baseEnd_13110] using wordTrace_append hprefix tailTrace_13110
  have hstable : (prefixWord ++ tailWord_13110).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13110).length < 2 ^ (prefixWord ++ tailWord_13110).sum := by decide
  have hdescent : baseEnd_13110 < baseStart_13110 := by decide
  rcases family_descends (prefixWord ++ tailWord_13110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13186 : List Nat := [3, 4, 2, 2, 1, 1, 1, 5]
def baseStart_13186 : Nat := 118140960795 + 13186 * 2 ^ 59
def prefixEnd_13186 : Nat := 4983230072969 + 3 ^ 40 * 13186 * 2
def baseEnd_13186 : Nat := 4012299798690751652957

theorem tailTrace_13186 : CollatzResearch.WordTrace tailWord_13186 prefixEnd_13186 4012299798690751652957 := by
  unfold tailWord_13186
  simp only [CollatzResearch.WordTrace]
  refine ⟨120233232559212208654853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 320621953491232556412941 120233232559212208654853)
  ·
    refine ⟨22543731104852289122785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120233232559212208654853 22543731104852289122785)
    ·
      refine ⟨16907798328639216842089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22543731104852289122785 16907798328639216842089)
      ·
        refine ⟨12680848746479412631567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16907798328639216842089 12680848746479412631567)
        ·
          refine ⟨19021273119719118947351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12680848746479412631567 19021273119719118947351)
          ·
            refine ⟨28531909679578678421027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19021273119719118947351 28531909679578678421027)
            ·
              refine ⟨42797864519368017631541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28531909679578678421027 42797864519368017631541)
              ·
                refine ⟨4012299798690751652957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42797864519368017631541 4012299798690751652957)
                ·
                  rfl

theorem cell19_13186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_13186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13186 prefixEnd_13186 := by exact prefixLift 13186
  have htrace : WordTrace (prefixWord ++ tailWord_13186) baseStart_13186 baseEnd_13186 := by
    simpa [prefixWord, tailWord_13186, baseEnd_13186] using wordTrace_append hprefix tailTrace_13186
  have hstable : (prefixWord ++ tailWord_13186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13186).length < 2 ^ (prefixWord ++ tailWord_13186).sum := by decide
  have hdescent : baseEnd_13186 < baseStart_13186 := by decide
  rcases family_descends (prefixWord ++ tailWord_13186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13268 : List Nat := [2, 4, 1, 2, 1, 9]
def baseStart_13268 : Nat := 118140960795 + 13268 * 2 ^ 59
def prefixEnd_13268 : Nat := 4983230072969 + 3 ^ 40 * 13268 * 2
def baseEnd_13268 : Nat := 448583461659873092279

theorem tailTrace_13268 : CollatzResearch.WordTrace tailWord_13268 prefixEnd_13268 448583461659873092279 := by
  unfold tailWord_13268
  simp only [CollatzResearch.WordTrace]
  refine ⟨241961857969888419552229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 322615810626517892736305 241961857969888419552229)
  ·
    refine ⟨45367848369354078666043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241961857969888419552229 45367848369354078666043)
    ·
      refine ⟨68051772554031117999065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45367848369354078666043 68051772554031117999065)
      ·
        refine ⟨51038829415523338499299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68051772554031117999065 51038829415523338499299)
        ·
          refine ⟨76558244123285007748949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51038829415523338499299 76558244123285007748949)
          ·
            refine ⟨448583461659873092279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 76558244123285007748949 448583461659873092279)
            ·
              rfl

theorem cell19_13268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 9].length) (baseStart_13268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13268 prefixEnd_13268 := by exact prefixLift 13268
  have htrace : WordTrace (prefixWord ++ tailWord_13268) baseStart_13268 baseEnd_13268 := by
    simpa [prefixWord, tailWord_13268, baseEnd_13268] using wordTrace_append hprefix tailTrace_13268
  have hstable : (prefixWord ++ tailWord_13268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13268).length < 2 ^ (prefixWord ++ tailWord_13268).sum := by decide
  have hdescent : baseEnd_13268 < baseStart_13268 := by decide
  rcases family_descends (prefixWord ++ tailWord_13268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13302 : List Nat := [5, 1, 1, 1, 3, 2, 3, 3]
def baseStart_13302 : Nat := 118140960795 + 13302 * 2 ^ 59
def prefixEnd_13302 : Nat := 4983230072969 + 3 ^ 40 * 13302 * 2
def baseEnd_13302 : Nat := 4047596839236853074863

theorem tailTrace_13302 : CollatzResearch.WordTrace tailWord_13302 prefixEnd_13302 4047596839236853074863 := by
  unfold tailWord_13302
  simp only [CollatzResearch.WordTrace]
  refine ⟨30322737363537540365135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 323442531877733763894773 30322737363537540365135)
  ·
    refine ⟨45484106045306310547703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30322737363537540365135 45484106045306310547703)
    ·
      refine ⟨68226159067959465821555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45484106045306310547703 68226159067959465821555)
      ·
        refine ⟨102339238601939198732333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68226159067959465821555 102339238601939198732333)
        ·
          refine ⟨38377214475727199524625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102339238601939198732333 38377214475727199524625)
          ·
            refine ⟨28782910856795399643469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38377214475727199524625 28782910856795399643469)
            ·
              refine ⟨10793591571298274866301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28782910856795399643469 10793591571298274866301)
              ·
                refine ⟨4047596839236853074863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10793591571298274866301 4047596839236853074863)
                ·
                  rfl

theorem cell19_13302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_13302 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13302 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13302 prefixEnd_13302 := by exact prefixLift 13302
  have htrace : WordTrace (prefixWord ++ tailWord_13302) baseStart_13302 baseEnd_13302 := by
    simpa [prefixWord, tailWord_13302, baseEnd_13302] using wordTrace_append hprefix tailTrace_13302
  have hstable : (prefixWord ++ tailWord_13302).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13302).length < 2 ^ (prefixWord ++ tailWord_13302).sum := by decide
  have hdescent : baseEnd_13302 < baseStart_13302 := by decide
  rcases family_descends (prefixWord ++ tailWord_13302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13526 : List Nat := [5, 2, 1, 2, 3, 1, 2, 3]
def baseStart_13526 : Nat := 118140960795 + 13526 * 2 ^ 59
def prefixEnd_13526 : Nat := 4983230072969 + 3 ^ 40 * 13526 * 2
def baseEnd_13526 : Nat := 4115756641670704096475

theorem tailTrace_13526 : CollatzResearch.WordTrace tailWord_13526 prefixEnd_13526 4115756641670704096475 := by
  unfold tailWord_13526
  simp only [CollatzResearch.WordTrace]
  refine ⟨30833359312817931374777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 328889166003391267997621 30833359312817931374777)
  ·
    refine ⟨23125019484613448531083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30833359312817931374777 23125019484613448531083)
    ·
      refine ⟨34687529226920172796625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23125019484613448531083 34687529226920172796625)
      ·
        refine ⟨26015646920190129597469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34687529226920172796625 26015646920190129597469)
        ·
          refine ⟨9755867595071298599051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26015646920190129597469 9755867595071298599051)
          ·
            refine ⟨14633801392606947898577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9755867595071298599051 14633801392606947898577)
            ·
              refine ⟨10975351044455210923933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14633801392606947898577 10975351044455210923933)
              ·
                refine ⟨4115756641670704096475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10975351044455210923933 4115756641670704096475)
                ·
                  rfl

theorem cell19_13526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_13526 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13526 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13526 prefixEnd_13526 := by exact prefixLift 13526
  have htrace : WordTrace (prefixWord ++ tailWord_13526) baseStart_13526 baseEnd_13526 := by
    simpa [prefixWord, tailWord_13526, baseEnd_13526] using wordTrace_append hprefix tailTrace_13526
  have hstable : (prefixWord ++ tailWord_13526).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13526).length < 2 ^ (prefixWord ++ tailWord_13526).sum := by decide
  have hdescent : baseEnd_13526 < baseStart_13526 := by decide
  rcases family_descends (prefixWord ++ tailWord_13526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13551 : List Nat := [1, 1, 2, 1, 8, 1, 5]
def baseStart_13551 : Nat := 118140960795 + 13551 * 2 ^ 59
def prefixEnd_13551 : Nat := 4983230072969 + 3 ^ 40 * 13551 * 2
def baseEnd_13551 : Nat := 1374454587492684513617

theorem tailTrace_13551 : CollatzResearch.WordTrace tailWord_13551 prefixEnd_13551 1374454587492684513617 := by
  unfold tailWord_13551
  simp only [CollatzResearch.WordTrace]
  refine ⟨494245573914516171656507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 329497049276344114437671 494245573914516171656507)
  ·
    refine ⟨741368360871774257484761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 494245573914516171656507 741368360871774257484761)
    ·
      refine ⟨556026270653830693113571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 741368360871774257484761 556026270653830693113571)
      ·
        refine ⟨834039405980746039670357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556026270653830693113571 834039405980746039670357)
        ·
          refine ⟨9773899288836867652387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 834039405980746039670357 9773899288836867652387)
          ·
            refine ⟨14660848933255301478581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9773899288836867652387 14660848933255301478581)
            ·
              refine ⟨1374454587492684513617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14660848933255301478581 1374454587492684513617)
              ·
                rfl

theorem cell19_13551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 5].length) (baseStart_13551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13551 prefixEnd_13551 := by exact prefixLift 13551
  have htrace : WordTrace (prefixWord ++ tailWord_13551) baseStart_13551 baseEnd_13551 := by
    simpa [prefixWord, tailWord_13551, baseEnd_13551] using wordTrace_append hprefix tailTrace_13551
  have hstable : (prefixWord ++ tailWord_13551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13551).length < 2 ^ (prefixWord ++ tailWord_13551).sum := by decide
  have hdescent : baseEnd_13551 < baseStart_13551 := by decide
  rcases family_descends (prefixWord ++ tailWord_13551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13555 : List Nat := [1, 1, 1, 2, 2, 5, 7]
def baseStart_13555 : Nat := 118140960795 + 13555 * 2 ^ 59
def prefixEnd_13555 : Nat := 4983230072969 + 3 ^ 40 * 13555 * 2
def baseEnd_13555 : Nat := 1374860300602409817317

theorem tailTrace_13555 : CollatzResearch.WordTrace tailWord_13555 prefixEnd_13555 1374860300602409817317 := by
  unfold tailWord_13555
  simp only [CollatzResearch.WordTrace]
  refine ⟨494391465900024854802119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 329594310600016569868079 494391465900024854802119)
  ·
    refine ⟨741587198850037282203179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 494391465900024854802119 741587198850037282203179)
    ·
      refine ⟨1112380798275055923304769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741587198850037282203179 1112380798275055923304769)
      ·
        refine ⟨834285598706291942478577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1112380798275055923304769 834285598706291942478577)
        ·
          refine ⟨625714199029718956858933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834285598706291942478577 625714199029718956858933)
          ·
            refine ⟨58660706159036152205525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 625714199029718956858933 58660706159036152205525)
            ·
              refine ⟨1374860300602409817317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58660706159036152205525 1374860300602409817317)
              ·
                rfl

theorem cell19_13555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_13555 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13555 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13555 prefixEnd_13555 := by exact prefixLift 13555
  have htrace : WordTrace (prefixWord ++ tailWord_13555) baseStart_13555 baseEnd_13555 := by
    simpa [prefixWord, tailWord_13555, baseEnd_13555] using wordTrace_append hprefix tailTrace_13555
  have hstable : (prefixWord ++ tailWord_13555).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13555).length < 2 ^ (prefixWord ++ tailWord_13555).sum := by decide
  have hdescent : baseEnd_13555 < baseStart_13555 := by decide
  rcases family_descends (prefixWord ++ tailWord_13555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13572 : List Nat := [2, 3, 2, 2, 2, 1, 1, 6]
def baseStart_13572 : Nat := 118140960795 + 13572 * 2 ^ 59
def prefixEnd_13572 : Nat := 4983230072969 + 3 ^ 40 * 13572 * 2
def baseEnd_13572 : Nat := 4129753743956227074127

theorem tailTrace_13572 : CollatzResearch.WordTrace tailWord_13572 prefixEnd_13572 4129753743956227074127 := by
  unfold tailWord_13572
  simp only [CollatzResearch.WordTrace]
  refine ⟨247505753419218379085485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 330007671225624505447313 247505753419218379085485)
  ·
    refine ⟨92814657532206892157057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 247505753419218379085485 92814657532206892157057)
    ·
      refine ⟨69610993149155169117793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92814657532206892157057 69610993149155169117793)
      ·
        refine ⟨52208244861866376838345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69610993149155169117793 52208244861866376838345)
        ·
          refine ⟨39156183646399782628759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52208244861866376838345 39156183646399782628759)
          ·
            refine ⟨58734275469599673943139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39156183646399782628759 58734275469599673943139)
            ·
              refine ⟨88101413204399510914709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58734275469599673943139 88101413204399510914709)
              ·
                refine ⟨4129753743956227074127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88101413204399510914709 4129753743956227074127)
                ·
                  rfl

theorem cell19_13572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_13572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13572 prefixEnd_13572 := by exact prefixLift 13572
  have htrace : WordTrace (prefixWord ++ tailWord_13572) baseStart_13572 baseEnd_13572 := by
    simpa [prefixWord, tailWord_13572, baseEnd_13572] using wordTrace_append hprefix tailTrace_13572
  have hstable : (prefixWord ++ tailWord_13572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13572).length < 2 ^ (prefixWord ++ tailWord_13572).sum := by decide
  have hdescent : baseEnd_13572 < baseStart_13572 := by decide
  rcases family_descends (prefixWord ++ tailWord_13572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13610 : List Nat := [3, 1, 4, 2, 1, 8]
def baseStart_13610 : Nat := 118140960795 + 13610 * 2 ^ 59
def prefixEnd_13610 : Nat := 4983230072969 + 3 ^ 40 * 13610 * 2
def baseEnd_13610 : Nat := 460146285287044247731

theorem tailTrace_13610 : CollatzResearch.WordTrace tailWord_13610 prefixEnd_13610 460146285287044247731 := by
  unfold tailWord_13610
  simp only [CollatzResearch.WordTrace]
  refine ⟨124099370175192312013571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 330931653800512832036189 124099370175192312013571)
  ·
    refine ⟨186149055262788468020357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124099370175192312013571 186149055262788468020357)
    ·
      refine ⟨34902947861772837753817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186149055262788468020357 34902947861772837753817)
      ·
        refine ⟨26177210896329628315363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34902947861772837753817 26177210896329628315363)
        ·
          refine ⟨39265816344494442473045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26177210896329628315363 39265816344494442473045)
          ·
            refine ⟨460146285287044247731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 39265816344494442473045 460146285287044247731)
            ·
              rfl

theorem cell19_13610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 8].length) (baseStart_13610 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13610 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13610 prefixEnd_13610 := by exact prefixLift 13610
  have htrace : WordTrace (prefixWord ++ tailWord_13610) baseStart_13610 baseEnd_13610 := by
    simpa [prefixWord, tailWord_13610, baseEnd_13610] using wordTrace_append hprefix tailTrace_13610
  have hstable : (prefixWord ++ tailWord_13610).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13610).length < 2 ^ (prefixWord ++ tailWord_13610).sum := by decide
  have hdescent : baseEnd_13610 < baseStart_13610 := by decide
  rcases family_descends (prefixWord ++ tailWord_13610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13625 : List Nat := [1, 2, 1, 6, 3, 1, 1, 4]
def baseStart_13625 : Nat := 118140960795 + 13625 * 2 ^ 59
def prefixEnd_13625 : Nat := 4983230072969 + 3 ^ 40 * 13625 * 2
def baseEnd_13625 : Nat := 4145880840067807896205

theorem tailTrace_13625 : CollatzResearch.WordTrace tailWord_13625 prefixEnd_13625 4145880840067807896205 := by
  unfold tailWord_13625
  simp only [CollatzResearch.WordTrace]
  refine ⟨496944575646426809850329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 331296383764284539900219 496944575646426809850329)
  ·
    refine ⟨372708431734820107387747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 496944575646426809850329 372708431734820107387747)
    ·
      refine ⟨559062647602230161081621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372708431734820107387747 559062647602230161081621)
      ·
        refine ⟨26206061606354538800701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 559062647602230161081621 26206061606354538800701)
        ·
          refine ⟨9827273102382952050263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26206061606354538800701 9827273102382952050263)
          ·
            refine ⟨14740909653574428075395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9827273102382952050263 14740909653574428075395)
            ·
              refine ⟨22111364480361642113093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14740909653574428075395 22111364480361642113093)
              ·
                refine ⟨4145880840067807896205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22111364480361642113093 4145880840067807896205)
                ·
                  rfl

theorem cell19_13625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 4].length) (baseStart_13625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13625 prefixEnd_13625 := by exact prefixLift 13625
  have htrace : WordTrace (prefixWord ++ tailWord_13625) baseStart_13625 baseEnd_13625 := by
    simpa [prefixWord, tailWord_13625, baseEnd_13625] using wordTrace_append hprefix tailTrace_13625
  have hstable : (prefixWord ++ tailWord_13625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13625).length < 2 ^ (prefixWord ++ tailWord_13625).sum := by decide
  have hdescent : baseEnd_13625 < baseStart_13625 := by decide
  rcases family_descends (prefixWord ++ tailWord_13625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13648 : List Nat := [2, 1, 1, 1, 1, 5, 5, 3]
def baseStart_13648 : Nat := 118140960795 + 13648 * 2 ^ 59
def prefixEnd_13648 : Nat := 4983230072969 + 3 ^ 40 * 13648 * 2
def baseEnd_13648 : Nat := 4152879391210569385031

theorem tailTrace_13648 : CollatzResearch.WordTrace tailWord_13648 prefixEnd_13648 4152879391210569385031 := by
  unfold tailWord_13648
  simp only [CollatzResearch.WordTrace]
  refine ⟨248891727281550868968799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 331855636375401158625065 248891727281550868968799)
  ·
    refine ⟨373337590922326303453199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248891727281550868968799 373337590922326303453199)
    ·
      refine ⟨560006386383489455179799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373337590922326303453199 560006386383489455179799)
      ·
        refine ⟨840009579575234182769699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560006386383489455179799 840009579575234182769699)
        ·
          refine ⟨1260014369362851274154549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840009579575234182769699 1260014369362851274154549)
          ·
            refine ⟨118126347127767306951989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1260014369362851274154549 118126347127767306951989)
            ·
              refine ⟨11074345043228185026749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118126347127767306951989 11074345043228185026749)
              ·
                refine ⟨4152879391210569385031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11074345043228185026749 4152879391210569385031)
                ·
                  rfl

theorem cell19_13648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_13648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13648 prefixEnd_13648 := by exact prefixLift 13648
  have htrace : WordTrace (prefixWord ++ tailWord_13648) baseStart_13648 baseEnd_13648 := by
    simpa [prefixWord, tailWord_13648, baseEnd_13648] using wordTrace_append hprefix tailTrace_13648
  have hstable : (prefixWord ++ tailWord_13648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13648).length < 2 ^ (prefixWord ++ tailWord_13648).sum := by decide
  have hdescent : baseEnd_13648 < baseStart_13648 := by decide
  rcases family_descends (prefixWord ++ tailWord_13648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13669 : List Nat := [1, 3, 1, 3, 1, 2, 8]
def baseStart_13669 : Nat := 118140960795 + 13669 * 2 ^ 59
def prefixEnd_13669 : Nat := 4983230072969 + 3 ^ 40 * 13669 * 2
def baseEnd_13669 : Nat := 1386423124229580972769

theorem tailTrace_13669 : CollatzResearch.WordTrace tailWord_13669 prefixEnd_13669 1386423124229580972769 := by
  unfold tailWord_13669
  simp only [CollatzResearch.WordTrace]
  refine ⟨498549387487022324452061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 332366258324681549634707 498549387487022324452061)
  ·
    refine ⟨186956020307633371669523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 498549387487022324452061 186956020307633371669523)
    ·
      refine ⟨280434030461450057504285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186956020307633371669523 280434030461450057504285)
      ·
        refine ⟨105162761423043771564107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280434030461450057504285 105162761423043771564107)
        ·
          refine ⟨157744142134565657346161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105162761423043771564107 157744142134565657346161)
          ·
            refine ⟨118308106600924243009621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157744142134565657346161 118308106600924243009621)
            ·
              refine ⟨1386423124229580972769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 118308106600924243009621 1386423124229580972769)
              ·
                rfl

theorem cell19_13669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_13669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13669 prefixEnd_13669 := by exact prefixLift 13669
  have htrace : WordTrace (prefixWord ++ tailWord_13669) baseStart_13669 baseEnd_13669 := by
    simpa [prefixWord, tailWord_13669, baseEnd_13669] using wordTrace_append hprefix tailTrace_13669
  have hstable : (prefixWord ++ tailWord_13669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13669).length < 2 ^ (prefixWord ++ tailWord_13669).sum := by decide
  have hdescent : baseEnd_13669 < baseStart_13669 := by decide
  rcases family_descends (prefixWord ++ tailWord_13669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13703 : List Nat := [1, 1, 4, 2, 2, 4, 2, 3]
def baseStart_13703 : Nat := 118140960795 + 13703 * 2 ^ 59
def prefixEnd_13703 : Nat := 4983230072969 + 3 ^ 40 * 13703 * 2
def baseEnd_13703 : Nat := 4169615056986738162659

theorem tailTrace_13703 : CollatzResearch.WordTrace tailWord_13703 prefixEnd_13703 4169615056986738162659 := by
  unfold tailWord_13703
  simp only [CollatzResearch.WordTrace]
  refine ⟨499789469363846131189763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 333192979575897420793175 499789469363846131189763)
  ·
    refine ⟨749684204045769196784645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 499789469363846131189763 749684204045769196784645)
    ·
      refine ⟨140565788258581724397121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 749684204045769196784645 140565788258581724397121)
      ·
        refine ⟨105424341193936293297841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140565788258581724397121 105424341193936293297841)
        ·
          refine ⟨79068255895452219973381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105424341193936293297841 79068255895452219973381)
          ·
            refine ⟨14825297980397291245009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79068255895452219973381 14825297980397291245009)
            ·
              refine ⟨11118973485297968433757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14825297980397291245009 11118973485297968433757)
              ·
                refine ⟨4169615056986738162659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11118973485297968433757 4169615056986738162659)
                ·
                  rfl

theorem cell19_13703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 3].length) (baseStart_13703 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13703 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13703 prefixEnd_13703 := by exact prefixLift 13703
  have htrace : WordTrace (prefixWord ++ tailWord_13703) baseStart_13703 baseEnd_13703 := by
    simpa [prefixWord, tailWord_13703, baseEnd_13703] using wordTrace_append hprefix tailTrace_13703
  have hstable : (prefixWord ++ tailWord_13703).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13703).length < 2 ^ (prefixWord ++ tailWord_13703).sum := by decide
  have hdescent : baseEnd_13703 < baseStart_13703 := by decide
  rcases family_descends (prefixWord ++ tailWord_13703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13705 : List Nat := [1, 2, 1, 1, 7, 1, 1, 5]
def baseStart_13705 : Nat := 118140960795 + 13705 * 2 ^ 59
def prefixEnd_13705 : Nat := 4983230072969 + 3 ^ 40 * 13705 * 2
def baseEnd_13705 : Nat := 4170223626651326118209

theorem tailTrace_13705 : CollatzResearch.WordTrace tailWord_13705 prefixEnd_13705 4170223626651326118209 := by
  unfold tailWord_13705
  simp only [CollatzResearch.WordTrace]
  refine ⟨499862415356600472762569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 333241610237733648508379 499862415356600472762569)
  ·
    refine ⟨374896811517450354571927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 499862415356600472762569 374896811517450354571927)
    ·
      refine ⟨562345217276175531857891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374896811517450354571927 562345217276175531857891)
      ·
        refine ⟨843517825914263297786837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562345217276175531857891 843517825914263297786837)
        ·
          refine ⟨19769949044865546041879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 843517825914263297786837 19769949044865546041879)
          ·
            refine ⟨29654923567298319062819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19769949044865546041879 29654923567298319062819)
            ·
              refine ⟨44482385350947478594229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29654923567298319062819 44482385350947478594229)
              ·
                refine ⟨4170223626651326118209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44482385350947478594229 4170223626651326118209)
                ·
                  rfl

theorem cell19_13705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_13705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13705 prefixEnd_13705 := by exact prefixLift 13705
  have htrace : WordTrace (prefixWord ++ tailWord_13705) baseStart_13705 baseEnd_13705 := by
    simpa [prefixWord, tailWord_13705, baseEnd_13705] using wordTrace_append hprefix tailTrace_13705
  have hstable : (prefixWord ++ tailWord_13705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13705).length < 2 ^ (prefixWord ++ tailWord_13705).sum := by decide
  have hdescent : baseEnd_13705 < baseStart_13705 := by decide
  rcases family_descends (prefixWord ++ tailWord_13705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13707 : List Nat := [1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_13707 : Nat := 118140960795 + 13707 * 2 ^ 59
def prefixEnd_13707 : Nat := 4983230072969 + 3 ^ 40 * 13707 * 2
def baseEnd_13707 : Nat := 4170832196315914073759

theorem tailTrace_13707 : CollatzResearch.WordTrace tailWord_13707 prefixEnd_13707 4170832196315914073759 := by
  unfold tailWord_13707
  simp only [CollatzResearch.WordTrace]
  refine ⟨499935361349354814335375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 333290240899569876223583 499935361349354814335375)
  ·
    refine ⟨749903042024032221503063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 499935361349354814335375 749903042024032221503063)
    ·
      refine ⟨1124854563036048332254595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749903042024032221503063 1124854563036048332254595)
      ·
        refine ⟨1687281844554072498381893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1124854563036048332254595 1687281844554072498381893)
        ·
          refine ⟨316365345853888593446605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1687281844554072498381893 316365345853888593446605)
          ·
            refine ⟨118637004695208222542477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316365345853888593446605 118637004695208222542477)
            ·
              refine ⟨44488876760703083453429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118637004695208222542477 44488876760703083453429)
              ·
                refine ⟨4170832196315914073759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44488876760703083453429 4170832196315914073759)
                ·
                  rfl

theorem cell19_13707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_13707 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13707 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13707 prefixEnd_13707 := by exact prefixLift 13707
  have htrace : WordTrace (prefixWord ++ tailWord_13707) baseStart_13707 baseEnd_13707 := by
    simpa [prefixWord, tailWord_13707, baseEnd_13707] using wordTrace_append hprefix tailTrace_13707
  have hstable : (prefixWord ++ tailWord_13707).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13707).length < 2 ^ (prefixWord ++ tailWord_13707).sum := by decide
  have hdescent : baseEnd_13707 < baseStart_13707 := by decide
  rcases family_descends (prefixWord ++ tailWord_13707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13741 : List Nat := [1, 5, 2, 2, 1, 2, 2, 4]
def baseStart_13741 : Nat := 118140960795 + 13741 * 2 ^ 59
def prefixEnd_13741 : Nat := 4983230072969 + 3 ^ 40 * 13741 * 2
def baseEnd_13741 : Nat := 4181177880613909318111

theorem tailTrace_13741 : CollatzResearch.WordTrace tailWord_13741 prefixEnd_13741 4181177880613909318111 := by
  unfold tailWord_13741
  simp only [CollatzResearch.WordTrace]
  refine ⟨501175443226178621073077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 334116962150785747382051 501175443226178621073077)
  ·
    refine ⟨46985197802454245725601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 501175443226178621073077 46985197802454245725601)
    ·
      refine ⟨35238898351840684294201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46985197802454245725601 35238898351840684294201)
      ·
        refine ⟨26429173763880513220651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35238898351840684294201 26429173763880513220651)
        ·
          refine ⟨39643760645820769830977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26429173763880513220651 39643760645820769830977)
          ·
            refine ⟨29732820484365577373233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39643760645820769830977 29732820484365577373233)
            ·
              refine ⟨22299615363274183029925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29732820484365577373233 22299615363274183029925)
              ·
                refine ⟨4181177880613909318111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22299615363274183029925 4181177880613909318111)
                ·
                  rfl

theorem cell19_13741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_13741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13741 prefixEnd_13741 := by exact prefixLift 13741
  have htrace : WordTrace (prefixWord ++ tailWord_13741) baseStart_13741 baseEnd_13741 := by
    simpa [prefixWord, tailWord_13741, baseEnd_13741] using wordTrace_append hprefix tailTrace_13741
  have hstable : (prefixWord ++ tailWord_13741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13741).length < 2 ^ (prefixWord ++ tailWord_13741).sum := by decide
  have hdescent : baseEnd_13741 < baseStart_13741 := by decide
  rcases family_descends (prefixWord ++ tailWord_13741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13838 : List Nat := [4, 1, 1, 2, 4, 1, 6]
def baseStart_13838 : Nat := 118140960795 + 13838 * 2 ^ 59
def prefixEnd_13838 : Nat := 4983230072969 + 3 ^ 40 * 13838 * 2
def baseEnd_13838 : Nat := 1403564503115475054097

theorem tailTrace_13838 : CollatzResearch.WordTrace tailWord_13838 prefixEnd_13838 1403564503115475054097 := by
  unfold tailWord_13838
  simp only [CollatzResearch.WordTrace]
  refine ⟨63089165484345523419271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 336475549249842791569445 63089165484345523419271)
  ·
    refine ⟨94633748226518285128907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63089165484345523419271 94633748226518285128907)
    ·
      refine ⟨141950622339777427693361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94633748226518285128907 141950622339777427693361)
      ·
        refine ⟨106462966754833070770021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141950622339777427693361 106462966754833070770021)
        ·
          refine ⟨19961806266531200769379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106462966754833070770021 19961806266531200769379)
          ·
            refine ⟨29942709399796801154069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19961806266531200769379 29942709399796801154069)
            ·
              refine ⟨1403564503115475054097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29942709399796801154069 1403564503115475054097)
              ·
                rfl

theorem cell19_13838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_13838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13838 prefixEnd_13838 := by exact prefixLift 13838
  have htrace : WordTrace (prefixWord ++ tailWord_13838) baseStart_13838 baseEnd_13838 := by
    simpa [prefixWord, tailWord_13838, baseEnd_13838] using wordTrace_append hprefix tailTrace_13838
  have hstable : (prefixWord ++ tailWord_13838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13838).length < 2 ^ (prefixWord ++ tailWord_13838).sum := by decide
  have hdescent : baseEnd_13838 < baseStart_13838 := by decide
  rcases family_descends (prefixWord ++ tailWord_13838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13895 : List Nat := [1, 1, 4, 1, 5, 2, 5]
def baseStart_13895 : Nat := 118140960795 + 13895 * 2 ^ 59
def prefixEnd_13895 : Nat := 4983230072969 + 3 ^ 40 * 13895 * 2
def baseEnd_13895 : Nat := 1409345914929060631823

theorem tailTrace_13895 : CollatzResearch.WordTrace tailWord_13895 prefixEnd_13895 1409345914929060631823 := by
  unfold tailWord_13895
  simp only [CollatzResearch.WordTrace]
  refine ⟨506792284668262922179139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 337861523112175281452759 506792284668262922179139)
  ·
    refine ⟨760188427002394383268709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 506792284668262922179139 760188427002394383268709)
    ·
      refine ⟨142535330062948946862883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 760188427002394383268709 142535330062948946862883)
      ·
        refine ⟨213802995094423420294325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142535330062948946862883 213802995094423420294325)
        ·
          refine ⟨20044030790102195652593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213802995094423420294325 20044030790102195652593)
          ·
            refine ⟨15033023092576646739445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20044030790102195652593 15033023092576646739445)
            ·
              refine ⟨1409345914929060631823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15033023092576646739445 1409345914929060631823)
              ·
                rfl

theorem cell19_13895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_13895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13895 prefixEnd_13895 := by exact prefixLift 13895
  have htrace : WordTrace (prefixWord ++ tailWord_13895) baseStart_13895 baseEnd_13895 := by
    simpa [prefixWord, tailWord_13895, baseEnd_13895] using wordTrace_append hprefix tailTrace_13895
  have hstable : (prefixWord ++ tailWord_13895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13895).length < 2 ^ (prefixWord ++ tailWord_13895).sum := by decide
  have hdescent : baseEnd_13895 < baseStart_13895 := by decide
  rcases family_descends (prefixWord ++ tailWord_13895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_13986 : List Nat := [3, 3, 1, 4, 1, 1, 3, 3]
def baseStart_13986 : Nat := 118140960795 + 13986 * 2 ^ 59
def prefixEnd_13986 : Nat := 4983230072969 + 3 ^ 40 * 13986 * 2
def baseEnd_13986 : Nat := 4255727664525933872999

theorem tailTrace_13986 : CollatzResearch.WordTrace tailWord_13986 prefixEnd_13986 4255727664525933872999 := by
  unfold tailWord_13986
  simp only [CollatzResearch.WordTrace]
  refine ⟨127527831834646365935453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 340074218225723642494541 127527831834646365935453)
  ·
    refine ⟨47822936937992387225795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127527831834646365935453 47822936937992387225795)
    ·
      refine ⟨71734405406988580838693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47822936937992387225795 71734405406988580838693)
      ·
        refine ⟨13450201013810358907255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71734405406988580838693 13450201013810358907255)
        ·
          refine ⟨20175301520715538360883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13450201013810358907255 20175301520715538360883)
          ·
            refine ⟨30262952281073307541325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20175301520715538360883 30262952281073307541325)
            ·
              refine ⟨11348607105402490327997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30262952281073307541325 11348607105402490327997)
              ·
                refine ⟨4255727664525933872999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11348607105402490327997 4255727664525933872999)
                ·
                  rfl

theorem cell19_13986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_13986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_13986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_13986 prefixEnd_13986 := by exact prefixLift 13986
  have htrace : WordTrace (prefixWord ++ tailWord_13986) baseStart_13986 baseEnd_13986 := by
    simpa [prefixWord, tailWord_13986, baseEnd_13986] using wordTrace_append hprefix tailTrace_13986
  have hstable : (prefixWord ++ tailWord_13986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_13986).length < 2 ^ (prefixWord ++ tailWord_13986).sum := by decide
  have hdescent : baseEnd_13986 < baseStart_13986 := by decide
  rcases family_descends (prefixWord ++ tailWord_13986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14030 : List Nat := [4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_14030 : Nat := 118140960795 + 14030 * 2 ^ 59
def prefixEnd_14030 : Nat := 4983230072969 + 3 ^ 40 * 14030 * 2
def baseEnd_14030 : Nat := 4269116197146868895101

theorem tailTrace_14030 : CollatzResearch.WordTrace tailWord_14030 prefixEnd_14030 4269116197146868895101 := by
  unfold tailWord_14030
  simp only [CollatzResearch.WordTrace]
  refine ⟨63964517397397622292943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 341144092786120652229029 63964517397397622292943)
  ·
    refine ⟨95946776096096433439415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63964517397397622292943 95946776096096433439415)
    ·
      refine ⟨143920164144144650159123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95946776096096433439415 143920164144144650159123)
      ·
        refine ⟨215880246216216975238685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143920164144144650159123 215880246216216975238685)
        ·
          refine ⟨80955092331081365714507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215880246216216975238685 80955092331081365714507)
          ·
            refine ⟨121432638496622048571761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80955092331081365714507 121432638496622048571761)
            ·
              refine ⟨91074478872466536428821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121432638496622048571761 91074478872466536428821)
              ·
                refine ⟨4269116197146868895101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91074478872466536428821 4269116197146868895101)
                ·
                  rfl

theorem cell19_14030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_14030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14030 prefixEnd_14030 := by exact prefixLift 14030
  have htrace : WordTrace (prefixWord ++ tailWord_14030) baseStart_14030 baseEnd_14030 := by
    simpa [prefixWord, tailWord_14030, baseEnd_14030] using wordTrace_append hprefix tailTrace_14030
  have hstable : (prefixWord ++ tailWord_14030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14030).length < 2 ^ (prefixWord ++ tailWord_14030).sum := by decide
  have hdescent : baseEnd_14030 < baseStart_14030 := by decide
  rcases family_descends (prefixWord ++ tailWord_14030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14045 : List Nat := [1, 4, 3, 3, 1, 1, 1, 5]
def baseStart_14045 : Nat := 118140960795 + 14045 * 2 ^ 59
def prefixEnd_14045 : Nat := 4983230072969 + 3 ^ 40 * 14045 * 2
def baseEnd_14045 : Nat := 4273680469631278561727

theorem tailTrace_14045 : CollatzResearch.WordTrace tailWord_14045 prefixEnd_14045 4273680469631278561727 := by
  unfold tailWord_14045
  simp only [CollatzResearch.WordTrace]
  refine ⟨512263234124838540139589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 341508822749892360093059 512263234124838540139589)
  ·
    refine ⟨96049356398407226276173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 512263234124838540139589 96049356398407226276173)
    ·
      refine ⟨36018508649402709853565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96049356398407226276173 36018508649402709853565)
      ·
        refine ⟨13506940743526016195087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36018508649402709853565 13506940743526016195087)
        ·
          refine ⟨20260411115289024292631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13506940743526016195087 20260411115289024292631)
          ·
            refine ⟨30390616672933536438947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20260411115289024292631 30390616672933536438947)
            ·
              refine ⟨45585925009400304658421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30390616672933536438947 45585925009400304658421)
              ·
                refine ⟨4273680469631278561727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45585925009400304658421 4273680469631278561727)
                ·
                  rfl

theorem cell19_14045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 5].length) (baseStart_14045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14045 prefixEnd_14045 := by exact prefixLift 14045
  have htrace : WordTrace (prefixWord ++ tailWord_14045) baseStart_14045 baseEnd_14045 := by
    simpa [prefixWord, tailWord_14045, baseEnd_14045] using wordTrace_append hprefix tailTrace_14045
  have hstable : (prefixWord ++ tailWord_14045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14045).length < 2 ^ (prefixWord ++ tailWord_14045).sum := by decide
  have hdescent : baseEnd_14045 < baseStart_14045 := by decide
  rcases family_descends (prefixWord ++ tailWord_14045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14106 : List Nat := [3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_14106 : Nat := 118140960795 + 14106 * 2 ^ 59
def prefixEnd_14106 : Nat := 4983230072969 + 3 ^ 40 * 14106 * 2
def baseEnd_14106 : Nat := 4292241844401211206005

theorem tailTrace_14106 : CollatzResearch.WordTrace tailWord_14106 prefixEnd_14106 4292241844401211206005 := by
  unfold tailWord_14106
  simp only [CollatzResearch.WordTrace]
  refine ⟨128622021725961489527543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 342992057935897305406781 128622021725961489527543)
  ·
    refine ⟨192933032588942234291315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128622021725961489527543 192933032588942234291315)
    ·
      refine ⟨289399548883413351436973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192933032588942234291315 289399548883413351436973)
      ·
        refine ⟨108524830831280006788865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289399548883413351436973 108524830831280006788865)
        ·
          refine ⟨81393623123460005091649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108524830831280006788865 81393623123460005091649)
          ·
            refine ⟨61045217342595003818737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81393623123460005091649 61045217342595003818737)
            ·
              refine ⟨45783913006946252864053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61045217342595003818737 45783913006946252864053)
              ·
                refine ⟨4292241844401211206005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45783913006946252864053 4292241844401211206005)
                ·
                  rfl

theorem cell19_14106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_14106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14106 prefixEnd_14106 := by exact prefixLift 14106
  have htrace : WordTrace (prefixWord ++ tailWord_14106) baseStart_14106 baseEnd_14106 := by
    simpa [prefixWord, tailWord_14106, baseEnd_14106] using wordTrace_append hprefix tailTrace_14106
  have hstable : (prefixWord ++ tailWord_14106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14106).length < 2 ^ (prefixWord ++ tailWord_14106).sum := by decide
  have hdescent : baseEnd_14106 < baseStart_14106 := by decide
  rcases family_descends (prefixWord ++ tailWord_14106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14125 : List Nat := [1, 5, 3, 10]
def baseStart_14125 : Nat := 118140960795 + 14125 * 2 ^ 59
def prefixEnd_14125 : Nat := 4983230072969 + 3 ^ 40 * 14125 * 2
def baseEnd_14125 : Nat := 53062015508824651651

theorem tailTrace_14125 : CollatzResearch.WordTrace tailWord_14125 prefixEnd_14125 53062015508824651651 := by
  unfold tailWord_14125
  simp only [CollatzResearch.WordTrace]
  refine ⟨515181073835012203051829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 343454049223341468701219 515181073835012203051829)
  ·
    refine ⟨48298225672032394036109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 515181073835012203051829 48298225672032394036109)
    ·
      refine ⟨18111834627012147763541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48298225672032394036109 18111834627012147763541)
      ·
        refine ⟨53062015508824651651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 18111834627012147763541 53062015508824651651)
        ·
          rfl

theorem cell19_14125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 10].length) (baseStart_14125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14125 prefixEnd_14125 := by exact prefixLift 14125
  have htrace : WordTrace (prefixWord ++ tailWord_14125) baseStart_14125 baseEnd_14125 := by
    simpa [prefixWord, tailWord_14125, baseEnd_14125] using wordTrace_append hprefix tailTrace_14125
  have hstable : (prefixWord ++ tailWord_14125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14125).length < 2 ^ (prefixWord ++ tailWord_14125).sum := by decide
  have hdescent : baseEnd_14125 < baseStart_14125 := by decide
  rcases family_descends (prefixWord ++ tailWord_14125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14142 : List Nat := [4, 2, 1, 2, 2, 1, 3, 4]
def baseStart_14142 : Nat := 118140960795 + 14142 * 2 ^ 59
def prefixEnd_14142 : Nat := 4983230072969 + 3 ^ 40 * 14142 * 2
def baseEnd_14142 : Nat := 4303196098363794405907

theorem tailTrace_14142 : CollatzResearch.WordTrace tailWord_14142 prefixEnd_14142 4303196098363794405907 := by
  unfold tailWord_14142
  simp only [CollatzResearch.WordTrace]
  refine ⟨64475139346678013302585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 343867409848949404280453 64475139346678013302585)
  ·
    refine ⟨48356354510008509976939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64475139346678013302585 48356354510008509976939)
    ·
      refine ⟨72534531765012764965409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48356354510008509976939 72534531765012764965409)
      ·
        refine ⟨54400898823759573724057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72534531765012764965409 54400898823759573724057)
        ·
          refine ⟨40800674117819680293043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54400898823759573724057 40800674117819680293043)
          ·
            refine ⟨61201011176729520439565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40800674117819680293043 61201011176729520439565)
            ·
              refine ⟨22950379191273570164837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61201011176729520439565 22950379191273570164837)
              ·
                refine ⟨4303196098363794405907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22950379191273570164837 4303196098363794405907)
                ·
                  rfl

theorem cell19_14142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_14142 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14142 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14142 prefixEnd_14142 := by exact prefixLift 14142
  have htrace : WordTrace (prefixWord ++ tailWord_14142) baseStart_14142 baseEnd_14142 := by
    simpa [prefixWord, tailWord_14142, baseEnd_14142] using wordTrace_append hprefix tailTrace_14142
  have hstable : (prefixWord ++ tailWord_14142).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14142).length < 2 ^ (prefixWord ++ tailWord_14142).sum := by decide
  have hdescent : baseEnd_14142 < baseStart_14142 := by decide
  rcases family_descends (prefixWord ++ tailWord_14142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14161 : List Nat := [1, 2, 2, 1, 5, 2, 3, 3]
def baseStart_14161 : Nat := 118140960795 + 14161 * 2 ^ 59
def prefixEnd_14161 : Nat := 4983230072969 + 3 ^ 40 * 14161 * 2
def baseEnd_14161 : Nat := 4308977510177379983633

theorem tailTrace_14161 : CollatzResearch.WordTrace tailWord_14161 prefixEnd_14161 4308977510177379983633 := by
  unfold tailWord_14161
  simp only [CollatzResearch.WordTrace]
  refine ⟨516494101704590351362337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 344329401136393567574891 516494101704590351362337)
  ·
    refine ⟨387370576278442763521753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 516494101704590351362337 387370576278442763521753)
    ·
      refine ⟨290527932208832072641315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 387370576278442763521753 290527932208832072641315)
      ·
        refine ⟨435791898313248108961973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290527932208832072641315 435791898313248108961973)
        ·
          refine ⟨40855490466867010215185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 435791898313248108961973 40855490466867010215185)
          ·
            refine ⟨30641617850150257661389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40855490466867010215185 30641617850150257661389)
            ·
              refine ⟨11490606693806346623021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30641617850150257661389 11490606693806346623021)
              ·
                refine ⟨4308977510177379983633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11490606693806346623021 4308977510177379983633)
                ·
                  rfl

theorem cell19_14161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 3].length) (baseStart_14161 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14161 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14161 prefixEnd_14161 := by exact prefixLift 14161
  have htrace : WordTrace (prefixWord ++ tailWord_14161) baseStart_14161 baseEnd_14161 := by
    simpa [prefixWord, tailWord_14161, baseEnd_14161] using wordTrace_append hprefix tailTrace_14161
  have hstable : (prefixWord ++ tailWord_14161).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14161).length < 2 ^ (prefixWord ++ tailWord_14161).sum := by decide
  have hdescent : baseEnd_14161 < baseStart_14161 := by decide
  rcases family_descends (prefixWord ++ tailWord_14161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14203 : List Nat := [1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_14203 : Nat := 118140960795 + 14203 * 2 ^ 59
def prefixEnd_14203 : Nat := 4983230072969 + 3 ^ 40 * 14203 * 2
def baseEnd_14203 : Nat := 4321757473133727050185

theorem tailTrace_14203 : CollatzResearch.WordTrace tailWord_14203 prefixEnd_14203 4321757473133727050185 := by
  unfold tailWord_14203
  simp only [CollatzResearch.WordTrace]
  refine ⟨518025967552431524391263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 345350645034954349594175 518025967552431524391263)
  ·
    refine ⟨777038951328647286586895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 518025967552431524391263 777038951328647286586895)
    ·
      refine ⟨1165558426992970929880343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 777038951328647286586895 1165558426992970929880343)
      ·
        refine ⟨1748337640489456394820515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165558426992970929880343 1748337640489456394820515)
        ·
          refine ⟨2622506460734184592230773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748337640489456394820515 2622506460734184592230773)
          ·
            refine ⟨245859980693829805521635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2622506460734184592230773 245859980693829805521635)
            ·
              refine ⟨368789971040744708282453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245859980693829805521635 368789971040744708282453)
              ·
                refine ⟨4321757473133727050185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 368789971040744708282453 4321757473133727050185)
                ·
                  rfl

theorem cell19_14203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_14203 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14203 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14203 prefixEnd_14203 := by exact prefixLift 14203
  have htrace : WordTrace (prefixWord ++ tailWord_14203) baseStart_14203 baseEnd_14203 := by
    simpa [prefixWord, tailWord_14203, baseEnd_14203] using wordTrace_append hprefix tailTrace_14203
  have hstable : (prefixWord ++ tailWord_14203).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14203).length < 2 ^ (prefixWord ++ tailWord_14203).sum := by decide
  have hdescent : baseEnd_14203 < baseStart_14203 := by decide
  rcases family_descends (prefixWord ++ tailWord_14203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14216 : List Nat := [2, 1, 3, 3, 3, 2, 2, 3]
def baseStart_14216 : Nat := 118140960795 + 14216 * 2 ^ 59
def prefixEnd_14216 : Nat := 4983230072969 + 3 ^ 40 * 14216 * 2
def baseEnd_14216 : Nat := 4325713175953548761261

theorem tailTrace_14216 : CollatzResearch.WordTrace tailWord_14216 prefixEnd_14216 4325713175953548761261 := by
  unfold tailWord_14216
  simp only [CollatzResearch.WordTrace]
  refine ⟨259250058252667372307251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 345666744336889829743001 259250058252667372307251)
  ·
    refine ⟨388875087379001058460877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 259250058252667372307251 388875087379001058460877)
    ·
      refine ⟨145828157767125396922829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 388875087379001058460877 145828157767125396922829)
      ·
        refine ⟨54685559162672023846061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145828157767125396922829 54685559162672023846061)
        ·
          refine ⟨20507084686002008942273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54685559162672023846061 20507084686002008942273)
          ·
            refine ⟨15380313514501506706705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20507084686002008942273 15380313514501506706705)
            ·
              refine ⟨11535235135876130030029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15380313514501506706705 11535235135876130030029)
              ·
                refine ⟨4325713175953548761261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11535235135876130030029 4325713175953548761261)
                ·
                  rfl

theorem cell19_14216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_14216 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14216 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14216 prefixEnd_14216 := by exact prefixLift 14216
  have htrace : WordTrace (prefixWord ++ tailWord_14216) baseStart_14216 baseEnd_14216 := by
    simpa [prefixWord, tailWord_14216, baseEnd_14216] using wordTrace_append hprefix tailTrace_14216
  have hstable : (prefixWord ++ tailWord_14216).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14216).length < 2 ^ (prefixWord ++ tailWord_14216).sum := by decide
  have hdescent : baseEnd_14216 < baseStart_14216 := by decide
  rcases family_descends (prefixWord ++ tailWord_14216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14218 : List Nat := [3, 1, 2, 4, 2, 1, 1, 5]
def baseStart_14218 : Nat := 118140960795 + 14218 * 2 ^ 59
def prefixEnd_14218 : Nat := 4983230072969 + 3 ^ 40 * 14218 * 2
def baseEnd_14218 : Nat := 4326321745618136716811

theorem tailTrace_14218 : CollatzResearch.WordTrace tailWord_14218 prefixEnd_14218 4326321745618136716811 := by
  unfold tailWord_14218
  simp only [CollatzResearch.WordTrace]
  refine ⟨129643265624522271546827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 345715374998726057458205 129643265624522271546827)
  ·
    refine ⟨194464898436783407320241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129643265624522271546827 194464898436783407320241)
    ·
      refine ⟨145848673827587555490181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 194464898436783407320241 145848673827587555490181)
      ·
        refine ⟨27346626342672666654409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145848673827587555490181 27346626342672666654409)
        ·
          refine ⟨20509969757004499990807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27346626342672666654409 20509969757004499990807)
          ·
            refine ⟨30764954635506749986211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20509969757004499990807 30764954635506749986211)
            ·
              refine ⟨46147431953260124979317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30764954635506749986211 46147431953260124979317)
              ·
                refine ⟨4326321745618136716811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46147431953260124979317 4326321745618136716811)
                ·
                  rfl

theorem cell19_14218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_14218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14218 prefixEnd_14218 := by exact prefixLift 14218
  have htrace : WordTrace (prefixWord ++ tailWord_14218) baseStart_14218 baseEnd_14218 := by
    simpa [prefixWord, tailWord_14218, baseEnd_14218] using wordTrace_append hprefix tailTrace_14218
  have hstable : (prefixWord ++ tailWord_14218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14218).length < 2 ^ (prefixWord ++ tailWord_14218).sum := by decide
  have hdescent : baseEnd_14218 < baseStart_14218 := by decide
  rcases family_descends (prefixWord ++ tailWord_14218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14294 : List Nat := [5, 2, 1, 1, 3, 7]
def baseStart_14294 : Nat := 118140960795 + 14294 * 2 ^ 59
def prefixEnd_14294 : Nat := 4983230072969 + 3 ^ 40 * 14294 * 2
def baseEnd_14294 : Nat := 483271932541386558635

theorem tailTrace_14294 : CollatzResearch.WordTrace tailWord_14294 prefixEnd_14294 483271932541386558635 := by
  unfold tailWord_14294
  simp only [CollatzResearch.WordTrace]
  refine ⟨32584063138922129122121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 347563340148502710635957 32584063138922129122121)
  ·
    refine ⟨24438047354191596841591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32584063138922129122121 24438047354191596841591)
    ·
      refine ⟨36657071031287395262387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24438047354191596841591 36657071031287395262387)
      ·
        refine ⟨54985606546931092893581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36657071031287395262387 54985606546931092893581)
        ·
          refine ⟨20619602455099159835093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54985606546931092893581 20619602455099159835093)
          ·
            refine ⟨483271932541386558635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20619602455099159835093 483271932541386558635)
            ·
              rfl

theorem cell19_14294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 7].length) (baseStart_14294 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14294 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14294 prefixEnd_14294 := by exact prefixLift 14294
  have htrace : WordTrace (prefixWord ++ tailWord_14294) baseStart_14294 baseEnd_14294 := by
    simpa [prefixWord, tailWord_14294, baseEnd_14294] using wordTrace_append hprefix tailTrace_14294
  have hstable : (prefixWord ++ tailWord_14294).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14294).length < 2 ^ (prefixWord ++ tailWord_14294).sum := by decide
  have hdescent : baseEnd_14294 < baseStart_14294 := by decide
  rcases family_descends (prefixWord ++ tailWord_14294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14298 : List Nat := [3, 1, 1, 2, 12]
def baseStart_14298 : Nat := 118140960795 + 14298 * 2 ^ 59
def prefixEnd_14298 : Nat := 4983230072969 + 3 ^ 40 * 14298 * 2
def baseEnd_14298 : Nat := 161135723414876108845

theorem tailTrace_14298 : CollatzResearch.WordTrace tailWord_14298 prefixEnd_14298 161135723414876108845 := by
  unfold tailWord_14298
  simp only [CollatzResearch.WordTrace]
  refine ⟨130372725552065687274887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 347660601472175166066365 130372725552065687274887)
  ·
    refine ⟨195559088328098530912331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130372725552065687274887 195559088328098530912331)
    ·
      refine ⟨293338632492147796368497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195559088328098530912331 293338632492147796368497)
      ·
        refine ⟨220003974369110847276373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293338632492147796368497 220003974369110847276373)
        ·
          refine ⟨161135723414876108845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 220003974369110847276373 161135723414876108845)
          ·
            rfl

theorem cell19_14298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 12].length) (baseStart_14298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14298 prefixEnd_14298 := by exact prefixLift 14298
  have htrace : WordTrace (prefixWord ++ tailWord_14298) baseStart_14298 baseEnd_14298 := by
    simpa [prefixWord, tailWord_14298, baseEnd_14298] using wordTrace_append hprefix tailTrace_14298
  have hstable : (prefixWord ++ tailWord_14298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14298).length < 2 ^ (prefixWord ++ tailWord_14298).sum := by decide
  have hdescent : baseEnd_14298 < baseStart_14298 := by decide
  rcases family_descends (prefixWord ++ tailWord_14298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14311 : List Nat := [1, 1, 5, 2, 4, 1, 1, 4]
def baseStart_14311 : Nat := 118140960795 + 14311 * 2 ^ 59
def prefixEnd_14311 : Nat := 4983230072969 + 3 ^ 40 * 14311 * 2
def baseEnd_14311 : Nat := 4354620235021476649891

theorem tailTrace_14311 : CollatzResearch.WordTrace tailWord_14311 prefixEnd_14311 4354620235021476649891 := by
  unfold tailWord_14311
  simp only [CollatzResearch.WordTrace]
  refine ⟨521965051161165969322787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 347976700774110646215191 521965051161165969322787)
  ·
    refine ⟨782947576741748953984181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 521965051161165969322787 782947576741748953984181)
    ·
      refine ⟨73401335319538964436017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 782947576741748953984181 73401335319538964436017)
      ·
        refine ⟨55051001489654223327013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73401335319538964436017 55051001489654223327013)
        ·
          refine ⟨10322062779310166873815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55051001489654223327013 10322062779310166873815)
          ·
            refine ⟨15483094168965250310723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10322062779310166873815 15483094168965250310723)
            ·
              refine ⟨23224641253447875466085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15483094168965250310723 23224641253447875466085)
              ·
                refine ⟨4354620235021476649891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23224641253447875466085 4354620235021476649891)
                ·
                  rfl

theorem cell19_14311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 4].length) (baseStart_14311 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14311 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14311 prefixEnd_14311 := by exact prefixLift 14311
  have htrace : WordTrace (prefixWord ++ tailWord_14311) baseStart_14311 baseEnd_14311 := by
    simpa [prefixWord, tailWord_14311, baseEnd_14311] using wordTrace_append hprefix tailTrace_14311
  have hstable : (prefixWord ++ tailWord_14311).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14311).length < 2 ^ (prefixWord ++ tailWord_14311).sum := by decide
  have hdescent : baseEnd_14311 < baseStart_14311 := by decide
  rcases family_descends (prefixWord ++ tailWord_14311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14391 : List Nat := [1, 1, 3, 1, 2, 2, 6, 3]
def baseStart_14391 : Nat := 118140960795 + 14391 * 2 ^ 59
def prefixEnd_14391 : Nat := 4983230072969 + 3 ^ 40 * 14391 * 2
def baseEnd_14391 : Nat := 4378963021604994871895

theorem tailTrace_14391 : CollatzResearch.WordTrace tailWord_14391 prefixEnd_14391 4378963021604994871895 := by
  unfold tailWord_14391
  simp only [CollatzResearch.WordTrace]
  refine ⟨524882890871339632235027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 349921927247559754823351 524882890871339632235027)
  ·
    refine ⟨787324336307009448352541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524882890871339632235027 787324336307009448352541)
    ·
      refine ⟨295246626115128543132203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 787324336307009448352541 295246626115128543132203)
      ·
        refine ⟨442869939172692814698305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295246626115128543132203 442869939172692814698305)
        ·
          refine ⟨332152454379519611023729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442869939172692814698305 332152454379519611023729)
          ·
            refine ⟨249114340784639708267797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 332152454379519611023729 249114340784639708267797)
            ·
              refine ⟨11677234724279986325053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 249114340784639708267797 11677234724279986325053)
              ·
                refine ⟨4378963021604994871895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11677234724279986325053 4378963021604994871895)
                ·
                  rfl

theorem cell19_14391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 3].length) (baseStart_14391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14391 prefixEnd_14391 := by exact prefixLift 14391
  have htrace : WordTrace (prefixWord ++ tailWord_14391) baseStart_14391 baseEnd_14391 := by
    simpa [prefixWord, tailWord_14391, baseEnd_14391] using wordTrace_append hprefix tailTrace_14391
  have hstable : (prefixWord ++ tailWord_14391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14391).length < 2 ^ (prefixWord ++ tailWord_14391).sum := by decide
  have hdescent : baseEnd_14391 < baseStart_14391 := by decide
  rcases family_descends (prefixWord ++ tailWord_14391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14412 : List Nat := [2, 2, 1, 3, 1, 1, 9]
def baseStart_14412 : Nat := 118140960795 + 14412 * 2 ^ 59
def prefixEnd_14412 : Nat := 4983230072969 + 3 ^ 40 * 14412 * 2
def baseEnd_14412 : Nat := 1461784334361056135057

theorem tailTrace_14412 : CollatzResearch.WordTrace tailWord_14412 prefixEnd_14412 1461784334361056135057 := by
  unfold tailWord_14412
  simp only [CollatzResearch.WordTrace]
  refine ⟨262824411897630109374745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 350432549196840145832993 262824411897630109374745)
  ·
    refine ⟨197118308923222582031059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262824411897630109374745 197118308923222582031059)
    ·
      refine ⟨295677463384833873046589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197118308923222582031059 295677463384833873046589)
      ·
        refine ⟨110879048769312702392471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295677463384833873046589 110879048769312702392471)
        ·
          refine ⟨166318573153969053588707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110879048769312702392471 166318573153969053588707)
          ·
            refine ⟨249477859730953580383061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166318573153969053588707 249477859730953580383061)
            ·
              refine ⟨1461784334361056135057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 249477859730953580383061 1461784334361056135057)
              ·
                rfl

theorem cell19_14412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_14412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14412 prefixEnd_14412 := by exact prefixLift 14412
  have htrace : WordTrace (prefixWord ++ tailWord_14412) baseStart_14412 baseEnd_14412 := by
    simpa [prefixWord, tailWord_14412, baseEnd_14412] using wordTrace_append hprefix tailTrace_14412
  have hstable : (prefixWord ++ tailWord_14412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14412).length < 2 ^ (prefixWord ++ tailWord_14412).sum := by decide
  have hdescent : baseEnd_14412 < baseStart_14412 := by decide
  rcases family_descends (prefixWord ++ tailWord_14412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14469 : List Nat := [1, 3, 1, 1, 5, 8]
def baseStart_14469 : Nat := 118140960795 + 14469 * 2 ^ 59
def prefixEnd_14469 : Nat := 4983230072969 + 3 ^ 40 * 14469 * 2
def baseEnd_14469 : Nat := 489188582058213904261

theorem tailTrace_14469 : CollatzResearch.WordTrace tailWord_14469 prefixEnd_14469 489188582058213904261 := by
  unfold tailWord_14469
  simp only [CollatzResearch.WordTrace]
  refine ⟨527727784588758953574461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 351818523059172635716307 527727784588758953574461)
  ·
    refine ⟨197897919220784607590423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 527727784588758953574461 197897919220784607590423)
    ·
      refine ⟨296846878831176911385635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197897919220784607590423 296846878831176911385635)
      ·
        refine ⟨445270318246765367078453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296846878831176911385635 445270318246765367078453)
        ·
          refine ⟨41744092335634253163605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 445270318246765367078453 41744092335634253163605)
          ·
            refine ⟨489188582058213904261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 41744092335634253163605 489188582058213904261)
            ·
              rfl

theorem cell19_14469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 8].length) (baseStart_14469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14469 prefixEnd_14469 := by exact prefixLift 14469
  have htrace : WordTrace (prefixWord ++ tailWord_14469) baseStart_14469 baseEnd_14469 := by
    simpa [prefixWord, tailWord_14469, baseEnd_14469] using wordTrace_append hprefix tailTrace_14469
  have hstable : (prefixWord ++ tailWord_14469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14469).length < 2 ^ (prefixWord ++ tailWord_14469).sum := by decide
  have hdescent : baseEnd_14469 < baseStart_14469 := by decide
  rcases family_descends (prefixWord ++ tailWord_14469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14524 : List Nat := [2, 2, 2, 3, 3, 1, 6]
def baseStart_14524 : Nat := 118140960795 + 14524 * 2 ^ 59
def prefixEnd_14524 : Nat := 4983230072969 + 3 ^ 40 * 14524 * 2
def baseEnd_14524 : Nat := 1473144301433364638659

theorem tailTrace_14524 : CollatzResearch.WordTrace tailWord_14524 prefixEnd_14524 1473144301433364638659 := by
  unfold tailWord_14524
  simp only [CollatzResearch.WordTrace]
  refine ⟨264866899694751673413313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 353155866259668897884417 264866899694751673413313)
  ·
    refine ⟨198650174771063755059985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264866899694751673413313 198650174771063755059985)
    ·
      refine ⟨148987631078297816294989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198650174771063755059985 148987631078297816294989)
      ·
        refine ⟨55870361654361681110621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148987631078297816294989 55870361654361681110621)
        ·
          refine ⟨20951385620385630416483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55870361654361681110621 20951385620385630416483)
          ·
            refine ⟨31427078430578445624725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20951385620385630416483 31427078430578445624725)
            ·
              refine ⟨1473144301433364638659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31427078430578445624725 1473144301433364638659)
              ·
                rfl

theorem cell19_14524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 6].length) (baseStart_14524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14524 prefixEnd_14524 := by exact prefixLift 14524
  have htrace : WordTrace (prefixWord ++ tailWord_14524) baseStart_14524 baseEnd_14524 := by
    simpa [prefixWord, tailWord_14524, baseEnd_14524] using wordTrace_append hprefix tailTrace_14524
  have hstable : (prefixWord ++ tailWord_14524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14524).length < 2 ^ (prefixWord ++ tailWord_14524).sum := by decide
  have hdescent : baseEnd_14524 < baseStart_14524 := by decide
  rcases family_descends (prefixWord ++ tailWord_14524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14556 : List Nat := [2, 2, 5, 2, 1, 2, 2, 3]
def baseStart_14556 : Nat := 118140960795 + 14556 * 2 ^ 59
def prefixEnd_14556 : Nat := 4983230072969 + 3 ^ 40 * 14556 * 2
def baseEnd_14556 : Nat := 4429170018933501204779

theorem tailTrace_14556 : CollatzResearch.WordTrace tailWord_14556 prefixEnd_14556 4429170018933501204779 := by
  unfold tailWord_14556
  simp only [CollatzResearch.WordTrace]
  refine ⟨265450467636786405995761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 353933956849048541327681 265450467636786405995761)
  ·
    refine ⟨199087850727589804496821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 265450467636786405995761 199087850727589804496821)
    ·
      refine ⟨18664486005711544171577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199087850727589804496821 18664486005711544171577)
      ·
        refine ⟨13998364504283658128683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18664486005711544171577 13998364504283658128683)
        ·
          refine ⟨20997546756425487193025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13998364504283658128683 20997546756425487193025)
          ·
            refine ⟨15748160067319115394769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20997546756425487193025 15748160067319115394769)
            ·
              refine ⟨11811120050489336546077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15748160067319115394769 11811120050489336546077)
              ·
                refine ⟨4429170018933501204779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11811120050489336546077 4429170018933501204779)
                ·
                  rfl

theorem cell19_14556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_14556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14556 prefixEnd_14556 := by exact prefixLift 14556
  have htrace : WordTrace (prefixWord ++ tailWord_14556) baseStart_14556 baseEnd_14556 := by
    simpa [prefixWord, tailWord_14556, baseEnd_14556] using wordTrace_append hprefix tailTrace_14556
  have hstable : (prefixWord ++ tailWord_14556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14556).length < 2 ^ (prefixWord ++ tailWord_14556).sum := by decide
  have hdescent : baseEnd_14556 < baseStart_14556 := by decide
  rcases family_descends (prefixWord ++ tailWord_14556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14600 : List Nat := [2, 1, 3, 2, 3, 2, 2, 4]
def baseStart_14600 : Nat := 118140960795 + 14600 * 2 ^ 59
def prefixEnd_14600 : Nat := 4983230072969 + 3 ^ 40 * 14600 * 2
def baseEnd_14600 : Nat := 4442558551554436226881

theorem tailTrace_14600 : CollatzResearch.WordTrace tailWord_14600 prefixEnd_14600 4442558551554436226881 := by
  unfold tailWord_14600
  simp only [CollatzResearch.WordTrace]
  refine ⟨266252873557084163296627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 355003831409445551062169 266252873557084163296627)
  ·
    refine ⟨399379310335626244944941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 266252873557084163296627 399379310335626244944941)
    ·
      refine ⟨149767241375859841854353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 399379310335626244944941 149767241375859841854353)
      ·
        refine ⟨112325431031894881390765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149767241375859841854353 112325431031894881390765)
        ·
          refine ⟨42122036636960580521537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112325431031894881390765 42122036636960580521537)
          ·
            refine ⟨31591527477720435391153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42122036636960580521537 31591527477720435391153)
            ·
              refine ⟨23693645608290326543365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31591527477720435391153 23693645608290326543365)
              ·
                refine ⟨4442558551554436226881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23693645608290326543365 4442558551554436226881)
                ·
                  rfl

theorem cell19_14600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_14600 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14600 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14600 prefixEnd_14600 := by exact prefixLift 14600
  have htrace : WordTrace (prefixWord ++ tailWord_14600) baseStart_14600 baseEnd_14600 := by
    simpa [prefixWord, tailWord_14600, baseEnd_14600] using wordTrace_append hprefix tailTrace_14600
  have hstable : (prefixWord ++ tailWord_14600).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14600).length < 2 ^ (prefixWord ++ tailWord_14600).sum := by decide
  have hdescent : baseEnd_14600 < baseStart_14600 := by decide
  rcases family_descends (prefixWord ++ tailWord_14600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14602 : List Nat := [3, 1, 2, 2, 1, 1, 3, 6]
def baseStart_14602 : Nat := 118140960795 + 14602 * 2 ^ 59
def prefixEnd_14602 : Nat := 4983230072969 + 3 ^ 40 * 14602 * 2
def baseEnd_14602 : Nat := 4443167121219024182431

theorem tailTrace_14602 : CollatzResearch.WordTrace tailWord_14602 prefixEnd_14602 4443167121219024182431 := by
  unfold tailWord_14602
  simp only [CollatzResearch.WordTrace]
  refine ⟨133144673276730667041515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 355052462071281778777373 133144673276730667041515)
  ·
    refine ⟨199717009915096000562273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133144673276730667041515 199717009915096000562273)
    ·
      refine ⟨149787757436322000421705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199717009915096000562273 149787757436322000421705)
      ·
        refine ⟨112340818077241500316279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149787757436322000421705 112340818077241500316279)
        ·
          refine ⟨168511227115862250474419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112340818077241500316279 168511227115862250474419)
          ·
            refine ⟨252766840673793375711629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168511227115862250474419 252766840673793375711629)
            ·
              refine ⟨94787565252672515891861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252766840673793375711629 94787565252672515891861)
              ·
                refine ⟨4443167121219024182431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94787565252672515891861 4443167121219024182431)
                ·
                  rfl

theorem cell19_14602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_14602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14602 prefixEnd_14602 := by exact prefixLift 14602
  have htrace : WordTrace (prefixWord ++ tailWord_14602) baseStart_14602 baseEnd_14602 := by
    simpa [prefixWord, tailWord_14602, baseEnd_14602] using wordTrace_append hprefix tailTrace_14602
  have hstable : (prefixWord ++ tailWord_14602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14602).length < 2 ^ (prefixWord ++ tailWord_14602).sum := by decide
  have hdescent : baseEnd_14602 < baseStart_14602 := by decide
  rcases family_descends (prefixWord ++ tailWord_14602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14638 : List Nat := [4, 1, 3, 3, 8]
def baseStart_14638 : Nat := 118140960795 + 14638 * 2 ^ 59
def prefixEnd_14638 : Nat := 4983230072969 + 3 ^ 40 * 14638 * 2
def baseEnd_14638 : Nat := 164967458340059532679

theorem tailTrace_14638 : CollatzResearch.WordTrace tailWord_14638 prefixEnd_14638 164967458340059532679 := by
  unfold tailWord_14638
  simp only [CollatzResearch.WordTrace]
  refine ⟨66736465122062602059571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 355927813984333877651045 66736465122062602059571)
  ·
    refine ⟨100104697683093903089357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66736465122062602059571 100104697683093903089357)
    ·
      refine ⟨37539261631160213658509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100104697683093903089357 37539261631160213658509)
      ·
        refine ⟨14077223111685080121941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37539261631160213658509 14077223111685080121941)
        ·
          refine ⟨164967458340059532679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 14077223111685080121941 164967458340059532679)
          ·
            rfl

theorem cell19_14638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 8].length) (baseStart_14638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14638 prefixEnd_14638 := by exact prefixLift 14638
  have htrace : WordTrace (prefixWord ++ tailWord_14638) baseStart_14638 baseEnd_14638 := by
    simpa [prefixWord, tailWord_14638, baseEnd_14638] using wordTrace_append hprefix tailTrace_14638
  have hstable : (prefixWord ++ tailWord_14638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14638).length < 2 ^ (prefixWord ++ tailWord_14638).sum := by decide
  have hdescent : baseEnd_14638 < baseStart_14638 := by decide
  rcases family_descends (prefixWord ++ tailWord_14638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14659 : List Nat := [1, 1, 1, 3, 1, 3, 5, 4]
def baseStart_14659 : Nat := 118140960795 + 14659 * 2 ^ 59
def prefixEnd_14659 : Nat := 4983230072969 + 3 ^ 40 * 14659 * 2
def baseEnd_14659 : Nat := 4460511356659780915609

theorem tailTrace_14659 : CollatzResearch.WordTrace tailWord_14659 prefixEnd_14659 4460511356659780915609 := by
  unfold tailWord_14659
  simp only [CollatzResearch.WordTrace]
  refine ⟨534657653900421402991031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 356438435933614268660687 534657653900421402991031)
  ·
    refine ⟨801986480850632104486547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 534657653900421402991031 801986480850632104486547)
    ·
      refine ⟨1202979721275948156729821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 801986480850632104486547 1202979721275948156729821)
      ·
        refine ⟨451117395478480558773683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1202979721275948156729821 451117395478480558773683)
        ·
          refine ⟨676676093217720838160525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451117395478480558773683 676676093217720838160525)
          ·
            refine ⟨253753534956645314310197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 676676093217720838160525 253753534956645314310197)
            ·
              refine ⟨23789393902185498216581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253753534956645314310197 23789393902185498216581)
              ·
                refine ⟨4460511356659780915609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23789393902185498216581 4460511356659780915609)
                ·
                  rfl

theorem cell19_14659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_14659 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14659 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14659 prefixEnd_14659 := by exact prefixLift 14659
  have htrace : WordTrace (prefixWord ++ tailWord_14659) baseStart_14659 baseEnd_14659 := by
    simpa [prefixWord, tailWord_14659, baseEnd_14659] using wordTrace_append hprefix tailTrace_14659
  have hstable : (prefixWord ++ tailWord_14659).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14659).length < 2 ^ (prefixWord ++ tailWord_14659).sum := by decide
  have hdescent : baseEnd_14659 < baseStart_14659 := by decide
  rcases family_descends (prefixWord ++ tailWord_14659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14750 : List Nat := [4, 3, 1, 2, 1, 3, 5]
def baseStart_14750 : Nat := 118140960795 + 14750 * 2 ^ 59
def prefixEnd_14750 : Nat := 4983230072969 + 3 ^ 40 * 14750 * 2
def baseEnd_14750 : Nat := 1496067092132844297713

theorem tailTrace_14750 : CollatzResearch.WordTrace tailWord_14750 prefixEnd_14750 1496067092132844297713 := by
  unfold tailWord_14750
  simp only [CollatzResearch.WordTrace]
  refine ⟨67247087071342993069213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 358651131047162629702469 67247087071342993069213)
  ·
    refine ⟨25217657651753622400955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67247087071342993069213 25217657651753622400955)
    ·
      refine ⟨37826486477630433601433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25217657651753622400955 37826486477630433601433)
      ·
        refine ⟨28369864858222825201075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37826486477630433601433 28369864858222825201075)
        ·
          refine ⟨42554797287334237801613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28369864858222825201075 42554797287334237801613)
          ·
            refine ⟨15958048982750339175605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42554797287334237801613 15958048982750339175605)
            ·
              refine ⟨1496067092132844297713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15958048982750339175605 1496067092132844297713)
              ·
                rfl

theorem cell19_14750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_14750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14750 prefixEnd_14750 := by exact prefixLift 14750
  have htrace : WordTrace (prefixWord ++ tailWord_14750) baseStart_14750 baseEnd_14750 := by
    simpa [prefixWord, tailWord_14750, baseEnd_14750] using wordTrace_append hprefix tailTrace_14750
  have hstable : (prefixWord ++ tailWord_14750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14750).length < 2 ^ (prefixWord ++ tailWord_14750).sum := by decide
  have hdescent : baseEnd_14750 < baseStart_14750 := by decide
  rcases family_descends (prefixWord ++ tailWord_14750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14792 : List Nat := [2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_14792 : Nat := 118140960795 + 14792 * 2 ^ 59
def prefixEnd_14792 : Nat := 4983230072969 + 3 ^ 40 * 14792 * 2
def baseEnd_14792 : Nat := 4500981239354879959691

theorem tailTrace_14792 : CollatzResearch.WordTrace tailWord_14792 prefixEnd_14792 4500981239354879959691 := by
  unfold tailWord_14792
  simp only [CollatzResearch.WordTrace]
  refine ⟨269754281209292558791315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 359672374945723411721753 269754281209292558791315)
  ·
    refine ⟨404631421813938838186973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269754281209292558791315 404631421813938838186973)
    ·
      refine ⟨151736783180227064320115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404631421813938838186973 151736783180227064320115)
      ·
        refine ⟨227605174770340596480173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151736783180227064320115 227605174770340596480173)
        ·
          refine ⟨85351940538877723680065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227605174770340596480173 85351940538877723680065)
          ·
            refine ⟨64013955404158292760049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85351940538877723680065 64013955404158292760049)
            ·
              refine ⟨48010466553118719570037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64013955404158292760049 48010466553118719570037)
              ·
                refine ⟨4500981239354879959691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48010466553118719570037 4500981239354879959691)
                ·
                  rfl

theorem cell19_14792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_14792 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14792 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14792 prefixEnd_14792 := by exact prefixLift 14792
  have htrace : WordTrace (prefixWord ++ tailWord_14792) baseStart_14792 baseEnd_14792 := by
    simpa [prefixWord, tailWord_14792, baseEnd_14792] using wordTrace_append hprefix tailTrace_14792
  have hstable : (prefixWord ++ tailWord_14792).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14792).length < 2 ^ (prefixWord ++ tailWord_14792).sum := by decide
  have hdescent : baseEnd_14792 < baseStart_14792 := by decide
  rcases family_descends (prefixWord ++ tailWord_14792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14902 : List Nat := [5, 1, 2, 1, 2, 1, 4, 3]
def baseStart_14902 : Nat := 118140960795 + 14902 * 2 ^ 59
def prefixEnd_14902 : Nat := 4983230072969 + 3 ^ 40 * 14902 * 2
def baseEnd_14902 : Nat := 4534452570907217514947

theorem tailTrace_14902 : CollatzResearch.WordTrace tailWord_14902 prefixEnd_14902 4534452570907217514947 := by
  unfold tailWord_14902
  simp only [CollatzResearch.WordTrace]
  refine ⟨33970037001254619005435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 362347061346715936057973 33970037001254619005435)
  ·
    refine ⟨50955055501881928508153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33970037001254619005435 50955055501881928508153)
    ·
      refine ⟨38216291626411446381115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50955055501881928508153 38216291626411446381115)
      ·
        refine ⟨57324437439617169571673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38216291626411446381115 57324437439617169571673)
        ·
          refine ⟨42993328079712877178755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57324437439617169571673 42993328079712877178755)
          ·
            refine ⟨64489992119569315768133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42993328079712877178755 64489992119569315768133)
            ·
              refine ⟨12091873522419246706525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64489992119569315768133 12091873522419246706525)
              ·
                refine ⟨4534452570907217514947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12091873522419246706525 4534452570907217514947)
                ·
                  rfl

theorem cell19_14902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_14902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14902 prefixEnd_14902 := by exact prefixLift 14902
  have htrace : WordTrace (prefixWord ++ tailWord_14902) baseStart_14902 baseEnd_14902 := by
    simpa [prefixWord, tailWord_14902, baseEnd_14902] using wordTrace_append hprefix tailTrace_14902
  have hstable : (prefixWord ++ tailWord_14902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14902).length < 2 ^ (prefixWord ++ tailWord_14902).sum := by decide
  have hdescent : baseEnd_14902 < baseStart_14902 := by decide
  rcases family_descends (prefixWord ++ tailWord_14902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14906 : List Nat := [3, 1, 1, 1, 3, 4, 1, 5]
def baseStart_14906 : Nat := 118140960795 + 14906 * 2 ^ 59
def prefixEnd_14906 : Nat := 4983230072969 + 3 ^ 40 * 14906 * 2
def baseEnd_14906 : Nat := 4535669710236393426047

theorem tailTrace_14906 : CollatzResearch.WordTrace tailWord_14906 prefixEnd_14906 4535669710236393426047 := by
  unfold tailWord_14906
  simp only [CollatzResearch.WordTrace]
  refine ⟨135916621001395646808143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 362444322670388391488381 135916621001395646808143)
  ·
    refine ⟨203874931502093470212215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135916621001395646808143 203874931502093470212215)
    ·
      refine ⟨305812397253140205318323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203874931502093470212215 305812397253140205318323)
      ·
        refine ⟨458718595879710307977485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305812397253140205318323 458718595879710307977485)
        ·
          refine ⟨172019473454891365491557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 458718595879710307977485 172019473454891365491557)
          ·
            refine ⟨32253651272792131029667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172019473454891365491557 32253651272792131029667)
            ·
              refine ⟨48380476909188196544501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32253651272792131029667 48380476909188196544501)
              ·
                refine ⟨4535669710236393426047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48380476909188196544501 4535669710236393426047)
                ·
                  rfl

theorem cell19_14906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_14906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14906 prefixEnd_14906 := by exact prefixLift 14906
  have htrace : WordTrace (prefixWord ++ tailWord_14906) baseStart_14906 baseEnd_14906 := by
    simpa [prefixWord, tailWord_14906, baseEnd_14906] using wordTrace_append hprefix tailTrace_14906
  have hstable : (prefixWord ++ tailWord_14906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14906).length < 2 ^ (prefixWord ++ tailWord_14906).sum := by decide
  have hdescent : baseEnd_14906 < baseStart_14906 := by decide
  rcases family_descends (prefixWord ++ tailWord_14906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14927 : List Nat := [1, 1, 2, 1, 1, 2, 11]
def baseStart_14927 : Nat := 118140960795 + 14927 * 2 ^ 59
def prefixEnd_14927 : Nat := 4983230072969 + 3 ^ 40 * 14927 * 2
def baseEnd_14927 : Nat := 1514019897238188986441

theorem tailTrace_14927 : CollatzResearch.WordTrace tailWord_14927 prefixEnd_14927 1514019897238188986441 := by
  unfold tailWord_14927
  simp only [CollatzResearch.WordTrace]
  refine ⟨544432416929503173747035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 362954944619668782498023 544432416929503173747035)
  ·
    refine ⟨816648625394254760620553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 544432416929503173747035 816648625394254760620553)
    ·
      refine ⟨612486469045691070465415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 816648625394254760620553 612486469045691070465415)
      ·
        refine ⟨918729703568536605698123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 612486469045691070465415 918729703568536605698123)
        ·
          refine ⟨1378094555352804908547185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918729703568536605698123 1378094555352804908547185)
          ·
            refine ⟨1033570916514603681410389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378094555352804908547185 1033570916514603681410389)
            ·
              refine ⟨1514019897238188986441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1033570916514603681410389 1514019897238188986441)
              ·
                rfl

theorem cell19_14927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_14927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14927 prefixEnd_14927 := by exact prefixLift 14927
  have htrace : WordTrace (prefixWord ++ tailWord_14927) baseStart_14927 baseEnd_14927 := by
    simpa [prefixWord, tailWord_14927, baseEnd_14927] using wordTrace_append hprefix tailTrace_14927
  have hstable : (prefixWord ++ tailWord_14927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14927).length < 2 ^ (prefixWord ++ tailWord_14927).sum := by decide
  have hdescent : baseEnd_14927 < baseStart_14927 := by decide
  rcases family_descends (prefixWord ++ tailWord_14927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14978 : List Nat := [3, 4, 3, 1, 8]
def baseStart_14978 : Nat := 118140960795 + 14978 * 2 ^ 59
def prefixEnd_14978 : Nat := 4983230072969 + 3 ^ 40 * 14978 * 2
def baseEnd_14978 : Nat := 168799193265242956513

theorem tailTrace_14978 : CollatzResearch.WordTrace tailWord_14978 prefixEnd_14978 168799193265242956513 := by
  unfold tailWord_14978
  simp only [CollatzResearch.WordTrace]
  refine ⟨136573134936184720963397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 364195026496492589235725 136573134936184720963397)
  ·
    refine ⟨25607462800534635180637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136573134936184720963397 25607462800534635180637)
    ·
      refine ⟨9602798550200488192739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25607462800534635180637 9602798550200488192739)
      ·
        refine ⟨14404197825300732289109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9602798550200488192739 14404197825300732289109)
        ·
          refine ⟨168799193265242956513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 14404197825300732289109 168799193265242956513)
          ·
            rfl

theorem cell19_14978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 8].length) (baseStart_14978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14978 prefixEnd_14978 := by exact prefixLift 14978
  have htrace : WordTrace (prefixWord ++ tailWord_14978) baseStart_14978 baseEnd_14978 := by
    simpa [prefixWord, tailWord_14978, baseEnd_14978] using wordTrace_append hprefix tailTrace_14978
  have hstable : (prefixWord ++ tailWord_14978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14978).length < 2 ^ (prefixWord ++ tailWord_14978).sum := by decide
  have hdescent : baseEnd_14978 < baseStart_14978 := by decide
  rcases family_descends (prefixWord ++ tailWord_14978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_14984 : List Nat := [2, 1, 3, 13]
def baseStart_14984 : Nat := 118140960795 + 14984 * 2 ^ 59
def prefixEnd_14984 : Nat := 4983230072969 + 3 ^ 40 * 14984 * 2
def baseEnd_14984 : Nat := 56288937372287946821

theorem tailTrace_14984 : CollatzResearch.WordTrace tailWord_14984 prefixEnd_14984 56288937372287946821 := by
  unfold tailWord_14984
  simp only [CollatzResearch.WordTrace]
  refine ⟨273255688861500954286003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 364340918482001272381337 273255688861500954286003)
  ·
    refine ⟨409883533292251431429005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273255688861500954286003 409883533292251431429005)
    ·
      refine ⟨153706324984594286785877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 409883533292251431429005 153706324984594286785877)
      ·
        refine ⟨56288937372287946821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 153706324984594286785877 56288937372287946821)
        ·
          rfl

theorem cell19_14984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 13].length) (baseStart_14984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_14984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_14984 prefixEnd_14984 := by exact prefixLift 14984
  have htrace : WordTrace (prefixWord ++ tailWord_14984) baseStart_14984 baseEnd_14984 := by
    simpa [prefixWord, tailWord_14984, baseEnd_14984] using wordTrace_append hprefix tailTrace_14984
  have hstable : (prefixWord ++ tailWord_14984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_14984).length < 2 ^ (prefixWord ++ tailWord_14984).sum := by decide
  have hdescent : baseEnd_14984 < baseStart_14984 := by decide
  rcases family_descends (prefixWord ++ tailWord_14984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15075 : List Nat := [1, 1, 1, 7, 1, 1, 4, 3]
def baseStart_15075 : Nat := 118140960795 + 15075 * 2 ^ 59
def prefixEnd_15075 : Nat := 4983230072969 + 3 ^ 40 * 15075 * 2
def baseEnd_15075 : Nat := 4587093846894075670031

theorem tailTrace_15075 : CollatzResearch.WordTrace tailWord_15075 prefixEnd_15075 4587093846894075670031 := by
  unfold tailWord_15075
  simp only [CollatzResearch.WordTrace]
  refine ⟨549830420393324450134679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 366553613595549633423119 549830420393324450134679)
  ·
    refine ⟨824745630589986675202019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 549830420393324450134679 824745630589986675202019)
    ·
      refine ⟨1237118445884980012803029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 824745630589986675202019 1237118445884980012803029)
      ·
        refine ⟨28994963575429219050071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 1237118445884980012803029 28994963575429219050071)
        ·
          refine ⟨43492445363143828575107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28994963575429219050071 43492445363143828575107)
          ·
            refine ⟨65238668044715742862661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43492445363143828575107 65238668044715742862661)
            ·
              refine ⟨12232250258384201786749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65238668044715742862661 12232250258384201786749)
              ·
                refine ⟨4587093846894075670031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12232250258384201786749 4587093846894075670031)
                ·
                  rfl

theorem cell19_15075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 3].length) (baseStart_15075 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15075 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15075 prefixEnd_15075 := by exact prefixLift 15075
  have htrace : WordTrace (prefixWord ++ tailWord_15075) baseStart_15075 baseEnd_15075 := by
    simpa [prefixWord, tailWord_15075, baseEnd_15075] using wordTrace_append hprefix tailTrace_15075
  have hstable : (prefixWord ++ tailWord_15075).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15075).length < 2 ^ (prefixWord ++ tailWord_15075).sum := by decide
  have hdescent : baseEnd_15075 < baseStart_15075 := by decide
  rcases family_descends (prefixWord ++ tailWord_15075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15077 : List Nat := [1, 3, 1, 4, 1, 3, 1, 5]
def baseStart_15077 : Nat := 118140960795 + 15077 * 2 ^ 59
def prefixEnd_15077 : Nat := 4983230072969 + 3 ^ 40 * 15077 * 2
def baseEnd_15077 : Nat := 4587702416558663625581

theorem tailTrace_15077 : CollatzResearch.WordTrace tailWord_15077 prefixEnd_15077 4587702416558663625581 := by
  unfold tailWord_15077
  simp only [CollatzResearch.WordTrace]
  refine ⟨549903366386078791707485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 366602244257385861138323 549903366386078791707485)
  ·
    refine ⟨206213762394779546890307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 549903366386078791707485 206213762394779546890307)
    ·
      refine ⟨309320643592169320335461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206213762394779546890307 309320643592169320335461)
      ·
        refine ⟨57997620673531747562899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309320643592169320335461 57997620673531747562899)
        ·
          refine ⟨86996431010297621344349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57997620673531747562899 86996431010297621344349)
          ·
            refine ⟨32623661628861608004131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86996431010297621344349 32623661628861608004131)
            ·
              refine ⟨48935492443292412006197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32623661628861608004131 48935492443292412006197)
              ·
                refine ⟨4587702416558663625581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48935492443292412006197 4587702416558663625581)
                ·
                  rfl

theorem cell19_15077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_15077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15077 prefixEnd_15077 := by exact prefixLift 15077
  have htrace : WordTrace (prefixWord ++ tailWord_15077) baseStart_15077 baseEnd_15077 := by
    simpa [prefixWord, tailWord_15077, baseEnd_15077] using wordTrace_append hprefix tailTrace_15077
  have hstable : (prefixWord ++ tailWord_15077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15077).length < 2 ^ (prefixWord ++ tailWord_15077).sum := by decide
  have hdescent : baseEnd_15077 < baseStart_15077 := by decide
  rcases family_descends (prefixWord ++ tailWord_15077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15098 : List Nat := [3, 1, 1, 1, 1, 3, 9]
def baseStart_15098 : Nat := 118140960795 + 15098 * 2 ^ 59
def prefixEnd_15098 : Nat := 4983230072969 + 3 ^ 40 * 15098 * 2
def baseEnd_15098 : Nat := 1531364132678945719619

theorem tailTrace_15098 : CollatzResearch.WordTrace tailWord_15098 prefixEnd_15098 1531364132678945719619 := by
  unfold tailWord_15098
  simp only [CollatzResearch.WordTrace]
  refine ⟨137667324827499844555487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 367112866206666252147965 137667324827499844555487)
  ·
    refine ⟨206500987241249766833231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137667324827499844555487 206500987241249766833231)
    ·
      refine ⟨309751480861874650249847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206500987241249766833231 309751480861874650249847)
      ·
        refine ⟨464627221292811975374771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309751480861874650249847 464627221292811975374771)
        ·
          refine ⟨696940831939217963062157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464627221292811975374771 696940831939217963062157)
          ·
            refine ⟨261352811977206736148309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 696940831939217963062157 261352811977206736148309)
            ·
              refine ⟨1531364132678945719619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 261352811977206736148309 1531364132678945719619)
              ·
                rfl

theorem cell19_15098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_15098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15098 prefixEnd_15098 := by exact prefixLift 15098
  have htrace : WordTrace (prefixWord ++ tailWord_15098) baseStart_15098 baseEnd_15098 := by
    simpa [prefixWord, tailWord_15098, baseEnd_15098] using wordTrace_append hprefix tailTrace_15098
  have hstable : (prefixWord ++ tailWord_15098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15098).length < 2 ^ (prefixWord ++ tailWord_15098).sum := by decide
  have hdescent : baseEnd_15098 < baseStart_15098 := by decide
  rcases family_descends (prefixWord ++ tailWord_15098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15149 : List Nat := [1, 5, 3, 2, 2, 6]
def baseStart_15149 : Nat := 118140960795 + 15149 * 2 ^ 59
def prefixEnd_15149 : Nat := 4983230072969 + 3 ^ 40 * 15149 * 2
def baseEnd_15149 : Nat := 512178991609314447265

theorem tailTrace_15149 : CollatzResearch.WordTrace tailWord_15149 prefixEnd_15149 512178991609314447265 := by
  unfold tailWord_15149
  simp only [CollatzResearch.WordTrace]
  refine ⟨552529422125235088328501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 368352948083490058885667 552529422125235088328501)
  ·
    refine ⟨51799633324240789530797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 552529422125235088328501 51799633324240789530797)
    ·
      refine ⟨19424862496590296074049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51799633324240789530797 19424862496590296074049)
      ·
        refine ⟨14568646872442722055537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19424862496590296074049 14568646872442722055537)
        ·
          refine ⟨10926485154332041541653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14568646872442722055537 10926485154332041541653)
          ·
            refine ⟨512178991609314447265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10926485154332041541653 512178991609314447265)
            ·
              rfl

theorem cell19_15149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 6].length) (baseStart_15149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15149 prefixEnd_15149 := by exact prefixLift 15149
  have htrace : WordTrace (prefixWord ++ tailWord_15149) baseStart_15149 baseEnd_15149 := by
    simpa [prefixWord, tailWord_15149, baseEnd_15149] using wordTrace_append hprefix tailTrace_15149
  have hstable : (prefixWord ++ tailWord_15149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15149).length < 2 ^ (prefixWord ++ tailWord_15149).sum := by decide
  have hdescent : baseEnd_15149 < baseStart_15149 := by decide
  rcases family_descends (prefixWord ++ tailWord_15149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15155 : List Nat := [1, 1, 1, 2, 6, 8]
def baseStart_15155 : Nat := 118140960795 + 15155 * 2 ^ 59
def prefixEnd_15155 : Nat := 4983230072969 + 3 ^ 40 * 15155 * 2
def baseEnd_15155 : Nat := 512381848164177099115

theorem tailTrace_15155 : CollatzResearch.WordTrace tailWord_15155 prefixEnd_15155 512381848164177099115 := by
  unfold tailWord_15155
  simp only [CollatzResearch.WordTrace]
  refine ⟨552748260103498113046919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 368498840068998742031279 552748260103498113046919)
  ·
    refine ⟨829122390155247169570379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 552748260103498113046919 829122390155247169570379)
    ·
      refine ⟨1243683585232870754355569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 829122390155247169570379 1243683585232870754355569)
      ·
        refine ⟨932762688924653065766677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1243683585232870754355569 932762688924653065766677)
        ·
          refine ⟨43723251043343112457813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 932762688924653065766677 43723251043343112457813)
          ·
            refine ⟨512381848164177099115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 43723251043343112457813 512381848164177099115)
            ·
              rfl

theorem cell19_15155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 8].length) (baseStart_15155 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15155 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15155 prefixEnd_15155 := by exact prefixLift 15155
  have htrace : WordTrace (prefixWord ++ tailWord_15155) baseStart_15155 baseEnd_15155 := by
    simpa [prefixWord, tailWord_15155, baseEnd_15155] using wordTrace_append hprefix tailTrace_15155
  have hstable : (prefixWord ++ tailWord_15155).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15155).length < 2 ^ (prefixWord ++ tailWord_15155).sum := by decide
  have hdescent : baseEnd_15155 < baseStart_15155 := by decide
  rcases family_descends (prefixWord ++ tailWord_15155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15212 : List Nat := [2, 2, 1, 1, 4, 1, 8]
def baseStart_15212 : Nat := 118140960795 + 15212 * 2 ^ 59
def prefixEnd_15212 : Nat := 4983230072969 + 3 ^ 40 * 15212 * 2
def baseEnd_15212 : Nat := 1542926956306116875071

theorem tailTrace_15212 : CollatzResearch.WordTrace tailWord_15212 prefixEnd_15212 1542926956306116875071 := by
  unfold tailWord_15212
  simp only [CollatzResearch.WordTrace]
  refine ⟨277413610448498423935945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 369884813931331231914593 277413610448498423935945)
  ·
    refine ⟨208060207836373817951959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277413610448498423935945 208060207836373817951959)
    ·
      refine ⟨312090311754560726927939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208060207836373817951959 312090311754560726927939)
      ·
        refine ⟨468135467631841090391909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312090311754560726927939 468135467631841090391909)
        ·
          refine ⟨87775400180970204448483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 468135467631841090391909 87775400180970204448483)
          ·
            refine ⟨131663100271455306672725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87775400180970204448483 131663100271455306672725)
            ·
              refine ⟨1542926956306116875071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 131663100271455306672725 1542926956306116875071)
              ·
                rfl

theorem cell19_15212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_15212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15212 prefixEnd_15212 := by exact prefixLift 15212
  have htrace : WordTrace (prefixWord ++ tailWord_15212) baseStart_15212 baseEnd_15212 := by
    simpa [prefixWord, tailWord_15212, baseEnd_15212] using wordTrace_append hprefix tailTrace_15212
  have hstable : (prefixWord ++ tailWord_15212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15212).length < 2 ^ (prefixWord ++ tailWord_15212).sum := by decide
  have hdescent : baseEnd_15212 < baseStart_15212 := by decide
  rcases family_descends (prefixWord ++ tailWord_15212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15284 : List Nat := [2, 5, 2, 1, 1, 1, 1, 6]
def baseStart_15284 : Nat := 118140960795 + 15284 * 2 ^ 59
def prefixEnd_15284 : Nat := 4983230072969 + 3 ^ 40 * 15284 * 2
def baseEnd_15284 : Nat := 4650689376843517025017

theorem tailTrace_15284 : CollatzResearch.WordTrace tailWord_15284 prefixEnd_15284 4650689376843517025017 := by
  unfold tailWord_15284
  simp only [CollatzResearch.WordTrace]
  refine ⟨278726638318076572246453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 371635517757435429661937 278726638318076572246453)
  ·
    refine ⟨26130622342319678648105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 278726638318076572246453 26130622342319678648105)
    ·
      refine ⟨19597966756739758986079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26130622342319678648105 19597966756739758986079)
      ·
        refine ⟨29396950135109638479119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19597966756739758986079 29396950135109638479119)
        ·
          refine ⟨44095425202664457718679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29396950135109638479119 44095425202664457718679)
          ·
            refine ⟨66143137803996686578019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44095425202664457718679 66143137803996686578019)
            ·
              refine ⟨99214706705995029867029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66143137803996686578019 99214706705995029867029)
              ·
                refine ⟨4650689376843517025017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99214706705995029867029 4650689376843517025017)
                ·
                  rfl

theorem cell19_15284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_15284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15284 prefixEnd_15284 := by exact prefixLift 15284
  have htrace : WordTrace (prefixWord ++ tailWord_15284) baseStart_15284 baseEnd_15284 := by
    simpa [prefixWord, tailWord_15284, baseEnd_15284] using wordTrace_append hprefix tailTrace_15284
  have hstable : (prefixWord ++ tailWord_15284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15284).length < 2 ^ (prefixWord ++ tailWord_15284).sum := by decide
  have hdescent : baseEnd_15284 < baseStart_15284 := by decide
  rcases family_descends (prefixWord ++ tailWord_15284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15288 : List Nat := [2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_15288 : Nat := 118140960795 + 15288 * 2 ^ 59
def prefixEnd_15288 : Nat := 4983230072969 + 3 ^ 40 * 15288 * 2
def baseEnd_15288 : Nat := 4651906516172692936117

theorem tailTrace_15288 : CollatzResearch.WordTrace tailWord_15288 prefixEnd_15288 4651906516172692936117 := by
  unfold tailWord_15288
  simp only [CollatzResearch.WordTrace]
  refine ⟨278799584310830913819259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 371732779081107885092345 278799584310830913819259)
  ·
    refine ⟨418199376466246370728889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 278799584310830913819259 418199376466246370728889)
    ·
      refine ⟨313649532349684778046667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 418199376466246370728889 313649532349684778046667)
      ·
        refine ⟨470474298524527167070001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313649532349684778046667 470474298524527167070001)
        ·
          refine ⟨352855723893395375302501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470474298524527167070001 352855723893395375302501)
          ·
            refine ⟨66160448230011632869219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352855723893395375302501 66160448230011632869219)
            ·
              refine ⟨99240672345017449303829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66160448230011632869219 99240672345017449303829)
              ·
                refine ⟨4651906516172692936117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99240672345017449303829 4651906516172692936117)
                ·
                  rfl

theorem cell19_15288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_15288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15288 prefixEnd_15288 := by exact prefixLift 15288
  have htrace : WordTrace (prefixWord ++ tailWord_15288) baseStart_15288 baseEnd_15288 := by
    simpa [prefixWord, tailWord_15288, baseEnd_15288] using wordTrace_append hprefix tailTrace_15288
  have hstable : (prefixWord ++ tailWord_15288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15288).length < 2 ^ (prefixWord ++ tailWord_15288).sum := by decide
  have hdescent : baseEnd_15288 < baseStart_15288 := by decide
  rcases family_descends (prefixWord ++ tailWord_15288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15307 : List Nat := [1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_15307 : Nat := 118140960795 + 15307 * 2 ^ 59
def prefixEnd_15307 : Nat := 4983230072969 + 3 ^ 40 * 15307 * 2
def baseEnd_15307 : Nat := 4657687927986278513843

theorem tailTrace_15307 : CollatzResearch.WordTrace tailWord_15307 prefixEnd_15307 4657687927986278513843 := by
  unfold tailWord_15307
  simp only [CollatzResearch.WordTrace]
  refine ⟨558292155552828072580175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 372194770368552048386783 558292155552828072580175)
  ·
    refine ⟨837438233329242108870263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 558292155552828072580175 837438233329242108870263)
    ·
      refine ⟨1256157349993863163305395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837438233329242108870263 1256157349993863163305395)
      ·
        refine ⟨1884236024990794744958093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256157349993863163305395 1884236024990794744958093)
        ·
          refine ⟨706588509371548029359285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1884236024990794744958093 706588509371548029359285)
          ·
            refine ⟨66242672753582627752433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 706588509371548029359285 66242672753582627752433)
            ·
              refine ⟨49682004565186970814325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66242672753582627752433 49682004565186970814325)
              ·
                refine ⟨4657687927986278513843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49682004565186970814325 4657687927986278513843)
                ·
                  rfl

theorem cell19_15307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_15307 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15307 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15307 prefixEnd_15307 := by exact prefixLift 15307
  have htrace : WordTrace (prefixWord ++ tailWord_15307) baseStart_15307 baseEnd_15307 := by
    simpa [prefixWord, tailWord_15307, baseEnd_15307] using wordTrace_append hprefix tailTrace_15307
  have hstable : (prefixWord ++ tailWord_15307).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15307).length < 2 ^ (prefixWord ++ tailWord_15307).sum := by decide
  have hdescent : baseEnd_15307 < baseStart_15307 := by decide
  rcases family_descends (prefixWord ++ tailWord_15307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15324 : List Nat := [2, 2, 6, 9]
def baseStart_15324 : Nat := 118140960795 + 15324 * 2 ^ 59
def prefixEnd_15324 : Nat := 4983230072969 + 3 ^ 40 * 15324 * 2
def baseEnd_15324 : Nat := 57566182347349088099

theorem tailTrace_15324 : CollatzResearch.WordTrace tailWord_15324 prefixEnd_15324 57566182347349088099 := by
  unfold tailWord_15324
  simp only [CollatzResearch.WordTrace]
  refine ⟨279456098245619987974513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 372608130994159983966017 279456098245619987974513)
  ·
    refine ⟨209592073684214990980885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279456098245619987974513 209592073684214990980885)
    ·
      refine ⟨9824628453947577702229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 209592073684214990980885 9824628453947577702229)
      ·
        refine ⟨57566182347349088099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 9824628453947577702229 57566182347349088099)
        ·
          rfl

theorem cell19_15324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 9].length) (baseStart_15324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15324 prefixEnd_15324 := by exact prefixLift 15324
  have htrace : WordTrace (prefixWord ++ tailWord_15324) baseStart_15324 baseEnd_15324 := by
    simpa [prefixWord, tailWord_15324, baseEnd_15324] using wordTrace_append hprefix tailTrace_15324
  have hstable : (prefixWord ++ tailWord_15324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15324).length < 2 ^ (prefixWord ++ tailWord_15324).sum := by decide
  have hdescent : baseEnd_15324 < baseStart_15324 := by decide
  rcases family_descends (prefixWord ++ tailWord_15324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15343 : List Nat := [1, 1, 2, 1, 4, 5, 1, 4]
def baseStart_15343 : Nat := 118140960795 + 15343 * 2 ^ 59
def prefixEnd_15343 : Nat := 4983230072969 + 3 ^ 40 * 15343 * 2
def baseEnd_15343 : Nat := 4668642181948861713745

theorem tailTrace_15343 : CollatzResearch.WordTrace tailWord_15343 prefixEnd_15343 4668642181948861713745 := by
  unfold tailWord_15343
  simp only [CollatzResearch.WordTrace]
  refine ⟨559605183422406220890683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 373070122281604147260455 559605183422406220890683)
  ·
    refine ⟨839407775133609331336025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 559605183422406220890683 839407775133609331336025)
    ·
      refine ⟨629555831350206998502019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839407775133609331336025 629555831350206998502019)
      ·
        refine ⟨944333747025310497753029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629555831350206998502019 944333747025310497753029)
        ·
          refine ⟨177062577567245718328693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 944333747025310497753029 177062577567245718328693)
          ·
            refine ⟨16599616646929286093315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177062577567245718328693 16599616646929286093315)
            ·
              refine ⟨24899424970393929139973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16599616646929286093315 24899424970393929139973)
              ·
                refine ⟨4668642181948861713745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24899424970393929139973 4668642181948861713745)
                ·
                  rfl

theorem cell19_15343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_15343 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15343 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15343 prefixEnd_15343 := by exact prefixLift 15343
  have htrace : WordTrace (prefixWord ++ tailWord_15343) baseStart_15343 baseEnd_15343 := by
    simpa [prefixWord, tailWord_15343, baseEnd_15343] using wordTrace_append hprefix tailTrace_15343
  have hstable : (prefixWord ++ tailWord_15343).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15343).length < 2 ^ (prefixWord ++ tailWord_15343).sum := by decide
  have hdescent : baseEnd_15343 < baseStart_15343 := by decide
  rcases family_descends (prefixWord ++ tailWord_15343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15358 : List Nat := [4, 2, 2, 2, 2, 1, 3, 3]
def baseStart_15358 : Nat := 118140960795 + 15358 * 2 ^ 59
def prefixEnd_15358 : Nat := 4983230072969 + 3 ^ 40 * 15358 * 2
def baseEnd_15358 : Nat := 4673206454433271380371

theorem tailTrace_15358 : CollatzResearch.WordTrace tailWord_15358 prefixEnd_15358 4673206454433271380371 := by
  unfold tailWord_15358
  simp only [CollatzResearch.WordTrace]
  refine ⟨70019034796007972835841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 373434852245375855124485 70019034796007972835841)
  ·
    refine ⟨52514276097005979626881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70019034796007972835841 52514276097005979626881)
    ·
      refine ⟨39385707072754484720161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52514276097005979626881 39385707072754484720161)
      ·
        refine ⟨29539280304565863540121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39385707072754484720161 29539280304565863540121)
        ·
          refine ⟨22154460228424397655091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29539280304565863540121 22154460228424397655091)
          ·
            refine ⟨33231690342636596482637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22154460228424397655091 33231690342636596482637)
            ·
              refine ⟨12461883878488723680989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33231690342636596482637 12461883878488723680989)
              ·
                refine ⟨4673206454433271380371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12461883878488723680989 4673206454433271380371)
                ·
                  rfl

theorem cell19_15358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_15358 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15358 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15358 prefixEnd_15358 := by exact prefixLift 15358
  have htrace : WordTrace (prefixWord ++ tailWord_15358) baseStart_15358 baseEnd_15358 := by
    simpa [prefixWord, tailWord_15358, baseEnd_15358] using wordTrace_append hprefix tailTrace_15358
  have hstable : (prefixWord ++ tailWord_15358).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15358).length < 2 ^ (prefixWord ++ tailWord_15358).sum := by decide
  have hdescent : baseEnd_15358 < baseStart_15358 := by decide
  rcases family_descends (prefixWord ++ tailWord_15358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15417 : List Nat := [1, 2, 1, 5, 2, 3, 2, 3]
def baseStart_15417 : Nat := 118140960795 + 15417 * 2 ^ 59
def prefixEnd_15417 : Nat := 4983230072969 + 3 ^ 40 * 15417 * 2
def baseEnd_15417 : Nat := 4691159259538616069099

theorem tailTrace_15417 : CollatzResearch.WordTrace tailWord_15417 prefixEnd_15417 4691159259538616069099 := by
  unfold tailWord_15417
  simp only [CollatzResearch.WordTrace]
  refine ⟨562304185154316859084505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 374869456769544572723003 562304185154316859084505)
  ·
    refine ⟨421728138865737644313379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 562304185154316859084505 421728138865737644313379)
    ·
      refine ⟨632592208298606466470069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421728138865737644313379 632592208298606466470069)
      ·
        refine ⟨59305519527994356231569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 632592208298606466470069 59305519527994356231569)
        ·
          refine ⟨44479139645995767173677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59305519527994356231569 44479139645995767173677)
          ·
            refine ⟨16679677367248412690129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44479139645995767173677 16679677367248412690129)
            ·
              refine ⟨12509758025436309517597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16679677367248412690129 12509758025436309517597)
              ·
                refine ⟨4691159259538616069099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12509758025436309517597 4691159259538616069099)
                ·
                  rfl

theorem cell19_15417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 3].length) (baseStart_15417 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15417 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15417 prefixEnd_15417 := by exact prefixLift 15417
  have htrace : WordTrace (prefixWord ++ tailWord_15417) baseStart_15417 baseEnd_15417 := by
    simpa [prefixWord, tailWord_15417, baseEnd_15417] using wordTrace_append hprefix tailTrace_15417
  have hstable : (prefixWord ++ tailWord_15417).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15417).length < 2 ^ (prefixWord ++ tailWord_15417).sum := by decide
  have hdescent : baseEnd_15417 < baseStart_15417 := by decide
  rcases family_descends (prefixWord ++ tailWord_15417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15514 : List Nat := [3, 1, 1, 5, 1, 1, 3, 4]
def baseStart_15514 : Nat := 118140960795 + 15514 * 2 ^ 59
def prefixEnd_15514 : Nat := 4983230072969 + 3 ^ 40 * 15514 * 2
def baseEnd_15514 : Nat := 4720674888271131913279

theorem tailTrace_15514 : CollatzResearch.WordTrace tailWord_15514 prefixEnd_15514 4720674888271131913279 := by
  unfold tailWord_15514
  simp only [CollatzResearch.WordTrace]
  refine ⟨141460516450725606341399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 377228043868601616910397 141460516450725606341399)
  ·
    refine ⟨212190774676088409512099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141460516450725606341399 212190774676088409512099)
    ·
      refine ⟨318286162014132614268149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212190774676088409512099 318286162014132614268149)
      ·
        refine ⟨29839327688824932587639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 318286162014132614268149 29839327688824932587639)
        ·
          refine ⟨44758991533237398881459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29839327688824932587639 44758991533237398881459)
          ·
            refine ⟨67138487299856098322189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44758991533237398881459 67138487299856098322189)
            ·
              refine ⟨25176932737446036870821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67138487299856098322189 25176932737446036870821)
              ·
                refine ⟨4720674888271131913279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25176932737446036870821 4720674888271131913279)
                ·
                  rfl

theorem cell19_15514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_15514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15514 prefixEnd_15514 := by exact prefixLift 15514
  have htrace : WordTrace (prefixWord ++ tailWord_15514) baseStart_15514 baseEnd_15514 := by
    simpa [prefixWord, tailWord_15514, baseEnd_15514] using wordTrace_append hprefix tailTrace_15514
  have hstable : (prefixWord ++ tailWord_15514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15514).length < 2 ^ (prefixWord ++ tailWord_15514).sum := by decide
  have hdescent : baseEnd_15514 < baseStart_15514 := by decide
  rcases family_descends (prefixWord ++ tailWord_15514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15592 : List Nat := [2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_15592 : Nat := 118140960795 + 15592 * 2 ^ 59
def prefixEnd_15592 : Nat := 4983230072969 + 3 ^ 40 * 15592 * 2
def baseEnd_15592 : Nat := 4744409105190062179733

theorem tailTrace_15592 : CollatzResearch.WordTrace tailWord_15592 prefixEnd_15592 4744409105190062179733 := by
  unfold tailWord_15592
  simp only [CollatzResearch.WordTrace]
  refine ⟨284343479760160873352515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 379124639680214497803353 284343479760160873352515)
  ·
    refine ⟨426515219640241310028773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284343479760160873352515 426515219640241310028773)
    ·
      refine ⟨79971603682545245630395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426515219640241310028773 79971603682545245630395)
      ·
        refine ⟨119957405523817868445593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79971603682545245630395 119957405523817868445593)
        ·
          refine ⟨89968054142863401334195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119957405523817868445593 89968054142863401334195)
          ·
            refine ⟨134952081214295102001293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89968054142863401334195 134952081214295102001293)
            ·
              refine ⟨50607030455360663250485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134952081214295102001293 50607030455360663250485)
              ·
                refine ⟨4744409105190062179733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50607030455360663250485 4744409105190062179733)
                ·
                  rfl

theorem cell19_15592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_15592 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15592 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15592 prefixEnd_15592 := by exact prefixLift 15592
  have htrace : WordTrace (prefixWord ++ tailWord_15592) baseStart_15592 baseEnd_15592 := by
    simpa [prefixWord, tailWord_15592, baseEnd_15592] using wordTrace_append hprefix tailTrace_15592
  have hstable : (prefixWord ++ tailWord_15592).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15592).length < 2 ^ (prefixWord ++ tailWord_15592).sum := by decide
  have hdescent : baseEnd_15592 < baseStart_15592 := by decide
  rcases family_descends (prefixWord ++ tailWord_15592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15630 : List Nat := [4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_15630 : Nat := 118140960795 + 15630 * 2 ^ 59
def prefixEnd_15630 : Nat := 4983230072969 + 3 ^ 40 * 15630 * 2
def baseEnd_15630 : Nat := 4755971928817233335185

theorem tailTrace_15630 : CollatzResearch.WordTrace tailWord_15630 prefixEnd_15630 4755971928817233335185 := by
  unfold tailWord_15630
  simp only [CollatzResearch.WordTrace]
  refine ⟨71259116672831779573543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 380048622255102824392229 71259116672831779573543)
  ·
    refine ⟨106888675009247669360315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71259116672831779573543 106888675009247669360315)
    ·
      refine ⟨160333012513871504040473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106888675009247669360315 160333012513871504040473)
      ·
        refine ⟨120249759385403628030355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160333012513871504040473 120249759385403628030355)
        ·
          refine ⟨180374639078105442045533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120249759385403628030355 180374639078105442045533)
          ·
            refine ⟨67640489654289540767075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180374639078105442045533 67640489654289540767075)
            ·
              refine ⟨101460734481434311150613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67640489654289540767075 101460734481434311150613)
              ·
                refine ⟨4755971928817233335185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101460734481434311150613 4755971928817233335185)
                ·
                  rfl

theorem cell19_15630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_15630 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15630 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15630 prefixEnd_15630 := by exact prefixLift 15630
  have htrace : WordTrace (prefixWord ++ tailWord_15630) baseStart_15630 baseEnd_15630 := by
    simpa [prefixWord, tailWord_15630, baseEnd_15630] using wordTrace_append hprefix tailTrace_15630
  have hstable : (prefixWord ++ tailWord_15630).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15630).length < 2 ^ (prefixWord ++ tailWord_15630).sum := by decide
  have hdescent : baseEnd_15630 < baseStart_15630 := by decide
  rcases family_descends (prefixWord ++ tailWord_15630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15687 : List Nat := [1, 1, 4, 1, 2, 3, 3, 4]
def baseStart_15687 : Nat := 118140960795 + 15687 * 2 ^ 59
def prefixEnd_15687 : Nat := 4983230072969 + 3 ^ 40 * 15687 * 2
def baseEnd_15687 : Nat := 4773316164257990068363

theorem tailTrace_15687 : CollatzResearch.WordTrace tailWord_15687 prefixEnd_15687 4773316164257990068363 := by
  unfold tailWord_15687
  simp only [CollatzResearch.WordTrace]
  refine ⟨572151894176152971413315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 381434596117435314275543 572151894176152971413315)
  ·
    refine ⟨858227841264229457119973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 572151894176152971413315 858227841264229457119973)
    ·
      refine ⟨160917720237043023209995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 858227841264229457119973 160917720237043023209995)
      ·
        refine ⟨241376580355564534814993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160917720237043023209995 241376580355564534814993)
        ·
          refine ⟨181032435266673401111245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241376580355564534814993 181032435266673401111245)
          ·
            refine ⟨67887163225002525416717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181032435266673401111245 67887163225002525416717)
            ·
              refine ⟨25457686209375947031269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67887163225002525416717 25457686209375947031269)
              ·
                refine ⟨4773316164257990068363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25457686209375947031269 4773316164257990068363)
                ·
                  rfl

theorem cell19_15687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_15687 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15687 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15687 prefixEnd_15687 := by exact prefixLift 15687
  have htrace : WordTrace (prefixWord ++ tailWord_15687) baseStart_15687 baseEnd_15687 := by
    simpa [prefixWord, tailWord_15687, baseEnd_15687] using wordTrace_append hprefix tailTrace_15687
  have hstable : (prefixWord ++ tailWord_15687).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15687).length < 2 ^ (prefixWord ++ tailWord_15687).sum := by decide
  have hdescent : baseEnd_15687 < baseStart_15687 := by decide
  rcases family_descends (prefixWord ++ tailWord_15687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15725 : List Nat := [1, 5, 1, 1, 1, 4, 6]
def baseStart_15725 : Nat := 118140960795 + 15725 * 2 ^ 59
def prefixEnd_15725 : Nat := 4983230072969 + 3 ^ 40 * 15725 * 2
def baseEnd_15725 : Nat := 1594959662628387074605

theorem tailTrace_15725 : CollatzResearch.WordTrace tailWord_15725 prefixEnd_15725 1594959662628387074605 := by
  unfold tailWord_15725
  simp only [CollatzResearch.WordTrace]
  refine ⟨573537868038485461296629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 382358578692323640864419 573537868038485461296629)
  ·
    refine ⟨53769175128608011996559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 573537868038485461296629 53769175128608011996559)
    ·
      refine ⟨80653762692912017994839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53769175128608011996559 80653762692912017994839)
      ·
        refine ⟨120980644039368026992259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80653762692912017994839 120980644039368026992259)
        ·
          refine ⟨181470966059052040488389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120980644039368026992259 181470966059052040488389)
          ·
            refine ⟨34025806136072257591573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181470966059052040488389 34025806136072257591573)
            ·
              refine ⟨1594959662628387074605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34025806136072257591573 1594959662628387074605)
              ·
                rfl

theorem cell19_15725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 6].length) (baseStart_15725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15725 prefixEnd_15725 := by exact prefixLift 15725
  have htrace : WordTrace (prefixWord ++ tailWord_15725) baseStart_15725 baseEnd_15725 := by
    simpa [prefixWord, tailWord_15725, baseEnd_15725] using wordTrace_append hprefix tailTrace_15725
  have hstable : (prefixWord ++ tailWord_15725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15725).length < 2 ^ (prefixWord ++ tailWord_15725).sum := by decide
  have hdescent : baseEnd_15725 < baseStart_15725 := by decide
  rcases family_descends (prefixWord ++ tailWord_15725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15727 : List Nat := [1, 1, 2, 1, 3, 1, 10]
def baseStart_15727 : Nat := 118140960795 + 15727 * 2 ^ 59
def prefixEnd_15727 : Nat := 4983230072969 + 3 ^ 40 * 15727 * 2
def baseEnd_15727 : Nat := 1595162519183249726455

theorem tailTrace_15727 : CollatzResearch.WordTrace tailWord_15727 prefixEnd_15727 1595162519183249726455 := by
  unfold tailWord_15727
  simp only [CollatzResearch.WordTrace]
  refine ⟨573610814031239802869435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 382407209354159868579623 573610814031239802869435)
  ·
    refine ⟨860416221046859704304153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 573610814031239802869435 860416221046859704304153)
    ·
      refine ⟨645312165785144778228115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 860416221046859704304153 645312165785144778228115)
      ·
        refine ⟨967968248677717167342173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645312165785144778228115 967968248677717167342173)
        ·
          refine ⟨362988093254143937753315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 967968248677717167342173 362988093254143937753315)
          ·
            refine ⟨544482139881215906629973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362988093254143937753315 544482139881215906629973)
            ·
              refine ⟨1595162519183249726455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 544482139881215906629973 1595162519183249726455)
              ·
                rfl

theorem cell19_15727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_15727 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15727 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15727 prefixEnd_15727 := by exact prefixLift 15727
  have htrace : WordTrace (prefixWord ++ tailWord_15727) baseStart_15727 baseEnd_15727 := by
    simpa [prefixWord, tailWord_15727, baseEnd_15727] using wordTrace_append hprefix tailTrace_15727
  have hstable : (prefixWord ++ tailWord_15727).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15727).length < 2 ^ (prefixWord ++ tailWord_15727).sum := by decide
  have hdescent : baseEnd_15727 < baseStart_15727 := by decide
  rcases family_descends (prefixWord ++ tailWord_15727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15820 : List Nat := [2, 2, 1, 4, 2, 1, 2, 5]
def baseStart_15820 : Nat := 118140960795 + 15820 * 2 ^ 59
def prefixEnd_15820 : Nat := 4983230072969 + 3 ^ 40 * 15820 * 2
def baseEnd_15820 : Nat := 4813786046953089112445

theorem tailTrace_15820 : CollatzResearch.WordTrace tailWord_15820 prefixEnd_15820 4813786046953089112445 := by
  unfold tailWord_15820
  simp only [CollatzResearch.WordTrace]
  refine ⟨288501401347158343002457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 384668535129544457336609 288501401347158343002457)
  ·
    refine ⟨216376051010368757251843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 288501401347158343002457 216376051010368757251843)
    ·
      refine ⟨324564076515553135877765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 216376051010368757251843 324564076515553135877765)
      ·
        refine ⟨60855764346666212977081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 324564076515553135877765 60855764346666212977081)
        ·
          refine ⟨45641823259999659732811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60855764346666212977081 45641823259999659732811)
          ·
            refine ⟨68462734889999489599217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45641823259999659732811 68462734889999489599217)
            ·
              refine ⟨51347051167499617199413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68462734889999489599217 51347051167499617199413)
              ·
                refine ⟨4813786046953089112445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51347051167499617199413 4813786046953089112445)
                ·
                  rfl

theorem cell19_15820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_15820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15820 prefixEnd_15820 := by exact prefixLift 15820
  have htrace : WordTrace (prefixWord ++ tailWord_15820) baseStart_15820 baseEnd_15820 := by
    simpa [prefixWord, tailWord_15820, baseEnd_15820] using wordTrace_append hprefix tailTrace_15820
  have hstable : (prefixWord ++ tailWord_15820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15820).length < 2 ^ (prefixWord ++ tailWord_15820).sum := by decide
  have hdescent : baseEnd_15820 < baseStart_15820 := by decide
  rcases family_descends (prefixWord ++ tailWord_15820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15841 : List Nat := [1, 2, 3, 1, 2, 10]
def baseStart_15841 : Nat := 118140960795 + 15841 * 2 ^ 59
def prefixEnd_15841 : Nat := 4983230072969 + 3 ^ 40 * 15841 * 2
def baseEnd_15841 : Nat := 535575114270140293969

theorem tailTrace_15841 : CollatzResearch.WordTrace tailWord_15841 prefixEnd_15841 535575114270140293969 := by
  unfold tailWord_15841
  simp only [CollatzResearch.WordTrace]
  refine ⟨577768735618237272519377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 385179157078824848346251 577768735618237272519377)
  ·
    refine ⟨433326551713677954389533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 577768735618237272519377 433326551713677954389533)
    ·
      refine ⟨162497456892629232896075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 433326551713677954389533 162497456892629232896075)
      ·
        refine ⟨243746185338943849344113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162497456892629232896075 243746185338943849344113)
        ·
          refine ⟨182809639004207887008085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243746185338943849344113 182809639004207887008085)
          ·
            refine ⟨535575114270140293969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 182809639004207887008085 535575114270140293969)
            ·
              rfl

theorem cell19_15841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 10].length) (baseStart_15841 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15841 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15841 prefixEnd_15841 := by exact prefixLift 15841
  have htrace : WordTrace (prefixWord ++ tailWord_15841) baseStart_15841 baseEnd_15841 := by
    simpa [prefixWord, tailWord_15841, baseEnd_15841] using wordTrace_append hprefix tailTrace_15841
  have hstable : (prefixWord ++ tailWord_15841).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15841).length < 2 ^ (prefixWord ++ tailWord_15841).sum := by decide
  have hdescent : baseEnd_15841 < baseStart_15841 := by decide
  rcases family_descends (prefixWord ++ tailWord_15841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15896 : List Nat := [2, 1, 2, 3, 4, 1, 6]
def baseStart_15896 : Nat := 118140960795 + 15896 * 2 ^ 59
def prefixEnd_15896 : Nat := 4983230072969 + 3 ^ 40 * 15896 * 2
def baseEnd_15896 : Nat := 1612303898069143807783

theorem tailTrace_15896 : CollatzResearch.WordTrace tailWord_15896 prefixEnd_15896 1612303898069143807783 := by
  unfold tailWord_15896
  simp only [CollatzResearch.WordTrace]
  refine ⟨289887375209490832885771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 386516500279321110514361 289887375209490832885771)
  ·
    refine ⟨434831062814236249328657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 289887375209490832885771 434831062814236249328657)
    ·
      refine ⟨326123297110677186996493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 434831062814236249328657 326123297110677186996493)
      ·
        refine ⟨122296236416503945123685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 326123297110677186996493 122296236416503945123685)
        ·
          refine ⟨22930544328094489710691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122296236416503945123685 22930544328094489710691)
          ·
            refine ⟨34395816492141734566037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22930544328094489710691 34395816492141734566037)
            ·
              refine ⟨1612303898069143807783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34395816492141734566037 1612303898069143807783)
              ·
                rfl

theorem cell19_15896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 6].length) (baseStart_15896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15896 prefixEnd_15896 := by exact prefixLift 15896
  have htrace : WordTrace (prefixWord ++ tailWord_15896) baseStart_15896 baseEnd_15896 := by
    simpa [prefixWord, tailWord_15896, baseEnd_15896] using wordTrace_append hprefix tailTrace_15896
  have hstable : (prefixWord ++ tailWord_15896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15896).length < 2 ^ (prefixWord ++ tailWord_15896).sum := by decide
  have hdescent : baseEnd_15896 < baseStart_15896 := by decide
  rcases family_descends (prefixWord ++ tailWord_15896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15949 : List Nat := [1, 6, 1, 1, 4, 1, 5]
def baseStart_15949 : Nat := 118140960795 + 15949 * 2 ^ 59
def prefixEnd_15949 : Nat := 4983230072969 + 3 ^ 40 * 15949 * 2
def baseEnd_15949 : Nat := 1617679596773004081809

theorem tailTrace_15949 : CollatzResearch.WordTrace tailWord_15949 prefixEnd_15949 1617679596773004081809 := by
  unfold tailWord_15949
  simp only [CollatzResearch.WordTrace]
  refine ⟨581707819226971717450901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 387805212817981144967267 581707819226971717450901)
  ·
    refine ⟨27267554026264299255511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 581707819226971717450901 27267554026264299255511)
    ·
      refine ⟨40901331039396448883267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27267554026264299255511 40901331039396448883267)
      ·
        refine ⟨61351996559094673324901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40901331039396448883267 61351996559094673324901)
        ·
          refine ⟨11503499354830251248419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61351996559094673324901 11503499354830251248419)
          ·
            refine ⟨17255249032245376872629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11503499354830251248419 17255249032245376872629)
            ·
              refine ⟨1617679596773004081809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17255249032245376872629 1617679596773004081809)
              ·
                rfl

theorem cell19_15949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 5].length) (baseStart_15949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15949 prefixEnd_15949 := by exact prefixLift 15949
  have htrace : WordTrace (prefixWord ++ tailWord_15949) baseStart_15949 baseEnd_15949 := by
    simpa [prefixWord, tailWord_15949, baseEnd_15949] using wordTrace_append hprefix tailTrace_15949
  have hstable : (prefixWord ++ tailWord_15949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15949).length < 2 ^ (prefixWord ++ tailWord_15949).sum := by decide
  have hdescent : baseEnd_15949 < baseStart_15949 := by decide
  rcases family_descends (prefixWord ++ tailWord_15949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15972 : List Nat := [2, 3, 1, 1, 2, 4, 2, 4]
def baseStart_15972 : Nat := 118140960795 + 15972 * 2 ^ 59
def prefixEnd_15972 : Nat := 4983230072969 + 3 ^ 40 * 15972 * 2
def baseEnd_15972 : Nat := 4860037341461773734253

theorem tailTrace_15972 : CollatzResearch.WordTrace tailWord_15972 prefixEnd_15972 4860037341461773734253 := by
  unfold tailWord_15972
  simp only [CollatzResearch.WordTrace]
  refine ⟨291273349071823322769085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 388364465429097763692113 291273349071823322769085)
  ·
    refine ⟨109227505901933746038407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 291273349071823322769085 109227505901933746038407)
    ·
      refine ⟨163841258852900619057611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109227505901933746038407 163841258852900619057611)
      ·
        refine ⟨245761888279350928586417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163841258852900619057611 245761888279350928586417)
        ·
          refine ⟨184321416209513196439813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245761888279350928586417 184321416209513196439813)
          ·
            refine ⟨34560265539283724332465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184321416209513196439813 34560265539283724332465)
            ·
              refine ⟨25920199154462793249349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34560265539283724332465 25920199154462793249349)
              ·
                refine ⟨4860037341461773734253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25920199154462793249349 4860037341461773734253)
                ·
                  rfl

theorem cell19_15972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_15972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15972 prefixEnd_15972 := by exact prefixLift 15972
  have htrace : WordTrace (prefixWord ++ tailWord_15972) baseStart_15972 baseEnd_15972 := by
    simpa [prefixWord, tailWord_15972, baseEnd_15972] using wordTrace_append hprefix tailTrace_15972
  have hstable : (prefixWord ++ tailWord_15972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15972).length < 2 ^ (prefixWord ++ tailWord_15972).sum := by decide
  have hdescent : baseEnd_15972 < baseStart_15972 := by decide
  rcases family_descends (prefixWord ++ tailWord_15972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_15993 : List Nat := [1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_15993 : Nat := 118140960795 + 15993 * 2 ^ 59
def prefixEnd_15993 : Nat := 4983230072969 + 3 ^ 40 * 15993 * 2
def baseEnd_15993 : Nat := 4866427322939947267529

theorem tailTrace_15993 : CollatzResearch.WordTrace tailWord_15993 prefixEnd_15993 4866427322939947267529 := by
  unfold tailWord_15993
  simp only [CollatzResearch.WordTrace]
  refine ⟨583312631067567232052633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 388875087378378154701755 583312631067567232052633)
  ·
    refine ⟨437484473300675424039475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 583312631067567232052633 437484473300675424039475)
    ·
      refine ⟨656226709951013136059213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437484473300675424039475 656226709951013136059213)
      ·
        refine ⟨246085016231629926022205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 656226709951013136059213 246085016231629926022205)
        ·
          refine ⟨92281881086861222258327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 246085016231629926022205 92281881086861222258327)
          ·
            refine ⟨138422821630291833387491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92281881086861222258327 138422821630291833387491)
            ·
              refine ⟨207634232445437750081237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 138422821630291833387491 207634232445437750081237)
              ·
                refine ⟨4866427322939947267529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 207634232445437750081237 4866427322939947267529)
                ·
                  rfl

theorem cell19_15993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_15993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_15993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_15993 prefixEnd_15993 := by exact prefixLift 15993
  have htrace : WordTrace (prefixWord ++ tailWord_15993) baseStart_15993 baseEnd_15993 := by
    simpa [prefixWord, tailWord_15993, baseEnd_15993] using wordTrace_append hprefix tailTrace_15993
  have hstable : (prefixWord ++ tailWord_15993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_15993).length < 2 ^ (prefixWord ++ tailWord_15993).sum := by decide
  have hdescent : baseEnd_15993 < baseStart_15993 := by decide
  rcases family_descends (prefixWord ++ tailWord_15993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16008 : List Nat := [2, 1, 3, 5, 2, 6]
def baseStart_16008 : Nat := 118140960795 + 16008 * 2 ^ 59
def prefixEnd_16008 : Nat := 4983230072969 + 3 ^ 40 * 16008 * 2
def baseEnd_16008 : Nat := 541221288380484103795

theorem tailTrace_16008 : CollatzResearch.WordTrace tailWord_16008 prefixEnd_16008 541221288380484103795 := by
  unfold tailWord_16008
  simp only [CollatzResearch.WordTrace]
  refine ⟨291929863006612396924339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 389239817342149862565785 291929863006612396924339)
  ·
    refine ⟨437894794509918595386509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 291929863006612396924339 437894794509918595386509)
    ·
      refine ⟨164210547941219473269941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 437894794509918595386509 164210547941219473269941)
      ·
        refine ⟨15394738869489325619057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164210547941219473269941 15394738869489325619057)
        ·
          refine ⟨11546054152116994214293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15394738869489325619057 11546054152116994214293)
          ·
            refine ⟨541221288380484103795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11546054152116994214293 541221288380484103795)
            ·
              rfl

theorem cell19_16008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 6].length) (baseStart_16008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16008 prefixEnd_16008 := by exact prefixLift 16008
  have htrace : WordTrace (prefixWord ++ tailWord_16008) baseStart_16008 baseEnd_16008 := by
    simpa [prefixWord, tailWord_16008, baseEnd_16008] using wordTrace_append hprefix tailTrace_16008
  have hstable : (prefixWord ++ tailWord_16008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16008).length < 2 ^ (prefixWord ++ tailWord_16008).sum := by decide
  have hdescent : baseEnd_16008 < baseStart_16008 := by decide
  rcases family_descends (prefixWord ++ tailWord_16008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16050 : List Nat := [3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_16050 : Nat := 118140960795 + 16050 * 2 ^ 59
def prefixEnd_16050 : Nat := 4983230072969 + 3 ^ 40 * 16050 * 2
def baseEnd_16050 : Nat := 4883771558380704000707

theorem tailTrace_16050 : CollatzResearch.WordTrace tailWord_16050 prefixEnd_16050 4883771558380704000707 := by
  unfold tailWord_16050
  simp only [CollatzResearch.WordTrace]
  refine ⟨146347897965266491719401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 390261061240710644585069 146347897965266491719401)
  ·
    refine ⟨109760923473949868789551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146347897965266491719401 109760923473949868789551)
    ·
      refine ⟨164641385210924803184327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109760923473949868789551 164641385210924803184327)
      ·
        refine ⟨246962077816387204776491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164641385210924803184327 246962077816387204776491)
        ·
          refine ⟨370443116724580807164737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246962077816387204776491 370443116724580807164737)
          ·
            refine ⟨277832337543435605373553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370443116724580807164737 277832337543435605373553)
            ·
              refine ⟨208374253157576704030165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277832337543435605373553 208374253157576704030165)
              ·
                refine ⟨4883771558380704000707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 208374253157576704030165 4883771558380704000707)
                ·
                  rfl

theorem cell19_16050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_16050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16050 prefixEnd_16050 := by exact prefixLift 16050
  have htrace : WordTrace (prefixWord ++ tailWord_16050) baseStart_16050 baseEnd_16050 := by
    simpa [prefixWord, tailWord_16050, baseEnd_16050] using wordTrace_append hprefix tailTrace_16050
  have hstable : (prefixWord ++ tailWord_16050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16050).length < 2 ^ (prefixWord ++ tailWord_16050).sum := by decide
  have hdescent : baseEnd_16050 < baseStart_16050 := by decide
  rcases family_descends (prefixWord ++ tailWord_16050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16088 : List Nat := [2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_16088 : Nat := 118140960795 + 16088 * 2 ^ 59
def prefixEnd_16088 : Nat := 4983230072969 + 3 ^ 40 * 16088 * 2
def baseEnd_16088 : Nat := 4895334382007875156159

theorem tailTrace_16088 : CollatzResearch.WordTrace tailWord_16088 prefixEnd_16088 4895334382007875156159 := by
  unfold tailWord_16088
  simp only [CollatzResearch.WordTrace]
  refine ⟨293388782861699228380459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 391185043815598971173945 293388782861699228380459)
  ·
    refine ⟨440083174292548842570689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293388782861699228380459 440083174292548842570689)
    ·
      refine ⟨330062380719411631928017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440083174292548842570689 330062380719411631928017)
      ·
        refine ⟨247546785539558723946013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330062380719411631928017 247546785539558723946013)
        ·
          refine ⟨92830044577334521479755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247546785539558723946013 92830044577334521479755)
          ·
            refine ⟨139245066866001782219633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92830044577334521479755 139245066866001782219633)
            ·
              refine ⟨104433800149501336664725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139245066866001782219633 104433800149501336664725)
              ·
                refine ⟨4895334382007875156159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104433800149501336664725 4895334382007875156159)
                ·
                  rfl

theorem cell19_16088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_16088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16088 prefixEnd_16088 := by exact prefixLift 16088
  have htrace : WordTrace (prefixWord ++ tailWord_16088) baseStart_16088 baseEnd_16088 := by
    simpa [prefixWord, tailWord_16088, baseEnd_16088] using wordTrace_append hprefix tailTrace_16088
  have hstable : (prefixWord ++ tailWord_16088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16088).length < 2 ^ (prefixWord ++ tailWord_16088).sum := by decide
  have hdescent : baseEnd_16088 < baseStart_16088 := by decide
  rcases family_descends (prefixWord ++ tailWord_16088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16103 : List Nat := [1, 1, 5, 4, 1, 1, 1, 5]
def baseStart_16103 : Nat := 118140960795 + 16103 * 2 ^ 59
def prefixEnd_16103 : Nat := 4983230072969 + 3 ^ 40 * 16103 * 2
def baseEnd_16103 : Nat := 4899898654492284822785

theorem tailTrace_16103 : CollatzResearch.WordTrace tailWord_16103 prefixEnd_16103 4899898654492284822785 := by
  unfold tailWord_16103
  simp only [CollatzResearch.WordTrace]
  refine ⟨587324660669056018556963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 391549773779370679037975 587324660669056018556963)
  ·
    refine ⟨880986991003584027835445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 587324660669056018556963 880986991003584027835445)
    ·
      refine ⟨82592530406586002609573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 880986991003584027835445 82592530406586002609573)
      ·
        refine ⟨15486099451234875489295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82592530406586002609573 15486099451234875489295)
        ·
          refine ⟨23229149176852313233943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15486099451234875489295 23229149176852313233943)
          ·
            refine ⟨34843723765278469850915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23229149176852313233943 34843723765278469850915)
            ·
              refine ⟨52265585647917704776373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34843723765278469850915 52265585647917704776373)
              ·
                refine ⟨4899898654492284822785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52265585647917704776373 4899898654492284822785)
                ·
                  rfl

theorem cell19_16103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 5].length) (baseStart_16103 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16103 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16103 prefixEnd_16103 := by exact prefixLift 16103
  have htrace : WordTrace (prefixWord ++ tailWord_16103) baseStart_16103 baseEnd_16103 := by
    simpa [prefixWord, tailWord_16103, baseEnd_16103] using wordTrace_append hprefix tailTrace_16103
  have hstable : (prefixWord ++ tailWord_16103).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16103).length < 2 ^ (prefixWord ++ tailWord_16103).sum := by decide
  have hdescent : baseEnd_16103 < baseStart_16103 := by decide
  rcases family_descends (prefixWord ++ tailWord_16103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16181 : List Nat := [1, 3, 3, 1, 5, 6]
def baseStart_16181 : Nat := 118140960795 + 16181 * 2 ^ 59
def prefixEnd_16181 : Nat := 4983230072969 + 3 ^ 40 * 16181 * 2
def baseEnd_16181 : Nat := 547070319045690565471

theorem tailTrace_16181 : CollatzResearch.WordTrace tailWord_16181 prefixEnd_16181 547070319045690565471 := by
  unfold tailWord_16181
  simp only [CollatzResearch.WordTrace]
  refine ⟨590169554386475339896397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 393446369590983559930931 590169554386475339896397)
  ·
    refine ⟨221313582894928252461149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 590169554386475339896397 221313582894928252461149)
    ·
      refine ⟨82992593585598094672931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221313582894928252461149 82992593585598094672931)
      ·
        refine ⟨124488890378397142009397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82992593585598094672931 124488890378397142009397)
        ·
          refine ⟨11670833472974732063381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124488890378397142009397 11670833472974732063381)
          ·
            refine ⟨547070319045690565471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11670833472974732063381 547070319045690565471)
            ·
              rfl

theorem cell19_16181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 6].length) (baseStart_16181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16181 prefixEnd_16181 := by exact prefixLift 16181
  have htrace : WordTrace (prefixWord ++ tailWord_16181) baseStart_16181 baseEnd_16181 := by
    simpa [prefixWord, tailWord_16181, baseEnd_16181] using wordTrace_append hprefix tailTrace_16181
  have hstable : (prefixWord ++ tailWord_16181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16181).length < 2 ^ (prefixWord ++ tailWord_16181).sum := by decide
  have hdescent : baseEnd_16181 < baseStart_16181 := by decide
  rcases family_descends (prefixWord ++ tailWord_16181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16200 : List Nat := [2, 1, 3, 1, 1, 6, 1, 4]
def baseStart_16200 : Nat := 118140960795 + 16200 * 2 ^ 59
def prefixEnd_16200 : Nat := 4983230072969 + 3 ^ 40 * 16200 * 2
def baseEnd_16200 : Nat := 4929414283224800666965

theorem tailTrace_16200 : CollatzResearch.WordTrace tailWord_16200 prefixEnd_16200 4929414283224800666965 := by
  unfold tailWord_16200
  simp only [CollatzResearch.WordTrace]
  refine ⟨295431270658820792419027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 393908360878427723225369 295431270658820792419027)
  ·
    refine ⟨443146905988231188628541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295431270658820792419027 443146905988231188628541)
    ·
      refine ⟨166180089745586695735703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443146905988231188628541 166180089745586695735703)
      ·
        refine ⟨249270134618380043603555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166180089745586695735703 249270134618380043603555)
        ·
          refine ⟨373905201927570065405333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249270134618380043603555 373905201927570065405333)
          ·
            refine ⟨17526806340354846815875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 373905201927570065405333 17526806340354846815875)
            ·
              refine ⟨26290209510532270223813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17526806340354846815875 26290209510532270223813)
              ·
                refine ⟨4929414283224800666965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26290209510532270223813 4929414283224800666965)
                ·
                  rfl

theorem cell19_16200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_16200 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16200 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16200 prefixEnd_16200 := by exact prefixLift 16200
  have htrace : WordTrace (prefixWord ++ tailWord_16200) baseStart_16200 baseEnd_16200 := by
    simpa [prefixWord, tailWord_16200, baseEnd_16200] using wordTrace_append hprefix tailTrace_16200
  have hstable : (prefixWord ++ tailWord_16200).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16200).length < 2 ^ (prefixWord ++ tailWord_16200).sum := by decide
  have hdescent : baseEnd_16200 < baseStart_16200 := by decide
  rcases family_descends (prefixWord ++ tailWord_16200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16238 : List Nat := [4, 1, 2, 3, 1, 2, 6]
def baseStart_16238 : Nat := 118140960795 + 16238 * 2 ^ 59
def prefixEnd_16238 : Nat := 4983230072969 + 3 ^ 40 * 16238 * 2
def baseEnd_16238 : Nat := 1646992368950657274139

theorem tailTrace_16238 : CollatzResearch.WordTrace tailWord_16238 prefixEnd_16238 1646992368950657274139 := by
  unfold tailWord_16238
  simp only [CollatzResearch.WordTrace]
  refine ⟨74031064397496759340171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 394832343453316049814245 74031064397496759340171)
  ·
    refine ⟨111046596596245139010257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74031064397496759340171 111046596596245139010257)
    ·
      refine ⟨83284947447183854257693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111046596596245139010257 83284947447183854257693)
      ·
        refine ⟨31231855292693945346635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83284947447183854257693 31231855292693945346635)
        ·
          refine ⟨46847782939040918019953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31231855292693945346635 46847782939040918019953)
          ·
            refine ⟨35135837204280688514965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46847782939040918019953 35135837204280688514965)
            ·
              refine ⟨1646992368950657274139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35135837204280688514965 1646992368950657274139)
              ·
                rfl

theorem cell19_16238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 6].length) (baseStart_16238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16238 prefixEnd_16238 := by exact prefixLift 16238
  have htrace : WordTrace (prefixWord ++ tailWord_16238) baseStart_16238 baseEnd_16238 := by
    simpa [prefixWord, tailWord_16238, baseEnd_16238] using wordTrace_append hprefix tailTrace_16238
  have hstable : (prefixWord ++ tailWord_16238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16238).length < 2 ^ (prefixWord ++ tailWord_16238).sum := by decide
  have hdescent : baseEnd_16238 < baseStart_16238 := by decide
  rcases family_descends (prefixWord ++ tailWord_16238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16270 : List Nat := [4, 1, 1, 5, 2, 1, 2, 3]
def baseStart_16270 : Nat := 118140960795 + 16270 * 2 ^ 59
def prefixEnd_16270 : Nat := 4983230072969 + 3 ^ 40 * 16270 * 2
def baseEnd_16270 : Nat := 4950714221485379111219

theorem tailTrace_16270 : CollatzResearch.WordTrace tailWord_16270 prefixEnd_16270 4950714221485379111219 := by
  unfold tailWord_16270
  simp only [CollatzResearch.WordTrace]
  refine ⟨74176956383005442485783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 395610434042695693257509 74176956383005442485783)
  ·
    refine ⟨111265434574508163728675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74176956383005442485783 111265434574508163728675)
    ·
      refine ⟨166898151861762245593013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111265434574508163728675 166898151861762245593013)
      ·
        refine ⟨15646701737040210524345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166898151861762245593013 15646701737040210524345)
        ·
          refine ⟨11735026302780157893259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15646701737040210524345 11735026302780157893259)
          ·
            refine ⟨17602539454170236839889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11735026302780157893259 17602539454170236839889)
            ·
              refine ⟨13201904590627677629917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17602539454170236839889 13201904590627677629917)
              ·
                refine ⟨4950714221485379111219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13201904590627677629917 4950714221485379111219)
                ·
                  rfl

theorem cell19_16270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_16270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16270 prefixEnd_16270 := by exact prefixLift 16270
  have htrace : WordTrace (prefixWord ++ tailWord_16270) baseStart_16270 baseEnd_16270 := by
    simpa [prefixWord, tailWord_16270, baseEnd_16270] using wordTrace_append hprefix tailTrace_16270
  have hstable : (prefixWord ++ tailWord_16270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16270).length < 2 ^ (prefixWord ++ tailWord_16270).sum := by decide
  have hdescent : baseEnd_16270 < baseStart_16270 := by decide
  rcases family_descends (prefixWord ++ tailWord_16270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16274 : List Nat := [3, 2, 3, 2, 1, 1, 4, 3]
def baseStart_16274 : Nat := 118140960795 + 16274 * 2 ^ 59
def prefixEnd_16274 : Nat := 4983230072969 + 3 ^ 40 * 16274 * 2
def baseEnd_16274 : Nat := 4951931360814555022319

theorem tailTrace_16274 : CollatzResearch.WordTrace tailWord_16274 prefixEnd_16274 4951931360814555022319 := by
  unfold tailWord_16274
  simp only [CollatzResearch.WordTrace]
  refine ⟨148390385762388055757969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 395707695366368148687917 148390385762388055757969)
  ·
    refine ⟨111292789321791041818477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148390385762388055757969 111292789321791041818477)
    ·
      refine ⟨41734795995671640681929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111292789321791041818477 41734795995671640681929)
      ·
        refine ⟨31301096996753730511447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41734795995671640681929 31301096996753730511447)
        ·
          refine ⟨46951645495130595767171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31301096996753730511447 46951645495130595767171)
          ·
            refine ⟨70427468242695893650757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46951645495130595767171 70427468242695893650757)
            ·
              refine ⟨13205150295505480059517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70427468242695893650757 13205150295505480059517)
              ·
                refine ⟨4951931360814555022319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13205150295505480059517 4951931360814555022319)
                ·
                  rfl

theorem cell19_16274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_16274 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16274 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16274 prefixEnd_16274 := by exact prefixLift 16274
  have htrace : WordTrace (prefixWord ++ tailWord_16274) baseStart_16274 baseEnd_16274 := by
    simpa [prefixWord, tailWord_16274, baseEnd_16274] using wordTrace_append hprefix tailTrace_16274
  have hstable : (prefixWord ++ tailWord_16274).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16274).length < 2 ^ (prefixWord ++ tailWord_16274).sum := by decide
  have hdescent : baseEnd_16274 < baseStart_16274 := by decide
  rcases family_descends (prefixWord ++ tailWord_16274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16276 : List Nat := [2, 4, 2, 1, 1, 3, 1, 5]
def baseStart_16276 : Nat := 118140960795 + 16276 * 2 ^ 59
def prefixEnd_16276 : Nat := 4983230072969 + 3 ^ 40 * 16276 * 2
def baseEnd_16276 : Nat := 4952539930479142977869

theorem tailTrace_16276 : CollatzResearch.WordTrace tailWord_16276 prefixEnd_16276 4952539930479142977869 := by
  unfold tailWord_16276
  simp only [CollatzResearch.WordTrace]
  refine ⟨296817244521153282302341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 395756326028204376403121 296817244521153282302341)
  ·
    refine ⟨55653233347716240431689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 296817244521153282302341 55653233347716240431689)
    ·
      refine ⟨41739925010787180323767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55653233347716240431689 41739925010787180323767)
      ·
        refine ⟨62609887516180770485651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41739925010787180323767 62609887516180770485651)
        ·
          refine ⟨93914831274271155728477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62609887516180770485651 93914831274271155728477)
          ·
            refine ⟨35218061727851683398179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93914831274271155728477 35218061727851683398179)
            ·
              refine ⟨52827092591777525097269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35218061727851683398179 52827092591777525097269)
              ·
                refine ⟨4952539930479142977869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52827092591777525097269 4952539930479142977869)
                ·
                  rfl

theorem cell19_16276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_16276 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16276 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16276 prefixEnd_16276 := by exact prefixLift 16276
  have htrace : WordTrace (prefixWord ++ tailWord_16276) baseStart_16276 baseEnd_16276 := by
    simpa [prefixWord, tailWord_16276, baseEnd_16276] using wordTrace_append hprefix tailTrace_16276
  have hstable : (prefixWord ++ tailWord_16276).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16276).length < 2 ^ (prefixWord ++ tailWord_16276).sum := by decide
  have hdescent : baseEnd_16276 < baseStart_16276 := by decide
  rcases family_descends (prefixWord ++ tailWord_16276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16295 : List Nat := [1, 1, 6, 1, 2, 3, 5]
def baseStart_16295 : Nat := 118140960795 + 16295 * 2 ^ 59
def prefixEnd_16295 : Nat := 4983230072969 + 3 ^ 40 * 16295 * 2
def baseEnd_16295 : Nat := 1652773780764242851865

theorem tailTrace_16295 : CollatzResearch.WordTrace tailWord_16295 prefixEnd_16295 1652773780764242851865 := by
  unfold tailWord_16295
  simp only [CollatzResearch.WordTrace]
  refine ⟨594327475973472809546339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 396218317315648539697559 594327475973472809546339)
  ·
    refine ⟨891491213960209214319509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 594327475973472809546339 891491213960209214319509)
    ·
      refine ⟨41788650654384806921227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 891491213960209214319509 41788650654384806921227)
      ·
        refine ⟨62682975981577210381841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41788650654384806921227 62682975981577210381841)
        ·
          refine ⟨47012231986182907786381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62682975981577210381841 47012231986182907786381)
          ·
            refine ⟨17629586994818590419893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47012231986182907786381 17629586994818590419893)
            ·
              refine ⟨1652773780764242851865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17629586994818590419893 1652773780764242851865)
              ·
                rfl

theorem cell19_16295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_16295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16295 prefixEnd_16295 := by exact prefixLift 16295
  have htrace : WordTrace (prefixWord ++ tailWord_16295) baseStart_16295 baseEnd_16295 := by
    simpa [prefixWord, tailWord_16295, baseEnd_16295] using wordTrace_append hprefix tailTrace_16295
  have hstable : (prefixWord ++ tailWord_16295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16295).length < 2 ^ (prefixWord ++ tailWord_16295).sum := by decide
  have hdescent : baseEnd_16295 < baseStart_16295 := by decide
  rcases family_descends (prefixWord ++ tailWord_16295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16348 : List Nat := [2, 2, 6, 1, 2, 6]
def baseStart_16348 : Nat := 118140960795 + 16348 * 2 ^ 59
def prefixEnd_16348 : Nat := 4983230072969 + 3 ^ 40 * 16348 * 2
def baseEnd_16348 : Nat := 552716493156034375297

theorem tailTrace_16348 : CollatzResearch.WordTrace tailWord_16348 prefixEnd_16348 552716493156034375297 := by
  unfold tailWord_16348
  simp only [CollatzResearch.WordTrace]
  refine ⟨298130272390731430612849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 397507029854308574150465 298130272390731430612849)
  ·
    refine ⟨223597704293048572959637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298130272390731430612849 223597704293048572959637)
    ·
      refine ⟨10481142388736651857483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 223597704293048572959637 10481142388736651857483)
      ·
        refine ⟨15721713583104977786225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10481142388736651857483 15721713583104977786225)
        ·
          refine ⟨11791285187328733339669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15721713583104977786225 11791285187328733339669)
          ·
            refine ⟨552716493156034375297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11791285187328733339669 552716493156034375297)
            ·
              rfl

theorem cell19_16348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 6].length) (baseStart_16348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16348 prefixEnd_16348 := by exact prefixLift 16348
  have htrace : WordTrace (prefixWord ++ tailWord_16348) baseStart_16348 baseEnd_16348 := by
    simpa [prefixWord, tailWord_16348, baseEnd_16348] using wordTrace_append hprefix tailTrace_16348
  have hstable : (prefixWord ++ tailWord_16348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16348).length < 2 ^ (prefixWord ++ tailWord_16348).sum := by decide
  have hdescent : baseEnd_16348 < baseStart_16348 := by decide
  rcases family_descends (prefixWord ++ tailWord_16348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16369 : List Nat := [1, 2, 2, 2, 6, 1, 1, 4]
def baseStart_16369 : Nat := 118140960795 + 16369 * 2 ^ 59
def prefixEnd_16369 : Nat := 4983230072969 + 3 ^ 40 * 16369 * 2
def baseEnd_16369 : Nat := 4980838419882482910949

theorem tailTrace_16369 : CollatzResearch.WordTrace tailWord_16369 prefixEnd_16369 4980838419882482910949 := by
  unfold tailWord_16369
  simp only [CollatzResearch.WordTrace]
  refine ⟨597026477705383447740161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 398017651803588965160107 597026477705383447740161)
  ·
    refine ⟨447769858279037585805121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 597026477705383447740161 447769858279037585805121)
    ·
      refine ⟨335827393709278189353841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447769858279037585805121 335827393709278189353841)
      ·
        refine ⟨251870545281958642015381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335827393709278189353841 251870545281958642015381)
        ·
          refine ⟨11806431810091811344471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251870545281958642015381 11806431810091811344471)
          ·
            refine ⟨17709647715137717016707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11806431810091811344471 17709647715137717016707)
            ·
              refine ⟨26564471572706575525061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17709647715137717016707 26564471572706575525061)
              ·
                refine ⟨4980838419882482910949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26564471572706575525061 4980838419882482910949)
                ·
                  rfl

theorem cell19_16369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 4].length) (baseStart_16369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16369 prefixEnd_16369 := by exact prefixLift 16369
  have htrace : WordTrace (prefixWord ++ tailWord_16369) baseStart_16369 baseEnd_16369 := by
    simpa [prefixWord, tailWord_16369, baseEnd_16369] using wordTrace_append hprefix tailTrace_16369
  have hstable : (prefixWord ++ tailWord_16369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16369).length < 2 ^ (prefixWord ++ tailWord_16369).sum := by decide
  have hdescent : baseEnd_16369 < baseStart_16369 := by decide
  rcases family_descends (prefixWord ++ tailWord_16369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16466 : List Nat := [3, 2, 2, 1, 4, 2, 5]
def baseStart_16466 : Nat := 118140960795 + 16466 * 2 ^ 59
def prefixEnd_16466 : Nat := 4983230072969 + 3 ^ 40 * 16466 * 2
def baseEnd_16466 : Nat := 1670118016204999585043

theorem tailTrace_16466 : CollatzResearch.WordTrace tailWord_16466 prefixEnd_16466 1670118016204999585043 := by
  unfold tailWord_16466
  simp only [CollatzResearch.WordTrace]
  refine ⟨150141089588492253505313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 400376238902646009347501 150141089588492253505313)
  ·
    refine ⟨112605817191369190128985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 150141089588492253505313 112605817191369190128985)
    ·
      refine ⟨84454362893526892596739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112605817191369190128985 84454362893526892596739)
      ·
        refine ⟨126681544340290338895109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84454362893526892596739 126681544340290338895109)
        ·
          refine ⟨23752789563804438542833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126681544340290338895109 23752789563804438542833)
          ·
            refine ⟨17814592172853328907125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23752789563804438542833 17814592172853328907125)
            ·
              refine ⟨1670118016204999585043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17814592172853328907125 1670118016204999585043)
              ·
                rfl

theorem cell19_16466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_16466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16466 prefixEnd_16466 := by exact prefixLift 16466
  have htrace : WordTrace (prefixWord ++ tailWord_16466) baseStart_16466 baseEnd_16466 := by
    simpa [prefixWord, tailWord_16466, baseEnd_16466] using wordTrace_append hprefix tailTrace_16466
  have hstable : (prefixWord ++ tailWord_16466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16466).length < 2 ^ (prefixWord ++ tailWord_16466).sum := by decide
  have hdescent : baseEnd_16466 < baseStart_16466 := by decide
  rcases family_descends (prefixWord ++ tailWord_16466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16487 : List Nat := [1, 1, 5, 1, 1, 2, 4, 4]
def baseStart_16487 : Nat := 118140960795 + 16487 * 2 ^ 59
def prefixEnd_16487 : Nat := 4983230072969 + 3 ^ 40 * 16487 * 2
def baseEnd_16487 : Nat := 5016744030093172288405

theorem tailTrace_16487 : CollatzResearch.WordTrace tailWord_16487 prefixEnd_16487 5016744030093172288405 := by
  unfold tailWord_16487
  simp only [CollatzResearch.WordTrace]
  refine ⟨601330291277889600535715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 400886860851926400357143 601330291277889600535715)
  ·
    refine ⟨901995436916834400803573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 601330291277889600535715 901995436916834400803573)
    ·
      refine ⟨84562072210953225075335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 901995436916834400803573 84562072210953225075335)
      ·
        refine ⟨126843108316429837613003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84562072210953225075335 126843108316429837613003)
        ·
          refine ⟨190264662474644756419505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126843108316429837613003 190264662474644756419505)
          ·
            refine ⟨142698496855983567314629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190264662474644756419505 142698496855983567314629)
            ·
              refine ⟨26755968160496918871493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 142698496855983567314629 26755968160496918871493)
              ·
                refine ⟨5016744030093172288405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26755968160496918871493 5016744030093172288405)
                ·
                  rfl

theorem cell19_16487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_16487 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16487 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16487 prefixEnd_16487 := by exact prefixLift 16487
  have htrace : WordTrace (prefixWord ++ tailWord_16487) baseStart_16487 baseEnd_16487 := by
    simpa [prefixWord, tailWord_16487, baseEnd_16487] using wordTrace_append hprefix tailTrace_16487
  have hstable : (prefixWord ++ tailWord_16487).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16487).length < 2 ^ (prefixWord ++ tailWord_16487).sum := by decide
  have hdescent : baseEnd_16487 < baseStart_16487 := by decide
  rcases family_descends (prefixWord ++ tailWord_16487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16534 : List Nat := [5, 3, 2, 1, 1, 2, 1, 4]
def baseStart_16534 : Nat := 118140960795 + 16534 * 2 ^ 59
def prefixEnd_16534 : Nat := 4983230072969 + 3 ^ 40 * 16534 * 2
def baseEnd_16534 : Nat := 5031045417210989243833

theorem tailTrace_16534 : CollatzResearch.WordTrace tailWord_16534 prefixEnd_16534 5031045417210989243833 := by
  unfold tailWord_16534
  simp only [CollatzResearch.WordTrace]
  refine ⟨37690282631726039218541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 402029681405077751664437 37690282631726039218541)
  ·
    refine ⟨14133855986897264706953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37690282631726039218541 14133855986897264706953)
    ·
      refine ⟨10600391990172948530215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14133855986897264706953 10600391990172948530215)
      ·
        refine ⟨15900587985259422795323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10600391990172948530215 15900587985259422795323)
        ·
          refine ⟨23850881977889134192985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15900587985259422795323 23850881977889134192985)
          ·
            refine ⟨17888161483416850644739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23850881977889134192985 17888161483416850644739)
            ·
              refine ⟨26832242225125275967109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17888161483416850644739 26832242225125275967109)
              ·
                refine ⟨5031045417210989243833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26832242225125275967109 5031045417210989243833)
                ·
                  rfl

theorem cell19_16534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_16534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16534 prefixEnd_16534 := by exact prefixLift 16534
  have htrace : WordTrace (prefixWord ++ tailWord_16534) baseStart_16534 baseEnd_16534 := by
    simpa [prefixWord, tailWord_16534, baseEnd_16534] using wordTrace_append hprefix tailTrace_16534
  have hstable : (prefixWord ++ tailWord_16534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16534).length < 2 ^ (prefixWord ++ tailWord_16534).sum := by decide
  have hdescent : baseEnd_16534 < baseStart_16534 := by decide
  rcases family_descends (prefixWord ++ tailWord_16534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16544 : List Nat := [2, 1, 1, 4, 2, 2, 3, 4]
def baseStart_16544 : Nat := 118140960795 + 16544 * 2 ^ 59
def prefixEnd_16544 : Nat := 4983230072969 + 3 ^ 40 * 16544 * 2
def baseEnd_16544 : Nat := 5034088265533929021583

theorem tailTrace_16544 : CollatzResearch.WordTrace tailWord_16544 prefixEnd_16544 5034088265533929021583 := by
  unfold tailWord_16544
  simp only [CollatzResearch.WordTrace]
  refine ⟨301704626035694167680343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 402272834714258890240457 301704626035694167680343)
  ·
    refine ⟨452556939053541251520515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 301704626035694167680343 452556939053541251520515)
    ·
      refine ⟨678835408580311877280773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452556939053541251520515 678835408580311877280773)
      ·
        refine ⟨127281639108808476990145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 678835408580311877280773 127281639108808476990145)
        ·
          refine ⟨95461229331606357742609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127281639108808476990145 95461229331606357742609)
          ·
            refine ⟨71595921998704768306957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95461229331606357742609 71595921998704768306957)
            ·
              refine ⟨26848470749514288115109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71595921998704768306957 26848470749514288115109)
              ·
                refine ⟨5034088265533929021583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26848470749514288115109 5034088265533929021583)
                ·
                  rfl

theorem cell19_16544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_16544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16544 prefixEnd_16544 := by exact prefixLift 16544
  have htrace : WordTrace (prefixWord ++ tailWord_16544) baseStart_16544 baseEnd_16544 := by
    simpa [prefixWord, tailWord_16544, baseEnd_16544] using wordTrace_append hprefix tailTrace_16544
  have hstable : (prefixWord ++ tailWord_16544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16544).length < 2 ^ (prefixWord ++ tailWord_16544).sum := by decide
  have hdescent : baseEnd_16544 < baseStart_16544 := by decide
  rcases family_descends (prefixWord ++ tailWord_16544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16578 : List Nat := [3, 5, 1, 1, 1, 2, 6]
def baseStart_16578 : Nat := 118140960795 + 16578 * 2 ^ 59
def prefixEnd_16578 : Nat := 4983230072969 + 3 ^ 40 * 16578 * 2
def baseEnd_16578 : Nat := 1681477983277308088645

theorem tailTrace_16578 : CollatzResearch.WordTrace tailWord_16578 prefixEnd_16578 1681477983277308088645 := by
  unfold tailWord_16578
  simp only [CollatzResearch.WordTrace]
  refine ⟨151162333487053035524597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 403099555965474761398925 151162333487053035524597)
  ·
    refine ⟨14171468764411222080431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151162333487053035524597 14171468764411222080431)
    ·
      refine ⟨21257203146616833120647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14171468764411222080431 21257203146616833120647)
      ·
        refine ⟨31885804719925249680971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21257203146616833120647 31885804719925249680971)
        ·
          refine ⟨47828707079887874521457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31885804719925249680971 47828707079887874521457)
          ·
            refine ⟨35871530309915905891093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47828707079887874521457 35871530309915905891093)
            ·
              refine ⟨1681477983277308088645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35871530309915905891093 1681477983277308088645)
              ·
                rfl

theorem cell19_16578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 6].length) (baseStart_16578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16578 prefixEnd_16578 := by exact prefixLift 16578
  have htrace : WordTrace (prefixWord ++ tailWord_16578) baseStart_16578 baseEnd_16578 := by
    simpa [prefixWord, tailWord_16578, baseEnd_16578] using wordTrace_append hprefix tailTrace_16578
  have hstable : (prefixWord ++ tailWord_16578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16578).length < 2 ^ (prefixWord ++ tailWord_16578).sum := by decide
  have hdescent : baseEnd_16578 < baseStart_16578 := by decide
  rcases family_descends (prefixWord ++ tailWord_16578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16610 : List Nat := [3, 3, 4, 1, 2, 1, 2, 3]
def baseStart_16610 : Nat := 118140960795 + 16610 * 2 ^ 59
def prefixEnd_16610 : Nat := 4983230072969 + 3 ^ 40 * 16610 * 2
def baseEnd_16610 : Nat := 5054171064465331554737

theorem tailTrace_16610 : CollatzResearch.WordTrace tailWord_16610 prefixEnd_16610 5054171064465331554737 := by
  unfold tailWord_16610
  simp only [CollatzResearch.WordTrace]
  refine ⟨151454117458070401815821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 403877646554854404842189 151454117458070401815821)
  ·
    refine ⟨56795294046776400680933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151454117458070401815821 56795294046776400680933)
    ·
      refine ⟨10649117633770575127675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56795294046776400680933 10649117633770575127675)
      ·
        refine ⟨15973676450655862691513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10649117633770575127675 15973676450655862691513)
        ·
          refine ⟨11980257337991897018635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15973676450655862691513 11980257337991897018635)
          ·
            refine ⟨17970386006987845527953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11980257337991897018635 17970386006987845527953)
            ·
              refine ⟨13477789505240884145965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17970386006987845527953 13477789505240884145965)
              ·
                refine ⟨5054171064465331554737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13477789505240884145965 5054171064465331554737)
                ·
                  rfl

theorem cell19_16610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_16610 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16610 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16610 prefixEnd_16610 := by exact prefixLift 16610
  have htrace : WordTrace (prefixWord ++ tailWord_16610) baseStart_16610 baseEnd_16610 := by
    simpa [prefixWord, tailWord_16610, baseEnd_16610] using wordTrace_append hprefix tailTrace_16610
  have hstable : (prefixWord ++ tailWord_16610).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16610).length < 2 ^ (prefixWord ++ tailWord_16610).sum := by decide
  have hdescent : baseEnd_16610 < baseStart_16610 := by decide
  rcases family_descends (prefixWord ++ tailWord_16610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16698 : List Nat := [3, 1, 1, 1, 4, 9]
def baseStart_16698 : Nat := 118140960795 + 16698 * 2 ^ 59
def prefixEnd_16698 : Nat := 4983230072969 + 3 ^ 40 * 16698 * 2
def baseEnd_16698 : Nat := 564549792189689066549

theorem tailTrace_16698 : CollatzResearch.WordTrace tailWord_16698 prefixEnd_16698 564549792189689066549 := by
  unfold tailWord_16698
  simp only [CollatzResearch.WordTrace]
  refine ⟨152256523378368159116687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 406017395675648424311165 152256523378368159116687)
  ·
    refine ⟨228384785067552238675031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152256523378368159116687 228384785067552238675031)
    ·
      refine ⟨342577177601328358012547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228384785067552238675031 342577177601328358012547)
      ·
        refine ⟨513865766401992537018821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342577177601328358012547 513865766401992537018821)
        ·
          refine ⟨96349831200373600691029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 513865766401992537018821 96349831200373600691029)
          ·
            refine ⟨564549792189689066549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 96349831200373600691029 564549792189689066549)
            ·
              rfl

theorem cell19_16698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 9].length) (baseStart_16698 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16698 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16698 prefixEnd_16698 := by exact prefixLift 16698
  have htrace : WordTrace (prefixWord ++ tailWord_16698) baseStart_16698 baseEnd_16698 := by
    simpa [prefixWord, tailWord_16698, baseEnd_16698] using wordTrace_append hprefix tailTrace_16698
  have hstable : (prefixWord ++ tailWord_16698).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16698).length < 2 ^ (prefixWord ++ tailWord_16698).sum := by decide
  have hdescent : baseEnd_16698 < baseStart_16698 := by decide
  rcases family_descends (prefixWord ++ tailWord_16698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16791 : List Nat := [1, 1, 3, 3, 1, 1, 6, 3]
def baseStart_16791 : Nat := 118140960795 + 16791 * 2 ^ 59
def prefixEnd_16791 : Nat := 4983230072969 + 3 ^ 40 * 16791 * 2
def baseEnd_16791 : Nat := 5109246619110541532021

theorem tailTrace_16791 : CollatzResearch.WordTrace tailWord_16791 prefixEnd_16791 5109246619110541532021 := by
  unfold tailWord_16791
  simp only [CollatzResearch.WordTrace]
  refine ⟨612418082176549519602227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 408278721451033013068151 612418082176549519602227)
  ·
    refine ⟨918627123264824279403341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 612418082176549519602227 918627123264824279403341)
    ·
      refine ⟨344485171224309104776253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 918627123264824279403341 344485171224309104776253)
      ·
        refine ⟨129181939209115914291095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344485171224309104776253 129181939209115914291095)
        ·
          refine ⟨193772908813673871436643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129181939209115914291095 193772908813673871436643)
          ·
            refine ⟨290659363220510807154965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193772908813673871436643 290659363220510807154965)
            ·
              refine ⟨13624657650961444085389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 290659363220510807154965 13624657650961444085389)
              ·
                refine ⟨5109246619110541532021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13624657650961444085389 5109246619110541532021)
                ·
                  rfl

theorem cell19_16791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 3].length) (baseStart_16791 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16791 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16791 prefixEnd_16791 := by exact prefixLift 16791
  have htrace : WordTrace (prefixWord ++ tailWord_16791) baseStart_16791 baseEnd_16791 := by
    simpa [prefixWord, tailWord_16791, baseEnd_16791] using wordTrace_append hprefix tailTrace_16791
  have hstable : (prefixWord ++ tailWord_16791).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16791).length < 2 ^ (prefixWord ++ tailWord_16791).sum := by decide
  have hdescent : baseEnd_16791 < baseStart_16791 := by decide
  rcases family_descends (prefixWord ++ tailWord_16791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16793 : List Nat := [1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_16793 : Nat := 118140960795 + 16793 * 2 ^ 59
def prefixEnd_16793 : Nat := 4983230072969 + 3 ^ 40 * 16793 * 2
def baseEnd_16793 : Nat := 5109855188775129487571

theorem tailTrace_16793 : CollatzResearch.WordTrace tailWord_16793 prefixEnd_16793 5109855188775129487571 := by
  unfold tailWord_16793
  simp only [CollatzResearch.WordTrace]
  refine ⟨612491028169303861175033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 408327352112869240783355 612491028169303861175033)
  ·
    refine ⟨459368271126977895881275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 612491028169303861175033 459368271126977895881275)
    ·
      refine ⟨689052406690466843821913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459368271126977895881275 689052406690466843821913)
      ·
        refine ⟨516789305017850132866435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 689052406690466843821913 516789305017850132866435)
        ·
          refine ⟨775183957526775199299653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516789305017850132866435 775183957526775199299653)
          ·
            refine ⟨145346992036270349868685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 775183957526775199299653 145346992036270349868685)
            ·
              refine ⟨54505122013601381200757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145346992036270349868685 54505122013601381200757)
              ·
                refine ⟨5109855188775129487571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54505122013601381200757 5109855188775129487571)
                ·
                  rfl

theorem cell19_16793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_16793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16793 prefixEnd_16793 := by exact prefixLift 16793
  have htrace : WordTrace (prefixWord ++ tailWord_16793) baseStart_16793 baseEnd_16793 := by
    simpa [prefixWord, tailWord_16793, baseEnd_16793] using wordTrace_append hprefix tailTrace_16793
  have hstable : (prefixWord ++ tailWord_16793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16793).length < 2 ^ (prefixWord ++ tailWord_16793).sum := by decide
  have hdescent : baseEnd_16793 < baseStart_16793 := by decide
  rcases family_descends (prefixWord ++ tailWord_16793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16808 : List Nat := [2, 1, 6, 1, 1, 3, 5]
def baseStart_16808 : Nat := 118140960795 + 16808 * 2 ^ 59
def prefixEnd_16808 : Nat := 4983230072969 + 3 ^ 40 * 16808 * 2
def baseEnd_16808 : Nat := 1704806487086513051399

theorem tailTrace_16808 : CollatzResearch.WordTrace tailWord_16808 prefixEnd_16808 1704806487086513051399 := by
  unfold tailWord_16808
  simp only [CollatzResearch.WordTrace]
  refine ⟨306519061557480711485539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 408692082076640948647385 306519061557480711485539)
  ·
    refine ⟨459778592336221067228309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 306519061557480711485539 459778592336221067228309)
    ·
      refine ⟨21552121515760362526327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 459778592336221067228309 21552121515760362526327)
      ·
        refine ⟨32328182273640543789491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21552121515760362526327 32328182273640543789491)
        ·
          refine ⟨48492273410460815684237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32328182273640543789491 48492273410460815684237)
          ·
            refine ⟨18184602528922805881589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48492273410460815684237 18184602528922805881589)
            ·
              refine ⟨1704806487086513051399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18184602528922805881589 1704806487086513051399)
              ·
                rfl

theorem cell19_16808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_16808 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16808 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16808 prefixEnd_16808 := by exact prefixLift 16808
  have htrace : WordTrace (prefixWord ++ tailWord_16808) baseStart_16808 baseEnd_16808 := by
    simpa [prefixWord, tailWord_16808, baseEnd_16808] using wordTrace_append hprefix tailTrace_16808
  have hstable : (prefixWord ++ tailWord_16808).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16808).length < 2 ^ (prefixWord ++ tailWord_16808).sum := by decide
  have hdescent : baseEnd_16808 < baseStart_16808 := by decide
  rcases family_descends (prefixWord ++ tailWord_16808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16829 : List Nat := [1, 4, 1, 2, 2, 3, 2, 4]
def baseStart_16829 : Nat := 118140960795 + 16829 * 2 ^ 59
def prefixEnd_16829 : Nat := 4983230072969 + 3 ^ 40 * 16829 * 2
def baseEnd_16829 : Nat := 5120809442737712687473

theorem tailTrace_16829 : CollatzResearch.WordTrace tailWord_16829 prefixEnd_16829 5120809442737712687473 := by
  unfold tailWord_16829
  simp only [CollatzResearch.WordTrace]
  refine ⟨613804056038882009485541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 409202704025921339657027 613804056038882009485541)
  ·
    refine ⟨115088260507290376778539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 613804056038882009485541 115088260507290376778539)
    ·
      refine ⟨172632390760935565167809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115088260507290376778539 172632390760935565167809)
      ·
        refine ⟨129474293070701673875857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172632390760935565167809 129474293070701673875857)
        ·
          refine ⟨97105719803026255406893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129474293070701673875857 97105719803026255406893)
          ·
            refine ⟨36414644926134845777585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97105719803026255406893 36414644926134845777585)
            ·
              refine ⟨27310983694601134333189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36414644926134845777585 27310983694601134333189)
              ·
                refine ⟨5120809442737712687473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27310983694601134333189 5120809442737712687473)
                ·
                  rfl

theorem cell19_16829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_16829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16829 prefixEnd_16829 := by exact prefixLift 16829
  have htrace : WordTrace (prefixWord ++ tailWord_16829) baseStart_16829 baseEnd_16829 := by
    simpa [prefixWord, tailWord_16829, baseEnd_16829] using wordTrace_append hprefix tailTrace_16829
  have hstable : (prefixWord ++ tailWord_16829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16829).length < 2 ^ (prefixWord ++ tailWord_16829).sum := by decide
  have hdescent : baseEnd_16829 < baseStart_16829 := by decide
  rcases family_descends (prefixWord ++ tailWord_16829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16867 : List Nat := [1, 1, 1, 6, 4, 6]
def baseStart_16867 : Nat := 118140960795 + 16867 * 2 ^ 59
def prefixEnd_16867 : Nat := 4983230072969 + 3 ^ 40 * 16867 * 2
def baseEnd_16867 : Nat := 570263585151653760325

theorem tailTrace_16867 : CollatzResearch.WordTrace tailWord_16867 prefixEnd_16867 570263585151653760325 := by
  unfold tailWord_16867
  simp only [CollatzResearch.WordTrace]
  refine ⟨615190029901214499368855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 410126686600809666245903 615190029901214499368855)
  ·
    refine ⟨922785044851821749053283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 615190029901214499368855 922785044851821749053283)
    ·
      refine ⟨1384177567277732623579925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922785044851821749053283 1384177567277732623579925)
      ·
        refine ⟨64883323466143716730309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1384177567277732623579925 64883323466143716730309)
        ·
          refine ⟨12165623149901946886933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64883323466143716730309 12165623149901946886933)
          ·
            refine ⟨570263585151653760325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12165623149901946886933 570263585151653760325)
            ·
              rfl

theorem cell19_16867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 6].length) (baseStart_16867 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16867 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16867 prefixEnd_16867 := by exact prefixLift 16867
  have htrace : WordTrace (prefixWord ++ tailWord_16867) baseStart_16867 baseEnd_16867 := by
    simpa [prefixWord, tailWord_16867, baseEnd_16867] using wordTrace_append hprefix tailTrace_16867
  have hstable : (prefixWord ++ tailWord_16867).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16867).length < 2 ^ (prefixWord ++ tailWord_16867).sum := by decide
  have hdescent : baseEnd_16867 < baseStart_16867 := by decide
  rcases family_descends (prefixWord ++ tailWord_16867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16869 : List Nat := [1, 3, 1, 5, 9]
def baseStart_16869 : Nat := 118140960795 + 16869 * 2 ^ 59
def prefixEnd_16869 : Nat := 4983230072969 + 3 ^ 40 * 16869 * 2
def baseEnd_16869 : Nat := 190110401334424881425

theorem tailTrace_16869 : CollatzResearch.WordTrace tailWord_16869 prefixEnd_16869 190110401334424881425 := by
  unfold tailWord_16869
  simp only [CollatzResearch.WordTrace]
  refine ⟨615262975893968840941661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 410175317262645893961107 615262975893968840941661)
  ·
    refine ⟨230723615960238315353123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 615262975893968840941661 230723615960238315353123)
    ·
      refine ⟨346085423940357473029685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230723615960238315353123 346085423940357473029685)
      ·
        refine ⟨32445508494408513096533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 346085423940357473029685 32445508494408513096533)
        ·
          refine ⟨190110401334424881425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 32445508494408513096533 190110401334424881425)
          ·
            rfl

theorem cell19_16869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 9].length) (baseStart_16869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16869 prefixEnd_16869 := by exact prefixLift 16869
  have htrace : WordTrace (prefixWord ++ tailWord_16869) baseStart_16869 baseEnd_16869 := by
    simpa [prefixWord, tailWord_16869, baseEnd_16869] using wordTrace_append hprefix tailTrace_16869
  have hstable : (prefixWord ++ tailWord_16869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16869).length < 2 ^ (prefixWord ++ tailWord_16869).sum := by decide
  have hdescent : baseEnd_16869 < baseStart_16869 := by decide
  rcases family_descends (prefixWord ++ tailWord_16869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16882 : List Nat := [3, 2, 1, 4, 3, 1, 1, 4]
def baseStart_16882 : Nat := 118140960795 + 16882 * 2 ^ 59
def prefixEnd_16882 : Nat := 4983230072969 + 3 ^ 40 * 16882 * 2
def baseEnd_16882 : Nat := 5136936538849293509551

theorem tailTrace_16882 : CollatzResearch.WordTrace tailWord_16882 prefixEnd_16882 5136936538849293509551 := by
  unfold tailWord_16882
  simp only [CollatzResearch.WordTrace]
  refine ⟨153934281211718015291225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 410491416564581374109933 153934281211718015291225)
  ·
    refine ⟨115450710908788511468419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153934281211718015291225 115450710908788511468419)
    ·
      refine ⟨173176066363182767202629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115450710908788511468419 173176066363182767202629)
      ·
        refine ⟨32470512443096768850493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173176066363182767202629 32470512443096768850493)
        ·
          refine ⟨12176442166161288318935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32470512443096768850493 12176442166161288318935)
          ·
            refine ⟨18264663249241932478403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12176442166161288318935 18264663249241932478403)
            ·
              refine ⟨27396994873862898717605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18264663249241932478403 27396994873862898717605)
              ·
                refine ⟨5136936538849293509551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27396994873862898717605 5136936538849293509551)
                ·
                  rfl

theorem cell19_16882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_16882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16882 prefixEnd_16882 := by exact prefixLift 16882
  have htrace : WordTrace (prefixWord ++ tailWord_16882) baseStart_16882 baseEnd_16882 := by
    simpa [prefixWord, tailWord_16882, baseEnd_16882] using wordTrace_append hprefix tailTrace_16882
  have hstable : (prefixWord ++ tailWord_16882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16882).length < 2 ^ (prefixWord ++ tailWord_16882).sum := by decide
  have hdescent : baseEnd_16882 < baseStart_16882 := by decide
  rcases family_descends (prefixWord ++ tailWord_16882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_16903 : List Nat := [1, 1, 4, 3, 3, 1, 3, 3]
def baseStart_16903 : Nat := 118140960795 + 16903 * 2 ^ 59
def prefixEnd_16903 : Nat := 4983230072969 + 3 ^ 40 * 16903 * 2
def baseEnd_16903 : Nat := 5143326520327467042827

theorem tailTrace_16903 : CollatzResearch.WordTrace tailWord_16903 prefixEnd_16903 5143326520327467042827 := by
  unfold tailWord_16903
  simp only [CollatzResearch.WordTrace]
  refine ⟨616503057770792647679363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 411002038513861765119575 616503057770792647679363)
  ·
    refine ⟨924754586656188971519045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 616503057770792647679363 924754586656188971519045)
    ·
      refine ⟨173391484998035432159821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 924754586656188971519045 173391484998035432159821)
      ·
        refine ⟨65021806874263287059933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173391484998035432159821 65021806874263287059933)
        ·
          refine ⟨24383177577848732647475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65021806874263287059933 24383177577848732647475)
          ·
            refine ⟨36574766366773098971213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24383177577848732647475 36574766366773098971213)
            ·
              refine ⟨13715537387539912114205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36574766366773098971213 13715537387539912114205)
              ·
                refine ⟨5143326520327467042827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13715537387539912114205 5143326520327467042827)
                ·
                  rfl

theorem cell19_16903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 3].length) (baseStart_16903 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_16903 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_16903 prefixEnd_16903 := by exact prefixLift 16903
  have htrace : WordTrace (prefixWord ++ tailWord_16903) baseStart_16903 baseEnd_16903 := by
    simpa [prefixWord, tailWord_16903, baseEnd_16903] using wordTrace_append hprefix tailTrace_16903
  have hstable : (prefixWord ++ tailWord_16903).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_16903).length < 2 ^ (prefixWord ++ tailWord_16903).sum := by decide
  have hdescent : baseEnd_16903 < baseStart_16903 := by decide
  rcases family_descends (prefixWord ++ tailWord_16903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17135 : List Nat := [1, 1, 2, 1, 5, 3, 1, 5]
def baseStart_17135 : Nat := 118140960795 + 17135 * 2 ^ 59
def prefixEnd_17135 : Nat := 4983230072969 + 3 ^ 40 * 17135 * 2
def baseEnd_17135 : Nat := 5213920601419669886639

theorem tailTrace_17135 : CollatzResearch.WordTrace tailWord_17135 prefixEnd_17135 5213920601419669886639 := by
  unfold tailWord_17135
  simp only [CollatzResearch.WordTrace]
  refine ⟨624964792930296270124859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 416643195286864180083239 624964792930296270124859)
  ·
    refine ⟨937447189395444405187289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 624964792930296270124859 937447189395444405187289)
    ·
      refine ⟨703085392046583303890467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 937447189395444405187289 703085392046583303890467)
      ·
        refine ⟨1054628088069874955835701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703085392046583303890467 1054628088069874955835701)
        ·
          refine ⟨98871383256550777109597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1054628088069874955835701 98871383256550777109597)
          ·
            refine ⟨37076768721206541416099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98871383256550777109597 37076768721206541416099)
            ·
              refine ⟨55615153081809812124149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37076768721206541416099 55615153081809812124149)
              ·
                refine ⟨5213920601419669886639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55615153081809812124149 5213920601419669886639)
                ·
                  rfl

theorem cell19_17135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_17135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17135 prefixEnd_17135 := by exact prefixLift 17135
  have htrace : WordTrace (prefixWord ++ tailWord_17135) baseStart_17135 baseEnd_17135 := by
    simpa [prefixWord, tailWord_17135, baseEnd_17135] using wordTrace_append hprefix tailTrace_17135
  have hstable : (prefixWord ++ tailWord_17135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17135).length < 2 ^ (prefixWord ++ tailWord_17135).sum := by decide
  have hdescent : baseEnd_17135 < baseStart_17135 := by decide
  rcases family_descends (prefixWord ++ tailWord_17135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17173 : List Nat := [1, 3, 2, 1, 2, 2, 4, 4]
def baseStart_17173 : Nat := 118140960795 + 17173 * 2 ^ 59
def prefixEnd_17173 : Nat := 4983230072969 + 3 ^ 40 * 17173 * 2
def baseEnd_17173 : Nat := 5225483425046841042091

theorem tailTrace_17173 : CollatzResearch.WordTrace tailWord_17173 prefixEnd_17173 5225483425046841042091 := by
  unfold tailWord_17173
  simp only [CollatzResearch.WordTrace]
  refine ⟨626350766792628760008173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 417567177861752506672115 626350766792628760008173)
  ·
    refine ⟨234881537547235785003065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 626350766792628760008173 234881537547235785003065)
    ·
      refine ⟨176161153160426838752299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234881537547235785003065 176161153160426838752299)
      ·
        refine ⟨264241729740640258128449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176161153160426838752299 264241729740640258128449)
        ·
          refine ⟨198181297305480193596337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264241729740640258128449 198181297305480193596337)
          ·
            refine ⟨148635972979110145197253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198181297305480193596337 148635972979110145197253)
            ·
              refine ⟨27869244933583152224485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148635972979110145197253 27869244933583152224485)
              ·
                refine ⟨5225483425046841042091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27869244933583152224485 5225483425046841042091)
                ·
                  rfl

theorem cell19_17173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_17173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17173 prefixEnd_17173 := by exact prefixLift 17173
  have htrace : WordTrace (prefixWord ++ tailWord_17173) baseStart_17173 baseEnd_17173 := by
    simpa [prefixWord, tailWord_17173, baseEnd_17173] using wordTrace_append hprefix tailTrace_17173
  have hstable : (prefixWord ++ tailWord_17173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17173).length < 2 ^ (prefixWord ++ tailWord_17173).sum := by decide
  have hdescent : baseEnd_17173 < baseStart_17173 := by decide
  rcases family_descends (prefixWord ++ tailWord_17173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17192 : List Nat := [2, 1, 5, 1, 1, 1, 1, 7]
def baseStart_17192 : Nat := 118140960795 + 17192 * 2 ^ 59
def prefixEnd_17192 : Nat := 4983230072969 + 3 ^ 40 * 17192 * 2
def baseEnd_17192 : Nat := 5231264836860426619817

theorem tailTrace_17192 : CollatzResearch.WordTrace tailWord_17192 prefixEnd_17192 5231264836860426619817 := by
  unfold tailWord_17192
  simp only [CollatzResearch.WordTrace]
  refine ⟨313521876861897502474915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 418029169149196669966553 313521876861897502474915)
  ·
    refine ⟨470282815292846253712373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 313521876861897502474915 470282815292846253712373)
    ·
      refine ⟨44089013933704336285535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 470282815292846253712373 44089013933704336285535)
      ·
        refine ⟨66133520900556504428303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44089013933704336285535 66133520900556504428303)
        ·
          refine ⟨99200281350834756642455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66133520900556504428303 99200281350834756642455)
          ·
            refine ⟨148800422026252134963683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99200281350834756642455 148800422026252134963683)
            ·
              refine ⟨223200633039378202445525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148800422026252134963683 223200633039378202445525)
              ·
                refine ⟨5231264836860426619817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 223200633039378202445525 5231264836860426619817)
                ·
                  rfl

theorem cell19_17192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_17192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17192 prefixEnd_17192 := by exact prefixLift 17192
  have htrace : WordTrace (prefixWord ++ tailWord_17192) baseStart_17192 baseEnd_17192 := by
    simpa [prefixWord, tailWord_17192, baseEnd_17192] using wordTrace_append hprefix tailTrace_17192
  have hstable : (prefixWord ++ tailWord_17192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17192).length < 2 ^ (prefixWord ++ tailWord_17192).sum := by decide
  have hdescent : baseEnd_17192 < baseStart_17192 := by decide
  rcases family_descends (prefixWord ++ tailWord_17192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17222 : List Nat := [6, 1, 1, 2, 3, 1, 1, 4]
def baseStart_17222 : Nat := 118140960795 + 17222 * 2 ^ 59
def prefixEnd_17222 : Nat := 4983230072969 + 3 ^ 40 * 17222 * 2
def baseEnd_17222 : Nat := 5240393381829245953069

theorem tailTrace_17222 : CollatzResearch.WordTrace tailWord_17222 prefixEnd_17222 5240393381829245953069 := by
  unfold tailWord_17222
  simp only [CollatzResearch.WordTrace]
  refine ⟨19629310737972191516935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 418758629076740085694613 19629310737972191516935)
  ·
    refine ⟨29443966106958287275403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19629310737972191516935 29443966106958287275403)
    ·
      refine ⟨44165949160437430913105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29443966106958287275403 44165949160437430913105)
      ·
        refine ⟨33124461870328073184829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44165949160437430913105 33124461870328073184829)
        ·
          refine ⟨12421673201373027444311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33124461870328073184829 12421673201373027444311)
          ·
            refine ⟨18632509802059541166467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12421673201373027444311 18632509802059541166467)
            ·
              refine ⟨27948764703089311749701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18632509802059541166467 27948764703089311749701)
              ·
                refine ⟨5240393381829245953069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27948764703089311749701 5240393381829245953069)
                ·
                  rfl

theorem cell19_17222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_17222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17222 prefixEnd_17222 := by exact prefixLift 17222
  have htrace : WordTrace (prefixWord ++ tailWord_17222) baseStart_17222 baseEnd_17222 := by
    simpa [prefixWord, tailWord_17222, baseEnd_17222] using wordTrace_append hprefix tailTrace_17222
  have hstable : (prefixWord ++ tailWord_17222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17222).length < 2 ^ (prefixWord ++ tailWord_17222).sum := by decide
  have hdescent : baseEnd_17222 < baseStart_17222 := by decide
  rcases family_descends (prefixWord ++ tailWord_17222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17228 : List Nat := [2, 2, 1, 3, 3, 3, 1, 4]
def baseStart_17228 : Nat := 118140960795 + 17228 * 2 ^ 59
def prefixEnd_17228 : Nat := 4983230072969 + 3 ^ 40 * 17228 * 2
def baseEnd_17228 : Nat := 5242219090823009819719

theorem tailTrace_17228 : CollatzResearch.WordTrace tailWord_17228 prefixEnd_17228 5242219090823009819719 := by
  unfold tailWord_17228
  simp only [CollatzResearch.WordTrace]
  refine ⟨314178390796686576630169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 418904521062248768840225 314178390796686576630169)
  ·
    refine ⟨235633793097514932472627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 314178390796686576630169 235633793097514932472627)
    ·
      refine ⟨353450689646272398708941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235633793097514932472627 353450689646272398708941)
      ·
        refine ⟨132544008617352149515853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 353450689646272398708941 132544008617352149515853)
        ·
          refine ⟨49704003231507056068445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132544008617352149515853 49704003231507056068445)
          ·
            refine ⟨18639001211815146025667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49704003231507056068445 18639001211815146025667)
            ·
              refine ⟨27958501817722719038501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18639001211815146025667 27958501817722719038501)
              ·
                refine ⟨5242219090823009819719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27958501817722719038501 5242219090823009819719)
                ·
                  rfl

theorem cell19_17228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_17228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17228 prefixEnd_17228 := by exact prefixLift 17228
  have htrace : WordTrace (prefixWord ++ tailWord_17228) baseStart_17228 baseEnd_17228 := by
    simpa [prefixWord, tailWord_17228, baseEnd_17228] using wordTrace_append hprefix tailTrace_17228
  have hstable : (prefixWord ++ tailWord_17228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17228).length < 2 ^ (prefixWord ++ tailWord_17228).sum := by decide
  have hdescent : baseEnd_17228 < baseStart_17228 := by decide
  rcases family_descends (prefixWord ++ tailWord_17228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17344 : List Nat := [2, 1, 1, 2, 3, 4, 2, 4]
def baseStart_17344 : Nat := 118140960795 + 17344 * 2 ^ 59
def prefixEnd_17344 : Nat := 4983230072969 + 3 ^ 40 * 17344 * 2
def baseEnd_17344 : Nat := 5277516131369111241625

theorem tailTrace_17344 : CollatzResearch.WordTrace tailWord_17344 prefixEnd_17344 5277516131369111241625 := by
  unfold tailWord_17344
  simp only [CollatzResearch.WordTrace]
  refine ⟨316293824586562482241543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 421725099448749976322057 316293824586562482241543)
  ·
    refine ⟨474440736879843723362315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 316293824586562482241543 474440736879843723362315)
    ·
      refine ⟨711661105319765585043473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474440736879843723362315 711661105319765585043473)
      ·
        refine ⟨533745828989824188782605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 711661105319765585043473 533745828989824188782605)
        ·
          refine ⟨200154685871184070793477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 533745828989824188782605 200154685871184070793477)
          ·
            refine ⟨37529003600847013273777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200154685871184070793477 37529003600847013273777)
            ·
              refine ⟨28146752700635259955333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37529003600847013273777 28146752700635259955333)
              ·
                refine ⟨5277516131369111241625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28146752700635259955333 5277516131369111241625)
                ·
                  rfl

theorem cell19_17344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_17344 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17344 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17344 prefixEnd_17344 := by exact prefixLift 17344
  have htrace : WordTrace (prefixWord ++ tailWord_17344) baseStart_17344 baseEnd_17344 := by
    simpa [prefixWord, tailWord_17344, baseEnd_17344] using wordTrace_append hprefix tailTrace_17344
  have hstable : (prefixWord ++ tailWord_17344).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17344).length < 2 ^ (prefixWord ++ tailWord_17344).sum := by decide
  have hdescent : baseEnd_17344 < baseStart_17344 := by decide
  rcases family_descends (prefixWord ++ tailWord_17344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17418 : List Nat := [3, 1, 2, 2, 3, 2, 3, 3]
def baseStart_17418 : Nat := 118140960795 + 17418 * 2 ^ 59
def prefixEnd_17418 : Nat := 4983230072969 + 3 ^ 40 * 17418 * 2
def baseEnd_17418 : Nat := 5300033208958865596979

theorem tailTrace_17418 : CollatzResearch.WordTrace tailWord_17418 prefixEnd_17418 5300033208958865596979 := by
  unfold tailWord_17418
  simp only [CollatzResearch.WordTrace]
  refine ⟨158821662726258900669227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 423524433936690401784605 158821662726258900669227)
  ·
    refine ⟨238232494089388351003841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158821662726258900669227 238232494089388351003841)
    ·
      refine ⟨178674370567041263252881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238232494089388351003841 178674370567041263252881)
      ·
        refine ⟨134005777925280947439661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178674370567041263252881 134005777925280947439661)
        ·
          refine ⟨50252166721980355289873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134005777925280947439661 50252166721980355289873)
          ·
            refine ⟨37689125041485266467405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50252166721980355289873 37689125041485266467405)
            ·
              refine ⟨14133421890556974925277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37689125041485266467405 14133421890556974925277)
              ·
                refine ⟨5300033208958865596979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14133421890556974925277 5300033208958865596979)
                ·
                  rfl

theorem cell19_17418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_17418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17418 prefixEnd_17418 := by exact prefixLift 17418
  have htrace : WordTrace (prefixWord ++ tailWord_17418) baseStart_17418 baseEnd_17418 := by
    simpa [prefixWord, tailWord_17418, baseEnd_17418] using wordTrace_append hprefix tailTrace_17418
  have hstable : (prefixWord ++ tailWord_17418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17418).length < 2 ^ (prefixWord ++ tailWord_17418).sum := by decide
  have hdescent : baseEnd_17418 < baseStart_17418 := by decide
  rcases family_descends (prefixWord ++ tailWord_17418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17473 : List Nat := [1, 2, 5, 1, 3, 2, 2, 3]
def baseStart_17473 : Nat := 118140960795 + 17473 * 2 ^ 59
def prefixEnd_17473 : Nat := 4983230072969 + 3 ^ 40 * 17473 * 2
def baseEnd_17473 : Nat := 5316768874735034374607

theorem tailTrace_17473 : CollatzResearch.WordTrace tailWord_17473 prefixEnd_17473 5316768874735034374607 := by
  unfold tailWord_17473
  simp only [CollatzResearch.WordTrace]
  refine ⟨637292665705779995929073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 424861777137186663952715 637292665705779995929073)
  ·
    refine ⟨477969499279334996946805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 637292665705779995929073 477969499279334996946805)
    ·
      refine ⟨44809640557437655963763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 477969499279334996946805 44809640557437655963763)
      ·
        refine ⟨67214460836156483945645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44809640557437655963763 67214460836156483945645)
        ·
          refine ⟨25205422813558681479617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67214460836156483945645 25205422813558681479617)
          ·
            refine ⟨18904067110169011109713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25205422813558681479617 18904067110169011109713)
            ·
              refine ⟨14178050332626758332285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18904067110169011109713 14178050332626758332285)
              ·
                refine ⟨5316768874735034374607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14178050332626758332285 5316768874735034374607)
                ·
                  rfl

theorem cell19_17473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 3].length) (baseStart_17473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17473 prefixEnd_17473 := by exact prefixLift 17473
  have htrace : WordTrace (prefixWord ++ tailWord_17473) baseStart_17473 baseEnd_17473 := by
    simpa [prefixWord, tailWord_17473, baseEnd_17473] using wordTrace_append hprefix tailTrace_17473
  have hstable : (prefixWord ++ tailWord_17473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17473).length < 2 ^ (prefixWord ++ tailWord_17473).sum := by decide
  have hdescent : baseEnd_17473 < baseStart_17473 := by decide
  rcases family_descends (prefixWord ++ tailWord_17473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17477 : List Nat := [1, 3, 1, 1, 1, 3, 6, 3]
def baseStart_17477 : Nat := 118140960795 + 17477 * 2 ^ 59
def prefixEnd_17477 : Nat := 4983230072969 + 3 ^ 40 * 17477 * 2
def baseEnd_17477 : Nat := 5317986014064210285707

theorem tailTrace_17477 : CollatzResearch.WordTrace tailWord_17477 prefixEnd_17477 5317986014064210285707 := by
  unfold tailWord_17477
  simp only [CollatzResearch.WordTrace]
  refine ⟨637438557691288679074685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 424959038460859119383123 637438557691288679074685)
  ·
    refine ⟨239039459134233254653007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 637438557691288679074685 239039459134233254653007)
    ·
      refine ⟨358559188701349881979511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239039459134233254653007 358559188701349881979511)
      ·
        refine ⟨537838783052024822969267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358559188701349881979511 537838783052024822969267)
        ·
          refine ⟨806758174578037234453901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537838783052024822969267 806758174578037234453901)
          ·
            refine ⟨302534315466763962920213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 806758174578037234453901 302534315466763962920213)
            ·
              refine ⟨14181296037504560761885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 302534315466763962920213 14181296037504560761885)
              ·
                refine ⟨5317986014064210285707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14181296037504560761885 5317986014064210285707)
                ·
                  rfl

theorem cell19_17477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 3].length) (baseStart_17477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17477 prefixEnd_17477 := by exact prefixLift 17477
  have htrace : WordTrace (prefixWord ++ tailWord_17477) baseStart_17477 baseEnd_17477 := by
    simpa [prefixWord, tailWord_17477, baseEnd_17477] using wordTrace_append hprefix tailTrace_17477
  have hstable : (prefixWord ++ tailWord_17477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17477).length < 2 ^ (prefixWord ++ tailWord_17477).sum := by decide
  have hdescent : baseEnd_17477 < baseStart_17477 := by decide
  rcases family_descends (prefixWord ++ tailWord_17477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17536 : List Nat := [2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_17536 : Nat := 118140960795 + 17536 * 2 ^ 59
def prefixEnd_17536 : Nat := 4983230072969 + 3 ^ 40 * 17536 * 2
def baseEnd_17536 : Nat := 5335938819169554974435

theorem tailTrace_17536 : CollatzResearch.WordTrace tailWord_17536 prefixEnd_17536 5335938819169554974435 := by
  unfold tailWord_17536
  simp only [CollatzResearch.WordTrace]
  refine ⟨319795232238770877736231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 426393642985027836981641 319795232238770877736231)
  ·
    refine ⟨479692848358156316604347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 319795232238770877736231 479692848358156316604347)
    ·
      refine ⟨719539272537234474906521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 479692848358156316604347 719539272537234474906521)
      ·
        refine ⟨539654454402925856179891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 719539272537234474906521 539654454402925856179891)
        ·
          refine ⟨809481681604388784269837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539654454402925856179891 809481681604388784269837)
          ·
            refine ⟨303555630601645794101189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 809481681604388784269837 303555630601645794101189)
            ·
              refine ⟨56916680737808586393973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 303555630601645794101189 56916680737808586393973)
              ·
                refine ⟨5335938819169554974435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56916680737808586393973 5335938819169554974435)
                ·
                  rfl

theorem cell19_17536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_17536 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17536 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17536 prefixEnd_17536 := by exact prefixLift 17536
  have htrace : WordTrace (prefixWord ++ tailWord_17536) baseStart_17536 baseEnd_17536 := by
    simpa [prefixWord, tailWord_17536, baseEnd_17536] using wordTrace_append hprefix tailTrace_17536
  have hstable : (prefixWord ++ tailWord_17536).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17536).length < 2 ^ (prefixWord ++ tailWord_17536).sum := by decide
  have hdescent : baseEnd_17536 < baseStart_17536 := by decide
  rcases family_descends (prefixWord ++ tailWord_17536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17572 : List Nat := [2, 3, 1, 2, 3, 1, 3, 4]
def baseStart_17572 : Nat := 118140960795 + 17572 * 2 ^ 59
def prefixEnd_17572 : Nat := 4983230072969 + 3 ^ 40 * 17572 * 2
def baseEnd_17572 : Nat := 5346893073132138174337

theorem tailTrace_17572 : CollatzResearch.WordTrace tailWord_17572 prefixEnd_17572 5346893073132138174337 := by
  unfold tailWord_17572
  simp only [CollatzResearch.WordTrace]
  refine ⟨320451746173559951891485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 427268994898079935855313 320451746173559951891485)
  ·
    refine ⟨120169404815084981959307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 320451746173559951891485 120169404815084981959307)
    ·
      refine ⟨180254107222627472938961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120169404815084981959307 180254107222627472938961)
      ·
        refine ⟨135190580416970604704221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180254107222627472938961 135190580416970604704221)
        ·
          refine ⟨50696467656363976764083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135190580416970604704221 50696467656363976764083)
          ·
            refine ⟨76044701484545965146125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50696467656363976764083 76044701484545965146125)
            ·
              refine ⟨28516763056704736929797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76044701484545965146125 28516763056704736929797)
              ·
                refine ⟨5346893073132138174337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28516763056704736929797 5346893073132138174337)
                ·
                  rfl

theorem cell19_17572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_17572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17572 prefixEnd_17572 := by exact prefixLift 17572
  have htrace : WordTrace (prefixWord ++ tailWord_17572) baseStart_17572 baseEnd_17572 := by
    simpa [prefixWord, tailWord_17572, baseEnd_17572] using wordTrace_append hprefix tailTrace_17572
  have hstable : (prefixWord ++ tailWord_17572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17572).length < 2 ^ (prefixWord ++ tailWord_17572).sum := by decide
  have hdescent : baseEnd_17572 < baseStart_17572 := by decide
  rcases family_descends (prefixWord ++ tailWord_17572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17591 : List Nat := [1, 1, 3, 1, 4, 1, 5, 3]
def baseStart_17591 : Nat := 118140960795 + 17591 * 2 ^ 59
def prefixEnd_17591 : Nat := 4983230072969 + 3 ^ 40 * 17591 * 2
def baseEnd_17591 : Nat := 5352674484945723752063

theorem tailTrace_17591 : CollatzResearch.WordTrace tailWord_17591 prefixEnd_17591 5352674484945723752063 := by
  unfold tailWord_17591
  simp only [CollatzResearch.WordTrace]
  refine ⟨641596479278286148724627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 427730986185524099149751 641596479278286148724627)
  ·
    refine ⟨962394718917429223086941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 641596479278286148724627 962394718917429223086941)
    ·
      refine ⟨360898019594035958657603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 962394718917429223086941 360898019594035958657603)
      ·
        refine ⟨541347029391053937986405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360898019594035958657603 541347029391053937986405)
        ·
          refine ⟨101502568010822613372451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 541347029391053937986405 101502568010822613372451)
          ·
            refine ⟨152253852016233920058677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101502568010822613372451 152253852016233920058677)
            ·
              refine ⟨14273798626521930005501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152253852016233920058677 14273798626521930005501)
              ·
                refine ⟨5352674484945723752063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14273798626521930005501 5352674484945723752063)
                ·
                  rfl

theorem cell19_17591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 3].length) (baseStart_17591 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17591 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17591 prefixEnd_17591 := by exact prefixLift 17591
  have htrace : WordTrace (prefixWord ++ tailWord_17591) baseStart_17591 baseEnd_17591 := by
    simpa [prefixWord, tailWord_17591, baseEnd_17591] using wordTrace_append hprefix tailTrace_17591
  have hstable : (prefixWord ++ tailWord_17591).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17591).length < 2 ^ (prefixWord ++ tailWord_17591).sum := by decide
  have hdescent : baseEnd_17591 < baseStart_17591 := by decide
  rcases family_descends (prefixWord ++ tailWord_17591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17682 : List Nat := [3, 2, 4, 2, 1, 1, 2, 4]
def baseStart_17682 : Nat := 118140960795 + 17682 * 2 ^ 59
def prefixEnd_17682 : Nat := 4983230072969 + 3 ^ 40 * 17682 * 2
def baseEnd_17682 : Nat := 5380364404684475729593

theorem tailTrace_17682 : CollatzResearch.WordTrace tailWord_17682 prefixEnd_17682 5380364404684475729593 := by
  unfold tailWord_17682
  simp only [CollatzResearch.WordTrace]
  refine ⟨161228880487152172571825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 429943681299072460191533 161228880487152172571825)
  ·
    refine ⟨120921660365364129428869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161228880487152172571825 120921660365364129428869)
    ·
      refine ⟨22672811318505774267913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120921660365364129428869 22672811318505774267913)
      ·
        refine ⟨17004608488879330700935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22672811318505774267913 17004608488879330700935)
        ·
          refine ⟨25506912733318996051403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17004608488879330700935 25506912733318996051403)
          ·
            refine ⟨38260369099978494077105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25506912733318996051403 38260369099978494077105)
            ·
              refine ⟨28695276824983870557829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38260369099978494077105 28695276824983870557829)
              ·
                refine ⟨5380364404684475729593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28695276824983870557829 5380364404684475729593)
                ·
                  rfl

theorem cell19_17682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_17682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17682 prefixEnd_17682 := by exact prefixLift 17682
  have htrace : WordTrace (prefixWord ++ tailWord_17682) baseStart_17682 baseEnd_17682 := by
    simpa [prefixWord, tailWord_17682, baseEnd_17682] using wordTrace_append hprefix tailTrace_17682
  have hstable : (prefixWord ++ tailWord_17682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17682).length < 2 ^ (prefixWord ++ tailWord_17682).sum := by decide
  have hdescent : baseEnd_17682 < baseStart_17682 := by decide
  rcases family_descends (prefixWord ++ tailWord_17682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17688 : List Nat := [2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_17688 : Nat := 118140960795 + 17688 * 2 ^ 59
def prefixEnd_17688 : Nat := 4983230072969 + 3 ^ 40 * 17688 * 2
def baseEnd_17688 : Nat := 5382190113678239596243

theorem tailTrace_17688 : CollatzResearch.WordTrace tailWord_17688 prefixEnd_17688 5382190113678239596243 := by
  unfold tailWord_17688
  simp only [CollatzResearch.WordTrace]
  refine ⟨322567179963435857502859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 430089573284581143337145 322567179963435857502859)
  ·
    refine ⟨483850769945153786254289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 322567179963435857502859 483850769945153786254289)
    ·
      refine ⟨362888077458865339690717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 483850769945153786254289 362888077458865339690717)
      ·
        refine ⟨136083029047074502384019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362888077458865339690717 136083029047074502384019)
        ·
          refine ⟨204124543570611753576029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136083029047074502384019 204124543570611753576029)
          ·
            refine ⟨76546703838979407591011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204124543570611753576029 76546703838979407591011)
            ·
              refine ⟨114820055758469111386517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76546703838979407591011 114820055758469111386517)
              ·
                refine ⟨5382190113678239596243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114820055758469111386517 5382190113678239596243)
                ·
                  rfl

theorem cell19_17688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_17688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17688 prefixEnd_17688 := by exact prefixLift 17688
  have htrace : WordTrace (prefixWord ++ tailWord_17688) baseStart_17688 baseEnd_17688 := by
    simpa [prefixWord, tailWord_17688, baseEnd_17688] using wordTrace_append hprefix tailTrace_17688
  have hstable : (prefixWord ++ tailWord_17688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17688).length < 2 ^ (prefixWord ++ tailWord_17688).sum := by decide
  have hdescent : baseEnd_17688 < baseStart_17688 := by decide
  rcases family_descends (prefixWord ++ tailWord_17688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17781 : List Nat := [1, 3, 4, 1, 3, 1, 6]
def baseStart_17781 : Nat := 118140960795 + 17781 * 2 ^ 59
def prefixEnd_17781 : Nat := 4983230072969 + 3 ^ 40 * 17781 * 2
def baseEnd_17781 : Nat := 1803496201027193176441

theorem tailTrace_17781 : CollatzResearch.WordTrace tailWord_17781 prefixEnd_17781 1803496201027193176441 := by
  unfold tailWord_17781
  simp only [CollatzResearch.WordTrace]
  refine ⟨648526348589948598141197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 432350899059965732094131 648526348589948598141197)
  ·
    refine ⟨243197380721230724302949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 648526348589948598141197 243197380721230724302949)
    ·
      refine ⟨45599508885230760806803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 243197380721230724302949 45599508885230760806803)
      ·
        refine ⟨68399263327846141210205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45599508885230760806803 68399263327846141210205)
        ·
          refine ⟨25649723747942302953827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68399263327846141210205 25649723747942302953827)
          ·
            refine ⟨38474585621913454430741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25649723747942302953827 38474585621913454430741)
            ·
              refine ⟨1803496201027193176441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38474585621913454430741 1803496201027193176441)
              ·
                rfl

theorem cell19_17781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_17781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17781 prefixEnd_17781 := by exact prefixLift 17781
  have htrace : WordTrace (prefixWord ++ tailWord_17781) baseStart_17781 baseEnd_17781 := by
    simpa [prefixWord, tailWord_17781, baseEnd_17781] using wordTrace_append hprefix tailTrace_17781
  have hstable : (prefixWord ++ tailWord_17781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17781).length < 2 ^ (prefixWord ++ tailWord_17781).sum := by decide
  have hdescent : baseEnd_17781 < baseStart_17781 := by decide
  rcases family_descends (prefixWord ++ tailWord_17781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_17916 : List Nat := [2, 2, 2, 1, 2, 1, 5, 4]
def baseStart_17916 : Nat := 118140960795 + 17916 * 2 ^ 59
def prefixEnd_17916 : Nat := 4983230072969 + 3 ^ 40 * 17916 * 2
def baseEnd_17916 : Nat := 5451567055441266528955

theorem tailTrace_17916 : CollatzResearch.WordTrace tailWord_17916 prefixEnd_17916 5451567055441266528955 := by
  unfold tailWord_17916
  simp only [CollatzResearch.WordTrace]
  refine ⟨326725101550433327152801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 435633468733911102870401 326725101550433327152801)
  ·
    refine ⟨245043826162824995364601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 326725101550433327152801 245043826162824995364601)
    ·
      refine ⟨183782869622118746523451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 245043826162824995364601 183782869622118746523451)
      ·
        refine ⟨275674304433178119785177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183782869622118746523451 275674304433178119785177)
        ·
          refine ⟨206755728324883589838883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275674304433178119785177 206755728324883589838883)
          ·
            refine ⟨310133592487325384758325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206755728324883589838883 310133592487325384758325)
            ·
              refine ⟨29075024295686754821093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 310133592487325384758325 29075024295686754821093)
              ·
                refine ⟨5451567055441266528955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29075024295686754821093 5451567055441266528955)
                ·
                  rfl

theorem cell19_17916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_17916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_17916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_17916 prefixEnd_17916 := by exact prefixLift 17916
  have htrace : WordTrace (prefixWord ++ tailWord_17916) baseStart_17916 baseEnd_17916 := by
    simpa [prefixWord, tailWord_17916, baseEnd_17916] using wordTrace_append hprefix tailTrace_17916
  have hstable : (prefixWord ++ tailWord_17916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_17916).length < 2 ^ (prefixWord ++ tailWord_17916).sum := by decide
  have hdescent : baseEnd_17916 < baseStart_17916 := by decide
  rcases family_descends (prefixWord ++ tailWord_17916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18049 : List Nat := [1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_18049 : Nat := 118140960795 + 18049 * 2 ^ 59
def prefixEnd_18049 : Nat := 4983230072969 + 3 ^ 40 * 18049 * 2
def baseEnd_18049 : Nat := 5492036938136365573037

theorem tailTrace_18049 : CollatzResearch.WordTrace tailWord_18049 prefixEnd_18049 5492036938136365573037 := by
  unfold tailWord_18049
  simp only [CollatzResearch.WordTrace]
  refine ⟨658301111619030368897201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 438867407746020245931467 658301111619030368897201)
  ·
    refine ⟨493725833714272776672901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 658301111619030368897201 493725833714272776672901)
    ·
      refine ⟨92573593821426145626169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 493725833714272776672901 92573593821426145626169)
      ·
        refine ⟨69430195366069609219627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92573593821426145626169 69430195366069609219627)
        ·
          refine ⟨104145293049104413829441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69430195366069609219627 104145293049104413829441)
          ·
            refine ⟨78108969786828310372081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104145293049104413829441 78108969786828310372081)
            ·
              refine ⟨58581727340121232779061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78108969786828310372081 58581727340121232779061)
              ·
                refine ⟨5492036938136365573037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58581727340121232779061 5492036938136365573037)
                ·
                  rfl

theorem cell19_18049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_18049 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18049 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18049 prefixEnd_18049 := by exact prefixLift 18049
  have htrace : WordTrace (prefixWord ++ tailWord_18049) baseStart_18049 baseEnd_18049 := by
    simpa [prefixWord, tailWord_18049, baseEnd_18049] using wordTrace_append hprefix tailTrace_18049
  have hstable : (prefixWord ++ tailWord_18049).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18049).length < 2 ^ (prefixWord ++ tailWord_18049).sum := by decide
  have hdescent : baseEnd_18049 < baseStart_18049 := by decide
  rcases family_descends (prefixWord ++ tailWord_18049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18066 : List Nat := [3, 2, 3, 1, 4, 6]
def baseStart_18066 : Nat := 118140960795 + 18066 * 2 ^ 59
def prefixEnd_18066 : Nat := 4983230072969 + 3 ^ 40 * 18066 * 2
def baseEnd_18066 : Nat := 610801086698373688357

theorem tailTrace_18066 : CollatzResearch.WordTrace tailWord_18066 prefixEnd_18066 610801086698373688357 := by
  unfold tailWord_18066
  simp only [CollatzResearch.WordTrace]
  refine ⟨164730288139360568066513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 439280768371628181510701 164730288139360568066513)
  ·
    refine ⟨123547716104520426049885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164730288139360568066513 123547716104520426049885)
    ·
      refine ⟨46330393539195159768707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123547716104520426049885 46330393539195159768707)
      ·
        refine ⟨69495590308792739653061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46330393539195159768707 69495590308792739653061)
        ·
          refine ⟨13030423182898638684949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69495590308792739653061 13030423182898638684949)
          ·
            refine ⟨610801086698373688357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13030423182898638684949 610801086698373688357)
            ·
              rfl

theorem cell19_18066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 6].length) (baseStart_18066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18066 prefixEnd_18066 := by exact prefixLift 18066
  have htrace : WordTrace (prefixWord ++ tailWord_18066) baseStart_18066 baseEnd_18066 := by
    simpa [prefixWord, tailWord_18066, baseEnd_18066] using wordTrace_append hprefix tailTrace_18066
  have hstable : (prefixWord ++ tailWord_18066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18066).length < 2 ^ (prefixWord ++ tailWord_18066).sum := by decide
  have hdescent : baseEnd_18066 < baseStart_18066 := by decide
  rcases family_descends (prefixWord ++ tailWord_18066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18068 : List Nat := [2, 4, 2, 2, 9]
def baseStart_18068 : Nat := 118140960795 + 18068 * 2 ^ 59
def prefixEnd_18068 : Nat := 4983230072969 + 3 ^ 40 * 18068 * 2
def baseEnd_18068 : Nat := 203622901849998190769

theorem tailTrace_18068 : CollatzResearch.WordTrace tailWord_18068 prefixEnd_18068 203622901849998190769 := by
  unfold tailWord_18068
  simp only [CollatzResearch.WordTrace]
  refine ⟨329497049275098306919429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 439329399033464409225905 329497049275098306919429)
  ·
    refine ⟨61780696739080932547393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 329497049275098306919429 61780696739080932547393)
    ·
      refine ⟨46335522554310699410545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61780696739080932547393 46335522554310699410545)
      ·
        refine ⟨34751641915733024557909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46335522554310699410545 34751641915733024557909)
        ·
          refine ⟨203622901849998190769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 34751641915733024557909 203622901849998190769)
          ·
            rfl

theorem cell19_18068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 9].length) (baseStart_18068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18068 prefixEnd_18068 := by exact prefixLift 18068
  have htrace : WordTrace (prefixWord ++ tailWord_18068) baseStart_18068 baseEnd_18068 := by
    simpa [prefixWord, tailWord_18068, baseEnd_18068] using wordTrace_append hprefix tailTrace_18068
  have hstable : (prefixWord ++ tailWord_18068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18068).length < 2 ^ (prefixWord ++ tailWord_18068).sum := by decide
  have hdescent : baseEnd_18068 < baseStart_18068 := by decide
  rcases family_descends (prefixWord ++ tailWord_18068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18161 : List Nat := [1, 2, 2, 2, 2, 5, 2, 3]
def baseStart_18161 : Nat := 118140960795 + 18161 * 2 ^ 59
def prefixEnd_18161 : Nat := 4983230072969 + 3 ^ 40 * 18161 * 2
def baseEnd_18161 : Nat := 5526116839353291083843

theorem tailTrace_18161 : CollatzResearch.WordTrace tailWord_18161 prefixEnd_18161 5526116839353291083843 := by
  unfold tailWord_18161
  simp only [CollatzResearch.WordTrace]
  refine ⟨662386087213273496974337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 441590724808848997982891 662386087213273496974337)
  ·
    refine ⟨496789565409955122730753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 662386087213273496974337 496789565409955122730753)
    ·
      refine ⟨372592174057466342048065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 496789565409955122730753 372592174057466342048065)
      ·
        refine ⟨279444130543099756536049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372592174057466342048065 279444130543099756536049)
        ·
          refine ⟨209583097907324817402037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279444130543099756536049 209583097907324817402037)
          ·
            refine ⟨19648415428811701631441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 209583097907324817402037 19648415428811701631441)
            ·
              refine ⟨14736311571608776223581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19648415428811701631441 14736311571608776223581)
              ·
                refine ⟨5526116839353291083843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14736311571608776223581 5526116839353291083843)
                ·
                  rfl

theorem cell19_18161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 3].length) (baseStart_18161 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18161 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18161 prefixEnd_18161 := by exact prefixLift 18161
  have htrace : WordTrace (prefixWord ++ tailWord_18161) baseStart_18161 baseEnd_18161 := by
    simpa [prefixWord, tailWord_18161, baseEnd_18161] using wordTrace_append hprefix tailTrace_18161
  have hstable : (prefixWord ++ tailWord_18161).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18161).length < 2 ^ (prefixWord ++ tailWord_18161).sum := by decide
  have hdescent : baseEnd_18161 < baseStart_18161 := by decide
  rcases family_descends (prefixWord ++ tailWord_18161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18163 : List Nat := [1, 1, 1, 2, 2, 3, 6, 3]
def baseStart_18163 : Nat := 118140960795 + 18163 * 2 ^ 59
def prefixEnd_18163 : Nat := 4983230072969 + 3 ^ 40 * 18163 * 2
def baseEnd_18163 : Nat := 5526725409017879039393

theorem tailTrace_18163 : CollatzResearch.WordTrace tailWord_18163 prefixEnd_18163 5526725409017879039393 := by
  unfold tailWord_18163
  simp only [CollatzResearch.WordTrace]
  refine ⟨662459033206027838547143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 441639355470685225698095 662459033206027838547143)
  ·
    refine ⟨993688549809041757820715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662459033206027838547143 993688549809041757820715)
    ·
      refine ⟨1490532824713562636731073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993688549809041757820715 1490532824713562636731073)
      ·
        refine ⟨1117899618535171977548305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1490532824713562636731073 1117899618535171977548305)
        ·
          refine ⟨838424713901378983161229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1117899618535171977548305 838424713901378983161229)
          ·
            refine ⟨314409267713017118685461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 838424713901378983161229 314409267713017118685461)
            ·
              refine ⟨14737934424047677438381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 314409267713017118685461 14737934424047677438381)
              ·
                refine ⟨5526725409017879039393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14737934424047677438381 5526725409017879039393)
                ·
                  rfl

theorem cell19_18163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 3].length) (baseStart_18163 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18163 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18163 prefixEnd_18163 := by exact prefixLift 18163
  have htrace : WordTrace (prefixWord ++ tailWord_18163) baseStart_18163 baseEnd_18163 := by
    simpa [prefixWord, tailWord_18163, baseEnd_18163] using wordTrace_append hprefix tailTrace_18163
  have hstable : (prefixWord ++ tailWord_18163).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18163).length < 2 ^ (prefixWord ++ tailWord_18163).sum := by decide
  have hdescent : baseEnd_18163 < baseStart_18163 := by decide
  rcases family_descends (prefixWord ++ tailWord_18163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18239 : List Nat := [1, 1, 2, 2, 7, 6]
def baseStart_18239 : Nat := 118140960795 + 18239 * 2 ^ 59
def prefixEnd_18239 : Nat := 4983230072969 + 3 ^ 40 * 18239 * 2
def baseEnd_18239 : Nat := 616650117363580150033

theorem tailTrace_18239 : CollatzResearch.WordTrace tailWord_18239 prefixEnd_18239 616650117363580150033 := by
  unfold tailWord_18239
  simp only [CollatzResearch.WordTrace]
  refine ⟨665230980930692818313771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 443487320620461878875847 665230980930692818313771)
  ·
    refine ⟨997846471396039227470657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 665230980930692818313771 997846471396039227470657)
    ·
      refine ⟨748384853547029420602993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 997846471396039227470657 748384853547029420602993)
      ·
        refine ⟨561288640160272065452245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 748384853547029420602993 561288640160272065452245)
        ·
          refine ⟨13155202503756376534037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 561288640160272065452245 13155202503756376534037)
          ·
            refine ⟨616650117363580150033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13155202503756376534037 616650117363580150033)
            ·
              rfl

theorem cell19_18239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 6].length) (baseStart_18239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18239 prefixEnd_18239 := by exact prefixLift 18239
  have htrace : WordTrace (prefixWord ++ tailWord_18239) baseStart_18239 baseEnd_18239 := by
    simpa [prefixWord, tailWord_18239, baseEnd_18239] using wordTrace_append hprefix tailTrace_18239
  have hstable : (prefixWord ++ tailWord_18239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18239).length < 2 ^ (prefixWord ++ tailWord_18239).sum := by decide
  have hdescent : baseEnd_18239 < baseStart_18239 := by decide
  rcases family_descends (prefixWord ++ tailWord_18239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18241 : List Nat := [1, 2, 5, 11]
def baseStart_18241 : Nat := 118140960795 + 18241 * 2 ^ 59
def prefixEnd_18241 : Nat := 4983230072969 + 3 ^ 40 * 18241 * 2
def baseEnd_18241 : Nat := 68524192912800114887

theorem tailTrace_18241 : CollatzResearch.WordTrace tailWord_18241 prefixEnd_18241 68524192912800114887 := by
  unfold tailWord_18241
  simp only [CollatzResearch.WordTrace]
  refine ⟨665303926923447159886577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 443535951282298106591051 665303926923447159886577)
  ·
    refine ⟨498977945192585369914933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 665303926923447159886577 498977945192585369914933)
    ·
      refine ⟨46779182361804878429525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 498977945192585369914933 46779182361804878429525)
      ·
        refine ⟨68524192912800114887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 46779182361804878429525 68524192912800114887)
        ·
          rfl

theorem cell19_18241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 11].length) (baseStart_18241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18241 prefixEnd_18241 := by exact prefixLift 18241
  have htrace : WordTrace (prefixWord ++ tailWord_18241) baseStart_18241 baseEnd_18241 := by
    simpa [prefixWord, tailWord_18241, baseEnd_18241] using wordTrace_append hprefix tailTrace_18241
  have hstable : (prefixWord ++ tailWord_18241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18241).length < 2 ^ (prefixWord ++ tailWord_18241).sum := by decide
  have hdescent : baseEnd_18241 < baseStart_18241 := by decide
  rcases family_descends (prefixWord ++ tailWord_18241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18258 : List Nat := [3, 2, 2, 1, 1, 3, 3, 4]
def baseStart_18258 : Nat := 118140960795 + 18258 * 2 ^ 59
def prefixEnd_18258 : Nat := 4983230072969 + 3 ^ 40 * 18258 * 2
def baseEnd_18258 : Nat := 5555632468085806928023

theorem tailTrace_18258 : CollatzResearch.WordTrace tailWord_18258 prefixEnd_18258 5555632468085806928023 := by
  unfold tailWord_18258
  simp only [CollatzResearch.WordTrace]
  refine ⟨166480991965464765813857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 443949311907906042170285 166480991965464765813857)
  ·
    refine ⟨124860743974098574360393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166480991965464765813857 124860743974098574360393)
    ·
      refine ⟨93645557980573930770295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124860743974098574360393 93645557980573930770295)
      ·
        refine ⟨140468336970860896155443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93645557980573930770295 140468336970860896155443)
        ·
          refine ⟨210702505456291344233165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140468336970860896155443 210702505456291344233165)
          ·
            refine ⟨79013439546109254087437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210702505456291344233165 79013439546109254087437)
            ·
              refine ⟨29630039829790970282789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79013439546109254087437 29630039829790970282789)
              ·
                refine ⟨5555632468085806928023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29630039829790970282789 5555632468085806928023)
                ·
                  rfl

theorem cell19_18258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_18258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18258 prefixEnd_18258 := by exact prefixLift 18258
  have htrace : WordTrace (prefixWord ++ tailWord_18258) baseStart_18258 baseEnd_18258 := by
    simpa [prefixWord, tailWord_18258, baseEnd_18258] using wordTrace_append hprefix tailTrace_18258
  have hstable : (prefixWord ++ tailWord_18258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18258).length < 2 ^ (prefixWord ++ tailWord_18258).sum := by decide
  have hdescent : baseEnd_18258 < baseStart_18258 := by decide
  rcases family_descends (prefixWord ++ tailWord_18258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18275 : List Nat := [1, 1, 1, 5, 4, 1, 3, 3]
def baseStart_18275 : Nat := 118140960795 + 18275 * 2 ^ 59
def prefixEnd_18275 : Nat := 4983230072969 + 3 ^ 40 * 18275 * 2
def baseEnd_18275 : Nat := 5560805310234804550199

theorem tailTrace_18275 : CollatzResearch.WordTrace tailWord_18275 prefixEnd_18275 5560805310234804550199 := by
  unfold tailWord_18275
  simp only [CollatzResearch.WordTrace]
  refine ⟨666544008800270966624279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 444362672533513977749519 666544008800270966624279)
  ·
    refine ⟨999816013200406449936419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 666544008800270966624279 999816013200406449936419)
    ·
      refine ⟨1499724019800609674904629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 999816013200406449936419 1499724019800609674904629)
      ·
        refine ⟨140599126856307157022309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1499724019800609674904629 140599126856307157022309)
        ·
          refine ⟨26362336285557591941683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140599126856307157022309 26362336285557591941683)
          ·
            refine ⟨39543504428336387912525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26362336285557591941683 39543504428336387912525)
            ·
              refine ⟨14828814160626145467197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39543504428336387912525 14828814160626145467197)
              ·
                refine ⟨5560805310234804550199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14828814160626145467197 5560805310234804550199)
                ·
                  rfl

theorem cell19_18275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 3].length) (baseStart_18275 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18275 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18275 prefixEnd_18275 := by exact prefixLift 18275
  have htrace : WordTrace (prefixWord ++ tailWord_18275) baseStart_18275 baseEnd_18275 := by
    simpa [prefixWord, tailWord_18275, baseEnd_18275] using wordTrace_append hprefix tailTrace_18275
  have hstable : (prefixWord ++ tailWord_18275).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18275).length < 2 ^ (prefixWord ++ tailWord_18275).sum := by decide
  have hdescent : baseEnd_18275 < baseStart_18275 := by decide
  rcases family_descends (prefixWord ++ tailWord_18275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18294 : List Nat := [5, 1, 1, 3, 2, 1, 6]
def baseStart_18294 : Nat := 118140960795 + 18294 * 2 ^ 59
def prefixEnd_18294 : Nat := 4983230072969 + 3 ^ 40 * 18294 * 2
def baseEnd_18294 : Nat := 1855528907349463375975

theorem tailTrace_18294 : CollatzResearch.WordTrace tailWord_18294 prefixEnd_18294 1855528907349463375975 := by
  unfold tailWord_18294
  simp only [CollatzResearch.WordTrace]
  refine ⟨41702312233214825722871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 444824663820958141043957 41702312233214825722871)
  ·
    refine ⟨62553468349822238584307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41702312233214825722871 62553468349822238584307)
    ·
      refine ⟨93830202524733357876461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62553468349822238584307 93830202524733357876461)
      ·
        refine ⟨35186325946775009203673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93830202524733357876461 35186325946775009203673)
        ·
          refine ⟨26389744460081256902755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35186325946775009203673 26389744460081256902755)
          ·
            refine ⟨39584616690121885354133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26389744460081256902755 39584616690121885354133)
            ·
              refine ⟨1855528907349463375975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39584616690121885354133 1855528907349463375975)
              ·
                rfl

theorem cell19_18294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_18294 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18294 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18294 prefixEnd_18294 := by exact prefixLift 18294
  have htrace : WordTrace (prefixWord ++ tailWord_18294) baseStart_18294 baseEnd_18294 := by
    simpa [prefixWord, tailWord_18294, baseEnd_18294] using wordTrace_append hprefix tailTrace_18294
  have hstable : (prefixWord ++ tailWord_18294).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18294).length < 2 ^ (prefixWord ++ tailWord_18294).sum := by decide
  have hdescent : baseEnd_18294 < baseStart_18294 := by decide
  rcases family_descends (prefixWord ++ tailWord_18294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18326 : List Nat := [5, 3, 1, 1, 2, 2, 2, 3]
def baseStart_18326 : Nat := 118140960795 + 18326 * 2 ^ 59
def prefixEnd_18326 : Nat := 4983230072969 + 3 ^ 40 * 18326 * 2
def baseEnd_18326 : Nat := 5576323836681797416727

theorem tailTrace_18326 : CollatzResearch.WordTrace tailWord_18326 prefixEnd_18326 5576323836681797416727 := by
  unfold tailWord_18326
  simp only [CollatzResearch.WordTrace]
  refine ⟨41775258225969167295677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 445602754410337784487221 41775258225969167295677)
  ·
    refine ⟨15665721834738437735879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41775258225969167295677 15665721834738437735879)
    ·
      refine ⟨23498582752107656603819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15665721834738437735879 23498582752107656603819)
      ·
        refine ⟨35247874128161484905729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23498582752107656603819 35247874128161484905729)
        ·
          refine ⟨26435905596121113679297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35247874128161484905729 26435905596121113679297)
          ·
            refine ⟨19826929197090835259473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26435905596121113679297 19826929197090835259473)
            ·
              refine ⟨14870196897818126444605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19826929197090835259473 14870196897818126444605)
              ·
                refine ⟨5576323836681797416727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14870196897818126444605 5576323836681797416727)
                ·
                  rfl

theorem cell19_18326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_18326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18326 prefixEnd_18326 := by exact prefixLift 18326
  have htrace : WordTrace (prefixWord ++ tailWord_18326) baseStart_18326 baseEnd_18326 := by
    simpa [prefixWord, tailWord_18326, baseEnd_18326] using wordTrace_append hprefix tailTrace_18326
  have hstable : (prefixWord ++ tailWord_18326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18326).length < 2 ^ (prefixWord ++ tailWord_18326).sum := by decide
  have hdescent : baseEnd_18326 < baseStart_18326 := by decide
  rcases family_descends (prefixWord ++ tailWord_18326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18328 : List Nat := [2, 1, 2, 6, 2, 1, 2, 3]
def baseStart_18328 : Nat := 118140960795 + 18328 * 2 ^ 59
def prefixEnd_18328 : Nat := 4983230072969 + 3 ^ 40 * 18328 * 2
def baseEnd_18328 : Nat := 5576932406346385372277

theorem tailTrace_18328 : CollatzResearch.WordTrace tailWord_18328 prefixEnd_18328 5576932406346385372277 := by
  unfold tailWord_18328
  simp only [CollatzResearch.WordTrace]
  refine ⟨334238538804130509151819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 445651385072174012202425 334238538804130509151819)
  ·
    refine ⟨501357808206195763727729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 334238538804130509151819 501357808206195763727729)
    ·
      refine ⟨376018356154646822795797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 501357808206195763727729 376018356154646822795797)
      ·
        refine ⟨17625860444749069818553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 376018356154646822795797 17625860444749069818553)
        ·
          refine ⟨13219395333561802363915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17625860444749069818553 13219395333561802363915)
          ·
            refine ⟨19829093000342703545873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13219395333561802363915 19829093000342703545873)
            ·
              refine ⟨14871819750257027659405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19829093000342703545873 14871819750257027659405)
              ·
                refine ⟨5576932406346385372277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14871819750257027659405 5576932406346385372277)
                ·
                  rfl

theorem cell19_18328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_18328 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18328 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18328 prefixEnd_18328 := by exact prefixLift 18328
  have htrace : WordTrace (prefixWord ++ tailWord_18328) baseStart_18328 baseEnd_18328 := by
    simpa [prefixWord, tailWord_18328, baseEnd_18328] using wordTrace_append hprefix tailTrace_18328
  have hstable : (prefixWord ++ tailWord_18328).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18328).length < 2 ^ (prefixWord ++ tailWord_18328).sum := by decide
  have hdescent : baseEnd_18328 < baseStart_18328 := by decide
  rcases family_descends (prefixWord ++ tailWord_18328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18332 : List Nat := [2, 2, 3, 3, 1, 1, 4, 3]
def baseStart_18332 : Nat := 118140960795 + 18332 * 2 ^ 59
def prefixEnd_18332 : Nat := 4983230072969 + 3 ^ 40 * 18332 * 2
def baseEnd_18332 : Nat := 5578149545675561283377

theorem tailTrace_18332 : CollatzResearch.WordTrace tailWord_18332 prefixEnd_18332 5578149545675561283377 := by
  unfold tailWord_18332
  simp only [CollatzResearch.WordTrace]
  refine ⟨334311484796884850724625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 445748646395846467632833 334311484796884850724625)
  ·
    refine ⟨250733613597663638043469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 334311484796884850724625 250733613597663638043469)
    ·
      refine ⟨94025105099123864266301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 250733613597663638043469 94025105099123864266301)
      ·
        refine ⟨35259414412171449099863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94025105099123864266301 35259414412171449099863)
        ·
          refine ⟨52889121618257173649795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35259414412171449099863 52889121618257173649795)
          ·
            refine ⟨79333682427385760474693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52889121618257173649795 79333682427385760474693)
            ·
              refine ⟨14875065455134830089005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79333682427385760474693 14875065455134830089005)
              ·
                refine ⟨5578149545675561283377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14875065455134830089005 5578149545675561283377)
                ·
                  rfl

theorem cell19_18332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_18332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18332 prefixEnd_18332 := by exact prefixLift 18332
  have htrace : WordTrace (prefixWord ++ tailWord_18332) baseStart_18332 baseEnd_18332 := by
    simpa [prefixWord, tailWord_18332, baseEnd_18332] using wordTrace_append hprefix tailTrace_18332
  have hstable : (prefixWord ++ tailWord_18332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18332).length < 2 ^ (prefixWord ++ tailWord_18332).sum := by decide
  have hdescent : baseEnd_18332 < baseStart_18332 := by decide
  rcases family_descends (prefixWord ++ tailWord_18332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18353 : List Nat := [1, 2, 2, 4, 2, 3, 5]
def baseStart_18353 : Nat := 118140960795 + 18353 * 2 ^ 59
def prefixEnd_18353 : Nat := 4983230072969 + 3 ^ 40 * 18353 * 2
def baseEnd_18353 : Nat := 1861513175717911605551

theorem tailTrace_18353 : CollatzResearch.WordTrace tailWord_18353 prefixEnd_18353 1861513175717911605551 := by
  unfold tailWord_18353
  simp only [CollatzResearch.WordTrace]
  refine ⟨669388902517690287963713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 446259268345126858642475 669388902517690287963713)
  ·
    refine ⟨502041676888267715972785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 669388902517690287963713 502041676888267715972785)
    ·
      refine ⟨376531257666200786979589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 502041676888267715972785 376531257666200786979589)
      ·
        refine ⟨70599610812412647558673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 376531257666200786979589 70599610812412647558673)
        ·
          refine ⟨52949708109309485669005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70599610812412647558673 52949708109309485669005)
          ·
            refine ⟨19856140540991057125877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52949708109309485669005 19856140540991057125877)
            ·
              refine ⟨1861513175717911605551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19856140540991057125877 1861513175717911605551)
              ·
                rfl

theorem cell19_18353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 5].length) (baseStart_18353 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18353 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18353 prefixEnd_18353 := by exact prefixLift 18353
  have htrace : WordTrace (prefixWord ++ tailWord_18353) baseStart_18353 baseEnd_18353 := by
    simpa [prefixWord, tailWord_18353, baseEnd_18353] using wordTrace_append hprefix tailTrace_18353
  have hstable : (prefixWord ++ tailWord_18353).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18353).length < 2 ^ (prefixWord ++ tailWord_18353).sum := by decide
  have hdescent : baseEnd_18353 < baseStart_18353 := by decide
  rcases family_descends (prefixWord ++ tailWord_18353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18469 : List Nat := [1, 3, 1, 2, 2, 4, 6]
def baseStart_18469 : Nat := 118140960795 + 18469 * 2 ^ 59
def prefixEnd_18469 : Nat := 4983230072969 + 3 ^ 40 * 18469 * 2
def baseEnd_18469 : Nat := 1873278855899945412853

theorem tailTrace_18469 : CollatzResearch.WordTrace tailWord_18469 prefixEnd_18469 1873278855899945412853 := by
  unfold tailWord_18469
  simp only [CollatzResearch.WordTrace]
  refine ⟨673619770097442099186461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 449079846731628066124307 673619770097442099186461)
  ·
    refine ⟨252607413786540787194923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 673619770097442099186461 252607413786540787194923)
    ·
      refine ⟨378911120679811180792385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252607413786540787194923 378911120679811180792385)
      ·
        refine ⟨284183340509858385594289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378911120679811180792385 284183340509858385594289)
        ·
          refine ⟨213137505382393789195717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284183340509858385594289 213137505382393789195717)
          ·
            refine ⟨39963282259198835474197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213137505382393789195717 39963282259198835474197)
            ·
              refine ⟨1873278855899945412853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39963282259198835474197 1873278855899945412853)
              ·
                rfl

theorem cell19_18469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 6].length) (baseStart_18469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18469 prefixEnd_18469 := by exact prefixLift 18469
  have htrace : WordTrace (prefixWord ++ tailWord_18469) baseStart_18469 baseEnd_18469 := by
    simpa [prefixWord, tailWord_18469, baseEnd_18469] using wordTrace_append hprefix tailTrace_18469
  have hstable : (prefixWord ++ tailWord_18469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18469).length < 2 ^ (prefixWord ++ tailWord_18469).sum := by decide
  have hdescent : baseEnd_18469 < baseStart_18469 := by decide
  rcases family_descends (prefixWord ++ tailWord_18469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18486 : List Nat := [5, 1, 2, 1, 1, 1, 2, 6]
def baseStart_18486 : Nat := 118140960795 + 18486 * 2 ^ 59
def prefixEnd_18486 : Nat := 4983230072969 + 3 ^ 40 * 18486 * 2
def baseEnd_18486 : Nat := 5625009409848833860735

theorem tailTrace_18486 : CollatzResearch.WordTrace tailWord_18486 prefixEnd_18486 5625009409848833860735 := by
  unfold tailWord_18486
  simp only [CollatzResearch.WordTrace]
  refine ⟨42139988189740875159707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 449493207357236001703541 42139988189740875159707)
  ·
    refine ⟨63209982284611312739561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42139988189740875159707 63209982284611312739561)
    ·
      refine ⟨47407486713458484554671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63209982284611312739561 47407486713458484554671)
      ·
        refine ⟨71111230070187726832007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47407486713458484554671 71111230070187726832007)
        ·
          refine ⟨106666845105281590248011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71111230070187726832007 106666845105281590248011)
          ·
            refine ⟨160000267657922385372017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106666845105281590248011 160000267657922385372017)
            ·
              refine ⟨120000200743441789029013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160000267657922385372017 120000200743441789029013)
              ·
                refine ⟨5625009409848833860735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120000200743441789029013 5625009409848833860735)
                ·
                  rfl

theorem cell19_18486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_18486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18486 prefixEnd_18486 := by exact prefixLift 18486
  have htrace : WordTrace (prefixWord ++ tailWord_18486) baseStart_18486 baseEnd_18486 := by
    simpa [prefixWord, tailWord_18486, baseEnd_18486] using wordTrace_append hprefix tailTrace_18486
  have hstable : (prefixWord ++ tailWord_18486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18486).length < 2 ^ (prefixWord ++ tailWord_18486).sum := by decide
  have hdescent : baseEnd_18486 < baseStart_18486 := by decide
  rcases family_descends (prefixWord ++ tailWord_18486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18524 : List Nat := [2, 2, 4, 1, 1, 4, 5]
def baseStart_18524 : Nat := 118140960795 + 18524 * 2 ^ 59
def prefixEnd_18524 : Nat := 4983230072969 + 3 ^ 40 * 18524 * 2
def baseEnd_18524 : Nat := 1878857411158668338729

theorem tailTrace_18524 : CollatzResearch.WordTrace tailWord_18524 prefixEnd_18524 1878857411158668338729 := by
  unfold tailWord_18524
  simp only [CollatzResearch.WordTrace]
  refine ⟨337812892449093246219313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 450417189932124328292417 337812892449093246219313)
  ·
    refine ⟨253359669336819934664485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 337812892449093246219313 253359669336819934664485)
    ·
      refine ⟨47504938000653737749591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 253359669336819934664485 47504938000653737749591)
      ·
        refine ⟨71257407000980606624387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47504938000653737749591 71257407000980606624387)
        ·
          refine ⟨106886110501470909936581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71257407000980606624387 106886110501470909936581)
          ·
            refine ⟨20041145719025795613109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106886110501470909936581 20041145719025795613109)
            ·
              refine ⟨1878857411158668338729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20041145719025795613109 1878857411158668338729)
              ·
                rfl

theorem cell19_18524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_18524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18524 prefixEnd_18524 := by exact prefixLift 18524
  have htrace : WordTrace (prefixWord ++ tailWord_18524) baseStart_18524 baseEnd_18524 := by
    simpa [prefixWord, tailWord_18524, baseEnd_18524] using wordTrace_append hprefix tailTrace_18524
  have hstable : (prefixWord ++ tailWord_18524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18524).length < 2 ^ (prefixWord ++ tailWord_18524).sum := by decide
  have hdescent : baseEnd_18524 < baseStart_18524 := by decide
  rcases family_descends (prefixWord ++ tailWord_18524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18545 : List Nat := [1, 2, 2, 2, 1, 1, 6, 4]
def baseStart_18545 : Nat := 118140960795 + 18545 * 2 ^ 59
def prefixEnd_18545 : Nat := 4983230072969 + 3 ^ 40 * 18545 * 2
def baseEnd_18545 : Nat := 5642962214954178549463

theorem tailTrace_18545 : CollatzResearch.WordTrace tailWord_18545 prefixEnd_18545 5642962214954178549463 := by
  unfold tailWord_18545
  simp only [CollatzResearch.WordTrace]
  refine ⟨676391717822107078953089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 450927811881404719302059 676391717822107078953089)
  ·
    refine ⟨507293788366580309214817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 676391717822107078953089 507293788366580309214817)
    ·
      refine ⟨380470341274935231911113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 507293788366580309214817 380470341274935231911113)
      ·
        refine ⟨285352755956201423933335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380470341274935231911113 285352755956201423933335)
        ·
          refine ⟨428029133934302135900003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285352755956201423933335 428029133934302135900003)
          ·
            refine ⟨642043700901453203850005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428029133934302135900003 642043700901453203850005)
            ·
              refine ⟨30095798479755618930469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 642043700901453203850005 30095798479755618930469)
              ·
                refine ⟨5642962214954178549463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30095798479755618930469 5642962214954178549463)
                ·
                  rfl

theorem cell19_18545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_18545 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18545 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18545 prefixEnd_18545 := by exact prefixLift 18545
  have htrace : WordTrace (prefixWord ++ tailWord_18545) baseStart_18545 baseEnd_18545 := by
    simpa [prefixWord, tailWord_18545, baseEnd_18545] using wordTrace_append hprefix tailTrace_18545
  have hstable : (prefixWord ++ tailWord_18545).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18545).length < 2 ^ (prefixWord ++ tailWord_18545).sum := by decide
  have hdescent : baseEnd_18545 < baseStart_18545 := by decide
  rcases family_descends (prefixWord ++ tailWord_18545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18564 : List Nat := [2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_18564 : Nat := 118140960795 + 18564 * 2 ^ 59
def prefixEnd_18564 : Nat := 4983230072969 + 3 ^ 40 * 18564 * 2
def baseEnd_18564 : Nat := 5648743626767764127189

theorem tailTrace_18564 : CollatzResearch.WordTrace tailWord_18564 prefixEnd_18564 5648743626767764127189 := by
  unfold tailWord_18564
  simp only [CollatzResearch.WordTrace]
  refine ⟨338542352376636661947373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 451389803168848882596497 338542352376636661947373)
  ·
    refine ⟨126953382141238748230265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 338542352376636661947373 126953382141238748230265)
    ·
      refine ⟨95215036605929061172699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126953382141238748230265 95215036605929061172699)
      ·
        refine ⟨142822554908893591759049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95215036605929061172699 142822554908893591759049)
        ·
          refine ⟨107116916181670193819287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142822554908893591759049 107116916181670193819287)
          ·
            refine ⟨160675374272505290728931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107116916181670193819287 160675374272505290728931)
            ·
              refine ⟨241013061408757936093397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160675374272505290728931 241013061408757936093397)
              ·
                refine ⟨5648743626767764127189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 241013061408757936093397 5648743626767764127189)
                ·
                  rfl

theorem cell19_18564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_18564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18564 prefixEnd_18564 := by exact prefixLift 18564
  have htrace : WordTrace (prefixWord ++ tailWord_18564) baseStart_18564 baseEnd_18564 := by
    simpa [prefixWord, tailWord_18564, baseEnd_18564] using wordTrace_append hprefix tailTrace_18564
  have hstable : (prefixWord ++ tailWord_18564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18564).length < 2 ^ (prefixWord ++ tailWord_18564).sum := by decide
  have hdescent : baseEnd_18564 < baseStart_18564 := by decide
  rcases family_descends (prefixWord ++ tailWord_18564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18583 : List Nat := [1, 1, 3, 3, 4, 7]
def baseStart_18583 : Nat := 118140960795 + 18583 * 2 ^ 59
def prefixEnd_18583 : Nat := 4983230072969 + 3 ^ 40 * 18583 * 2
def baseEnd_18583 : Nat := 628280559842372189435

theorem tailTrace_18583 : CollatzResearch.WordTrace tailWord_18583 prefixEnd_18583 628280559842372189435 := by
  unfold tailWord_18583
  simp only [CollatzResearch.WordTrace]
  refine ⟨677777691684439568836403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 451851794456293045890935 677777691684439568836403)
  ·
    refine ⟨1016666537526659353254605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 677777691684439568836403 1016666537526659353254605)
    ·
      refine ⟨381249951572497257470477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1016666537526659353254605 381249951572497257470477)
      ·
        refine ⟨142968731839686471551429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 381249951572497257470477 142968731839686471551429)
        ·
          refine ⟨26806637219941213415893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142968731839686471551429 26806637219941213415893)
          ·
            refine ⟨628280559842372189435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 26806637219941213415893 628280559842372189435)
            ·
              rfl

theorem cell19_18583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 7].length) (baseStart_18583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18583 prefixEnd_18583 := by exact prefixLift 18583
  have htrace : WordTrace (prefixWord ++ tailWord_18583) baseStart_18583 baseEnd_18583 := by
    simpa [prefixWord, tailWord_18583, baseEnd_18583] using wordTrace_append hprefix tailTrace_18583
  have hstable : (prefixWord ++ tailWord_18583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18583).length < 2 ^ (prefixWord ++ tailWord_18583).sum := by decide
  have hdescent : baseEnd_18583 < baseStart_18583 := by decide
  rcases family_descends (prefixWord ++ tailWord_18583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18674 : List Nat := [3, 2, 1, 3, 2, 3, 2, 3]
def baseStart_18674 : Nat := 118140960795 + 18674 * 2 ^ 59
def prefixEnd_18674 : Nat := 4983230072969 + 3 ^ 40 * 18674 * 2
def baseEnd_18674 : Nat := 5682214958320101682445

theorem tailTrace_18674 : CollatzResearch.WordTrace tailWord_18674 prefixEnd_18674 5682214958320101682445 := by
  unfold tailWord_18674
  simp only [CollatzResearch.WordTrace]
  refine ⟨170274183588690527599769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 454064489569841406932717 170274183588690527599769)
  ·
    refine ⟨127705637691517895699827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170274183588690527599769 127705637691517895699827)
    ·
      refine ⟨191558456537276843549741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127705637691517895699827 191558456537276843549741)
      ·
        refine ⟨71834421201478816331153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191558456537276843549741 71834421201478816331153)
        ·
          refine ⟨53875815901109112248365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71834421201478816331153 53875815901109112248365)
          ·
            refine ⟨20203430962915917093137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53875815901109112248365 20203430962915917093137)
            ·
              refine ⟨15152573222186937819853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20203430962915917093137 15152573222186937819853)
              ·
                refine ⟨5682214958320101682445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15152573222186937819853 5682214958320101682445)
                ·
                  rfl

theorem cell19_18674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_18674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18674 prefixEnd_18674 := by exact prefixLift 18674
  have htrace : WordTrace (prefixWord ++ tailWord_18674) baseStart_18674 baseEnd_18674 := by
    simpa [prefixWord, tailWord_18674, baseEnd_18674] using wordTrace_append hprefix tailTrace_18674
  have hstable : (prefixWord ++ tailWord_18674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18674).length < 2 ^ (prefixWord ++ tailWord_18674).sum := by decide
  have hdescent : baseEnd_18674 < baseStart_18674 := by decide
  rcases family_descends (prefixWord ++ tailWord_18674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18697 : List Nat := [1, 2, 1, 1, 3, 6, 5]
def baseStart_18697 : Nat := 118140960795 + 18697 * 2 ^ 59
def prefixEnd_18697 : Nat := 4983230072969 + 3 ^ 40 * 18697 * 2
def baseEnd_18697 : Nat := 1896404503154287723757

theorem tailTrace_18697 : CollatzResearch.WordTrace tailWord_18697 prefixEnd_18697 1896404503154287723757 := by
  unfold tailWord_18697
  simp only [CollatzResearch.WordTrace]
  refine ⟨681935613271437038486345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 454623742180958025657563 681935613271437038486345)
  ·
    refine ⟨511451709953577778864759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 681935613271437038486345 511451709953577778864759)
    ·
      refine ⟨767177564930366668297139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511451709953577778864759 767177564930366668297139)
      ·
        refine ⟨1150766347395550002445709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767177564930366668297139 1150766347395550002445709)
        ·
          refine ⟨431537380273331250917141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1150766347395550002445709 431537380273331250917141)
          ·
            refine ⟨20228314700312402386741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 431537380273331250917141 20228314700312402386741)
            ·
              refine ⟨1896404503154287723757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20228314700312402386741 1896404503154287723757)
              ·
                rfl

theorem cell19_18697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_18697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18697 prefixEnd_18697 := by exact prefixLift 18697
  have htrace : WordTrace (prefixWord ++ tailWord_18697) baseStart_18697 baseEnd_18697 := by
    simpa [prefixWord, tailWord_18697, baseEnd_18697] using wordTrace_append hprefix tailTrace_18697
  have hstable : (prefixWord ++ tailWord_18697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18697).length < 2 ^ (prefixWord ++ tailWord_18697).sum := by decide
  have hdescent : baseEnd_18697 < baseStart_18697 := by decide
  rcases family_descends (prefixWord ++ tailWord_18697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18714 : List Nat := [3, 1, 1, 3, 4, 1, 2, 4]
def baseStart_18714 : Nat := 118140960795 + 18714 * 2 ^ 59
def prefixEnd_18714 : Nat := 4983230072969 + 3 ^ 40 * 18714 * 2
def baseEnd_18714 : Nat := 5694386351611860793447

theorem tailTrace_18714 : CollatzResearch.WordTrace tailWord_18714 prefixEnd_18714 5694386351611860793447 := by
  unfold tailWord_18714
  simp only [CollatzResearch.WordTrace]
  refine ⟨170638913552462235463799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 455037102806565961236797 170638913552462235463799)
  ·
    refine ⟨255958370328693353195699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170638913552462235463799 255958370328693353195699)
    ·
      refine ⟨383937555493040029793549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255958370328693353195699 383937555493040029793549)
      ·
        refine ⟨143976583309890011172581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 383937555493040029793549 143976583309890011172581)
        ·
          refine ⟨26995609370604377094859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143976583309890011172581 26995609370604377094859)
          ·
            refine ⟨40493414055906565642289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26995609370604377094859 40493414055906565642289)
            ·
              refine ⟨30370060541929924231717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40493414055906565642289 30370060541929924231717)
              ·
                refine ⟨5694386351611860793447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30370060541929924231717 5694386351611860793447)
                ·
                  rfl

theorem cell19_18714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_18714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18714 prefixEnd_18714 := by exact prefixLift 18714
  have htrace : WordTrace (prefixWord ++ tailWord_18714) baseStart_18714 baseEnd_18714 := by
    simpa [prefixWord, tailWord_18714, baseEnd_18714] using wordTrace_append hprefix tailTrace_18714
  have hstable : (prefixWord ++ tailWord_18714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18714).length < 2 ^ (prefixWord ++ tailWord_18714).sum := by decide
  have hdescent : baseEnd_18714 < baseStart_18714 := by decide
  rcases family_descends (prefixWord ++ tailWord_18714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18782 : List Nat := [4, 4, 2, 1, 1, 1, 3, 3]
def baseStart_18782 : Nat := 118140960795 + 18782 * 2 ^ 59
def prefixEnd_18782 : Nat := 4983230072969 + 3 ^ 40 * 18782 * 2
def baseEnd_18782 : Nat := 5715077720207851282151

theorem tailTrace_18782 : CollatzResearch.WordTrace tailWord_18782 prefixEnd_18782 5715077720207851282151 := by
  unfold tailWord_18782
  simp only [CollatzResearch.WordTrace]
  refine ⟨85629477245437069416325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 456690545308997703553733 85629477245437069416325)
  ·
    refine ⟨16055526983519450515561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85629477245437069416325 16055526983519450515561)
    ·
      refine ⟨12041645237639587886671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16055526983519450515561 12041645237639587886671)
      ·
        refine ⟨18062467856459381830007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12041645237639587886671 18062467856459381830007)
        ·
          refine ⟨27093701784689072745011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18062467856459381830007 27093701784689072745011)
          ·
            refine ⟨40640552677033609117517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27093701784689072745011 40640552677033609117517)
            ·
              refine ⟨15240207253887603419069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40640552677033609117517 15240207253887603419069)
              ·
                refine ⟨5715077720207851282151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15240207253887603419069 5715077720207851282151)
                ·
                  rfl

theorem cell19_18782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_18782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18782 prefixEnd_18782 := by exact prefixLift 18782
  have htrace : WordTrace (prefixWord ++ tailWord_18782) baseStart_18782 baseEnd_18782 := by
    simpa [prefixWord, tailWord_18782, baseEnd_18782] using wordTrace_append hprefix tailTrace_18782
  have hstable : (prefixWord ++ tailWord_18782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18782).length < 2 ^ (prefixWord ++ tailWord_18782).sum := by decide
  have hdescent : baseEnd_18782 < baseStart_18782 := by decide
  rcases family_descends (prefixWord ++ tailWord_18782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18845 : List Nat := [1, 4, 2, 1, 4, 2, 2, 3]
def baseStart_18845 : Nat := 118140960795 + 18845 * 2 ^ 59
def prefixEnd_18845 : Nat := 4983230072969 + 3 ^ 40 * 18845 * 2
def baseEnd_18845 : Nat := 5734247664642371881979

theorem tailTrace_18845 : CollatzResearch.WordTrace tailWord_18845 prefixEnd_18845 5734247664642371881979 := by
  unfold tailWord_18845
  simp only [CollatzResearch.WordTrace]
  refine ⟨687333616735258314873989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 458222411156838876582659 687333616735258314873989)
  ·
    refine ⟨128875053137860934038873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 687333616735258314873989 128875053137860934038873)
    ·
      refine ⟨96656289853395700529155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128875053137860934038873 96656289853395700529155)
      ·
        refine ⟨144984434780093550793733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96656289853395700529155 144984434780093550793733)
        ·
          refine ⟨27184581521267540773825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144984434780093550793733 27184581521267540773825)
          ·
            refine ⟨20388436140950655580369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27184581521267540773825 20388436140950655580369)
            ·
              refine ⟨15291327105712991685277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20388436140950655580369 15291327105712991685277)
              ·
                refine ⟨5734247664642371881979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15291327105712991685277 5734247664642371881979)
                ·
                  rfl

theorem cell19_18845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 3].length) (baseStart_18845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18845 prefixEnd_18845 := by exact prefixLift 18845
  have htrace : WordTrace (prefixWord ++ tailWord_18845) baseStart_18845 baseEnd_18845 := by
    simpa [prefixWord, tailWord_18845, baseEnd_18845] using wordTrace_append hprefix tailTrace_18845
  have hstable : (prefixWord ++ tailWord_18845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18845).length < 2 ^ (prefixWord ++ tailWord_18845).sum := by decide
  have hdescent : baseEnd_18845 < baseStart_18845 := by decide
  rcases family_descends (prefixWord ++ tailWord_18845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18881 : List Nat := [1, 2, 7, 1, 1, 1, 2, 4]
def baseStart_18881 : Nat := 118140960795 + 18881 * 2 ^ 59
def prefixEnd_18881 : Nat := 4983230072969 + 3 ^ 40 * 18881 * 2
def baseEnd_18881 : Nat := 5745201918604955081881

theorem tailTrace_18881 : CollatzResearch.WordTrace tailWord_18881 prefixEnd_18881 5745201918604955081881 := by
  unfold tailWord_18881
  simp only [CollatzResearch.WordTrace]
  refine ⟨688646644604836463184497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 459097763069890975456331 688646644604836463184497)
  ·
    refine ⟨516484983453627347388373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 688646644604836463184497 516484983453627347388373)
    ·
      refine ⟨12105116799694390954415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 516484983453627347388373 12105116799694390954415)
      ·
        refine ⟨18157675199541586431623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12105116799694390954415 18157675199541586431623)
        ·
          refine ⟨27236512799312379647435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18157675199541586431623 27236512799312379647435)
          ·
            refine ⟨40854769198968569471153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27236512799312379647435 40854769198968569471153)
            ·
              refine ⟨30641076899226427103365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40854769198968569471153 30641076899226427103365)
              ·
                refine ⟨5745201918604955081881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30641076899226427103365 5745201918604955081881)
                ·
                  rfl

theorem cell19_18881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 4].length) (baseStart_18881 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18881 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18881 prefixEnd_18881 := by exact prefixLift 18881
  have htrace : WordTrace (prefixWord ++ tailWord_18881) baseStart_18881 baseEnd_18881 := by
    simpa [prefixWord, tailWord_18881, baseEnd_18881] using wordTrace_append hprefix tailTrace_18881
  have hstable : (prefixWord ++ tailWord_18881).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18881).length < 2 ^ (prefixWord ++ tailWord_18881).sum := by decide
  have hdescent : baseEnd_18881 < baseStart_18881 := by decide
  rcases family_descends (prefixWord ++ tailWord_18881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18887 : List Nat := [1, 1, 4, 1, 1, 5, 2, 4]
def baseStart_18887 : Nat := 118140960795 + 18887 * 2 ^ 59
def prefixEnd_18887 : Nat := 4983230072969 + 3 ^ 40 * 18887 * 2
def baseEnd_18887 : Nat := 5747027627598718948531

theorem tailTrace_18887 : CollatzResearch.WordTrace tailWord_18887 prefixEnd_18887 5747027627598718948531 := by
  unfold tailWord_18887
  simp only [CollatzResearch.WordTrace]
  refine ⟨688865482583099487902915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 459243655055399658601943 688865482583099487902915)
  ·
    refine ⟨1033298223874649231854373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 688865482583099487902915 1033298223874649231854373)
    ·
      refine ⟨193743416976496730972695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1033298223874649231854373 193743416976496730972695)
      ·
        refine ⟨290615125464745096459043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193743416976496730972695 290615125464745096459043)
        ·
          refine ⟨435922688197117644688565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290615125464745096459043 435922688197117644688565)
          ·
            refine ⟨40867752018479779189553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 435922688197117644688565 40867752018479779189553)
            ·
              refine ⟨30650814013859834392165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40867752018479779189553 30650814013859834392165)
              ·
                refine ⟨5747027627598718948531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30650814013859834392165 5747027627598718948531)
                ·
                  rfl

theorem cell19_18887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_18887 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18887 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18887 prefixEnd_18887 := by exact prefixLift 18887
  have htrace : WordTrace (prefixWord ++ tailWord_18887) baseStart_18887 baseEnd_18887 := by
    simpa [prefixWord, tailWord_18887, baseEnd_18887] using wordTrace_append hprefix tailTrace_18887
  have hstable : (prefixWord ++ tailWord_18887).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18887).length < 2 ^ (prefixWord ++ tailWord_18887).sum := by decide
  have hdescent : baseEnd_18887 < baseStart_18887 := by decide
  rcases family_descends (prefixWord ++ tailWord_18887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18889 : List Nat := [1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_18889 : Nat := 118140960795 + 18889 * 2 ^ 59
def prefixEnd_18889 : Nat := 4983230072969 + 3 ^ 40 * 18889 * 2
def baseEnd_18889 : Nat := 5747636197263306904081

theorem tailTrace_18889 : CollatzResearch.WordTrace tailWord_18889 prefixEnd_18889 5747636197263306904081 := by
  unfold tailWord_18889
  simp only [CollatzResearch.WordTrace]
  refine ⟨688938428575853829475721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 459292285717235886317147 688938428575853829475721)
  ·
    refine ⟨516703821431890372106791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 688938428575853829475721 516703821431890372106791)
    ·
      refine ⟨775055732147835558160187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516703821431890372106791 775055732147835558160187)
      ·
        refine ⟨1162583598221753337240281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 775055732147835558160187 1162583598221753337240281)
        ·
          refine ⟨871937698666315002930211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1162583598221753337240281 871937698666315002930211)
          ·
            refine ⟨1307906547999472504395317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871937698666315002930211 1307906547999472504395317)
            ·
              refine ⟨122616238874950547287061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1307906547999472504395317 122616238874950547287061)
              ·
                refine ⟨5747636197263306904081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122616238874950547287061 5747636197263306904081)
                ·
                  rfl

theorem cell19_18889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_18889 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18889 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18889 prefixEnd_18889 := by exact prefixLift 18889
  have htrace : WordTrace (prefixWord ++ tailWord_18889) baseStart_18889 baseEnd_18889 := by
    simpa [prefixWord, tailWord_18889, baseEnd_18889] using wordTrace_append hprefix tailTrace_18889
  have hstable : (prefixWord ++ tailWord_18889).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18889).length < 2 ^ (prefixWord ++ tailWord_18889).sum := by decide
  have hdescent : baseEnd_18889 < baseStart_18889 := by decide
  rcases family_descends (prefixWord ++ tailWord_18889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18925 : List Nat := [1, 5, 1, 3, 1, 8]
def baseStart_18925 : Nat := 118140960795 + 18925 * 2 ^ 59
def prefixEnd_18925 : Nat := 4983230072969 + 3 ^ 40 * 18925 * 2
def baseEnd_18925 : Nat := 639843383469543344887

theorem tailTrace_18925 : CollatzResearch.WordTrace tailWord_18925 prefixEnd_18925 639843383469543344887 := by
  unfold tailWord_18925
  simp only [CollatzResearch.WordTrace]
  refine ⟨690251456445431977786229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 460167637630287985190819 690251456445431977786229)
  ·
    refine ⟨64711074041759247917459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 690251456445431977786229 64711074041759247917459)
    ·
      refine ⟨97066611062638871876189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64711074041759247917459 97066611062638871876189)
      ·
        refine ⟨36399979148489576953571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97066611062638871876189 36399979148489576953571)
        ·
          refine ⟨54599968722734365430357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36399979148489576953571 54599968722734365430357)
          ·
            refine ⟨639843383469543344887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 54599968722734365430357 639843383469543344887)
            ·
              rfl

theorem cell19_18925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 8].length) (baseStart_18925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18925 prefixEnd_18925 := by exact prefixLift 18925
  have htrace : WordTrace (prefixWord ++ tailWord_18925) baseStart_18925 baseEnd_18925 := by
    simpa [prefixWord, tailWord_18925, baseEnd_18925] using wordTrace_append hprefix tailTrace_18925
  have hstable : (prefixWord ++ tailWord_18925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18925).length < 2 ^ (prefixWord ++ tailWord_18925).sum := by decide
  have hdescent : baseEnd_18925 < baseStart_18925 := by decide
  rcases family_descends (prefixWord ++ tailWord_18925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18957 : List Nat := [1, 7, 1, 1, 1, 2, 3, 3]
def baseStart_18957 : Nat := 118140960795 + 18957 * 2 ^ 59
def prefixEnd_18957 : Nat := 4983230072969 + 3 ^ 40 * 18957 * 2
def baseEnd_18957 : Nat := 5768327565859297392785

theorem tailTrace_18957 : CollatzResearch.WordTrace tailWord_18957 prefixEnd_18957 5768327565859297392785 := by
  unfold tailWord_18957
  simp only [CollatzResearch.WordTrace]
  refine ⟨691418592329501442951125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 460945728219667628634083 691418592329501442951125)
  ·
    refine ⟨16205123257722690069167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 691418592329501442951125 16205123257722690069167)
    ·
      refine ⟨24307684886584035103751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16205123257722690069167 24307684886584035103751)
      ·
        refine ⟨36461527329876052655627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24307684886584035103751 36461527329876052655627)
        ·
          refine ⟨54692290994814078983441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36461527329876052655627 54692290994814078983441)
          ·
            refine ⟨41019218246110559237581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54692290994814078983441 41019218246110559237581)
            ·
              refine ⟨15382206842291459714093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41019218246110559237581 15382206842291459714093)
              ·
                refine ⟨5768327565859297392785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15382206842291459714093 5768327565859297392785)
                ·
                  rfl

theorem cell19_18957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 3].length) (baseStart_18957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18957 prefixEnd_18957 := by exact prefixLift 18957
  have htrace : WordTrace (prefixWord ++ tailWord_18957) baseStart_18957 baseEnd_18957 := by
    simpa [prefixWord, tailWord_18957, baseEnd_18957] using wordTrace_append hprefix tailTrace_18957
  have hstable : (prefixWord ++ tailWord_18957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18957).length < 2 ^ (prefixWord ++ tailWord_18957).sum := by decide
  have hdescent : baseEnd_18957 < baseStart_18957 := by decide
  rcases family_descends (prefixWord ++ tailWord_18957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18963 : List Nat := [1, 1, 1, 2, 1, 5, 5, 3]
def baseStart_18963 : Nat := 118140960795 + 18963 * 2 ^ 59
def prefixEnd_18963 : Nat := 4983230072969 + 3 ^ 40 * 18963 * 2
def baseEnd_18963 : Nat := 5770153274853061259435

theorem tailTrace_18963 : CollatzResearch.WordTrace tailWord_18963 prefixEnd_18963 5770153274853061259435 := by
  unfold tailWord_18963
  simp only [CollatzResearch.WordTrace]
  refine ⟨691637430307764467669543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 461091620205176311779695 691637430307764467669543)
  ·
    refine ⟨1037456145461646701504315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 691637430307764467669543 1037456145461646701504315)
    ·
      refine ⟨1556184218192470052256473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1037456145461646701504315 1556184218192470052256473)
      ·
        refine ⟨1167138163644352539192355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1556184218192470052256473 1167138163644352539192355)
        ·
          refine ⟨1750707245466528808788533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1167138163644352539192355 1750707245466528808788533)
          ·
            refine ⟨164128804262487075823925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1750707245466528808788533 164128804262487075823925)
            ·
              refine ⟨15387075399608163358493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 164128804262487075823925 15387075399608163358493)
              ·
                refine ⟨5770153274853061259435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15387075399608163358493 5770153274853061259435)
                ·
                  rfl

theorem cell19_18963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 3].length) (baseStart_18963 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18963 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18963 prefixEnd_18963 := by exact prefixLift 18963
  have htrace : WordTrace (prefixWord ++ tailWord_18963) baseStart_18963 baseEnd_18963 := by
    simpa [prefixWord, tailWord_18963, baseEnd_18963] using wordTrace_append hprefix tailTrace_18963
  have hstable : (prefixWord ++ tailWord_18963).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18963).length < 2 ^ (prefixWord ++ tailWord_18963).sum := by decide
  have hdescent : baseEnd_18963 < baseStart_18963 := by decide
  rcases family_descends (prefixWord ++ tailWord_18963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_18980 : List Nat := [2, 3, 1, 5, 1, 1, 6]
def baseStart_18980 : Nat := 118140960795 + 18980 * 2 ^ 59
def prefixEnd_18980 : Nat := 4983230072969 + 3 ^ 40 * 18980 * 2
def baseEnd_18980 : Nat := 1925108705667352960537

theorem tailTrace_18980 : CollatzResearch.WordTrace tailWord_18980 prefixEnd_18980 1925108705667352960537 := by
  unfold tailWord_18980
  simp only [CollatzResearch.WordTrace]
  refine ⟨346128735623088185519197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 461504980830784247358929 346128735623088185519197)
  ·
    refine ⟨129798275858658069569699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 346128735623088185519197 129798275858658069569699)
    ·
      refine ⟨194697413787987104354549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129798275858658069569699 194697413787987104354549)
      ·
        refine ⟨18252882542623791033239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 194697413787987104354549 18252882542623791033239)
        ·
          refine ⟨27379323813935686549859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18252882542623791033239 27379323813935686549859)
          ·
            refine ⟨41068985720903529824789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27379323813935686549859 41068985720903529824789)
            ·
              refine ⟨1925108705667352960537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41068985720903529824789 1925108705667352960537)
              ·
                rfl

theorem cell19_18980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 6].length) (baseStart_18980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_18980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_18980 prefixEnd_18980 := by exact prefixLift 18980
  have htrace : WordTrace (prefixWord ++ tailWord_18980) baseStart_18980 baseEnd_18980 := by
    simpa [prefixWord, tailWord_18980, baseEnd_18980] using wordTrace_append hprefix tailTrace_18980
  have hstable : (prefixWord ++ tailWord_18980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_18980).length < 2 ^ (prefixWord ++ tailWord_18980).sum := by decide
  have hdescent : baseEnd_18980 < baseStart_18980 := by decide
  rcases family_descends (prefixWord ++ tailWord_18980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19012 : List Nat := [2, 3, 5, 1, 1, 2, 2, 3]
def baseStart_19012 : Nat := 118140960795 + 19012 * 2 ^ 59
def prefixEnd_19012 : Nat := 4983230072969 + 3 ^ 40 * 19012 * 2
def baseEnd_19012 : Nat := 5785063231635466170413

theorem tailTrace_19012 : CollatzResearch.WordTrace tailWord_19012 prefixEnd_19012 5785063231635466170413 := by
  unfold tailWord_19012
  simp only [CollatzResearch.WordTrace]
  refine ⟨346712303565122918101645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 462283071420163890802193 346712303565122918101645)
  ·
    refine ⟨130017113836921094288117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 346712303565122918101645 130017113836921094288117)
    ·
      refine ⟨12189104422211352589511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130017113836921094288117 12189104422211352589511)
      ·
        refine ⟨18283656633317028884267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12189104422211352589511 18283656633317028884267)
        ·
          refine ⟨27425484949975543326401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18283656633317028884267 27425484949975543326401)
          ·
            refine ⟨20569113712481657494801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27425484949975543326401 20569113712481657494801)
            ·
              refine ⟨15426835284361243121101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20569113712481657494801 15426835284361243121101)
              ·
                refine ⟨5785063231635466170413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15426835284361243121101 5785063231635466170413)
                ·
                  rfl

theorem cell19_19012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_19012 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19012 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19012 prefixEnd_19012 := by exact prefixLift 19012
  have htrace : WordTrace (prefixWord ++ tailWord_19012) baseStart_19012 baseEnd_19012 := by
    simpa [prefixWord, tailWord_19012, baseEnd_19012] using wordTrace_append hprefix tailTrace_19012
  have hstable : (prefixWord ++ tailWord_19012).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19012).length < 2 ^ (prefixWord ++ tailWord_19012).sum := by decide
  have hdescent : baseEnd_19012 < baseStart_19012 := by decide
  rcases family_descends (prefixWord ++ tailWord_19012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19014 : List Nat := [6, 1, 1, 1, 2, 3, 2, 3]
def baseStart_19014 : Nat := 118140960795 + 19014 * 2 ^ 59
def prefixEnd_19014 : Nat := 4983230072969 + 3 ^ 40 * 19014 * 2
def baseEnd_19014 : Nat := 5785671801300054125963

theorem tailTrace_19014 : CollatzResearch.WordTrace tailWord_19014 prefixEnd_19014 5785671801300054125963 := by
  unfold tailWord_19014
  simp only [CollatzResearch.WordTrace]
  refine ⟨21671798535093755555503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 462331702082000118517397 21671798535093755555503)
  ·
    refine ⟨32507697802640633333255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21671798535093755555503 32507697802640633333255)
    ·
      refine ⟨48761546703960949999883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32507697802640633333255 48761546703960949999883)
      ·
        refine ⟨73142320055941424999825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48761546703960949999883 73142320055941424999825)
        ·
          refine ⟨54856740041956068749869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73142320055941424999825 54856740041956068749869)
          ·
            refine ⟨20571277515733525781201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54856740041956068749869 20571277515733525781201)
            ·
              refine ⟨15428458136800144335901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20571277515733525781201 15428458136800144335901)
              ·
                refine ⟨5785671801300054125963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15428458136800144335901 5785671801300054125963)
                ·
                  rfl

theorem cell19_19014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_19014 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19014 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19014 prefixEnd_19014 := by exact prefixLift 19014
  have htrace : WordTrace (prefixWord ++ tailWord_19014) baseStart_19014 baseEnd_19014 := by
    simpa [prefixWord, tailWord_19014, baseEnd_19014] using wordTrace_append hprefix tailTrace_19014
  have hstable : (prefixWord ++ tailWord_19014).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19014).length < 2 ^ (prefixWord ++ tailWord_19014).sum := by decide
  have hdescent : baseEnd_19014 < baseStart_19014 := by decide
  rcases family_descends (prefixWord ++ tailWord_19014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19018 : List Nat := [3, 1, 2, 1, 1, 6, 2, 3]
def baseStart_19018 : Nat := 118140960795 + 19018 * 2 ^ 59
def prefixEnd_19018 : Nat := 4983230072969 + 3 ^ 40 * 19018 * 2
def baseEnd_19018 : Nat := 5786888940629230037063

theorem tailTrace_19018 : CollatzResearch.WordTrace tailWord_19018 prefixEnd_19018 5786888940629230037063 := by
  unfold tailWord_19018
  simp only [CollatzResearch.WordTrace]
  refine ⟨173410861277127215230427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 462428963405672573947805 173410861277127215230427)
  ·
    refine ⟨260116291915690822845641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 173410861277127215230427 260116291915690822845641)
    ·
      refine ⟨195087218936768117134231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260116291915690822845641 195087218936768117134231)
      ·
        refine ⟨292630828405152175701347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195087218936768117134231 292630828405152175701347)
        ·
          refine ⟨438946242607728263552021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292630828405152175701347 438946242607728263552021)
          ·
            refine ⟨20575605122237262354001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 438946242607728263552021 20575605122237262354001)
            ·
              refine ⟨15431703841677946765501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20575605122237262354001 15431703841677946765501)
              ·
                refine ⟨5786888940629230037063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15431703841677946765501 5786888940629230037063)
                ·
                  rfl

theorem cell19_19018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_19018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19018 prefixEnd_19018 := by exact prefixLift 19018
  have htrace : WordTrace (prefixWord ++ tailWord_19018) baseStart_19018 baseEnd_19018 := by
    simpa [prefixWord, tailWord_19018, baseEnd_19018] using wordTrace_append hprefix tailTrace_19018
  have hstable : (prefixWord ++ tailWord_19018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19018).length < 2 ^ (prefixWord ++ tailWord_19018).sum := by decide
  have hdescent : baseEnd_19018 < baseStart_19018 := by decide
  rcases family_descends (prefixWord ++ tailWord_19018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19041 : List Nat := [1, 2, 3, 1, 1, 4, 7]
def baseStart_19041 : Nat := 118140960795 + 19041 * 2 ^ 59
def prefixEnd_19041 : Nat := 4983230072969 + 3 ^ 40 * 19041 * 2
def baseEnd_19041 : Nat := 1931295830590663841963

theorem tailTrace_19041 : CollatzResearch.WordTrace tailWord_19041 prefixEnd_19041 1931295830590663841963 := by
  unfold tailWord_19041
  simp only [CollatzResearch.WordTrace]
  refine ⟨694482324025183789008977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 462988216016789192672651 694482324025183789008977)
  ·
    refine ⟨520861743018887841756733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 694482324025183789008977 520861743018887841756733)
    ·
      refine ⟨195323153632082940658775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 520861743018887841756733 195323153632082940658775)
      ·
        refine ⟨292984730448124410988163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195323153632082940658775 292984730448124410988163)
        ·
          refine ⟨439477095672186616482245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292984730448124410988163 439477095672186616482245)
          ·
            refine ⟨82401955438534990590421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 439477095672186616482245 82401955438534990590421)
            ·
              refine ⟨1931295830590663841963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 82401955438534990590421 1931295830590663841963)
              ·
                rfl

theorem cell19_19041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_19041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19041 prefixEnd_19041 := by exact prefixLift 19041
  have htrace : WordTrace (prefixWord ++ tailWord_19041) baseStart_19041 baseEnd_19041 := by
    simpa [prefixWord, tailWord_19041, baseEnd_19041] using wordTrace_append hprefix tailTrace_19041
  have hstable : (prefixWord ++ tailWord_19041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19041).length < 2 ^ (prefixWord ++ tailWord_19041).sum := by decide
  have hdescent : baseEnd_19041 < baseStart_19041 := by decide
  rcases family_descends (prefixWord ++ tailWord_19041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19079 : List Nat := [1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_19079 : Nat := 118140960795 + 19079 * 2 ^ 59
def prefixEnd_19079 : Nat := 4983230072969 + 3 ^ 40 * 19079 * 2
def baseEnd_19079 : Nat := 5805450315399162681341

theorem tailTrace_19079 : CollatzResearch.WordTrace tailWord_19079 prefixEnd_19079 5805450315399162681341 := by
  unfold tailWord_19079
  simp only [CollatzResearch.WordTrace]
  refine ⟨695868297887516278892291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 463912198591677519261527 695868297887516278892291)
  ·
    refine ⟨1043802446831274418338437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 695868297887516278892291 1043802446831274418338437)
    ·
      refine ⟨195712958780863953438457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1043802446831274418338437 195712958780863953438457)
      ·
        refine ⟨146784719085647965078843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195712958780863953438457 146784719085647965078843)
        ·
          refine ⟨220177078628471947618265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146784719085647965078843 220177078628471947618265)
          ·
            refine ⟨165132808971353960713699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220177078628471947618265 165132808971353960713699)
            ·
              refine ⟨247699213457030941070549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165132808971353960713699 247699213457030941070549)
              ·
                refine ⟨5805450315399162681341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 247699213457030941070549 5805450315399162681341)
                ·
                  rfl

theorem cell19_19079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_19079 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19079 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19079 prefixEnd_19079 := by exact prefixLift 19079
  have htrace : WordTrace (prefixWord ++ tailWord_19079) baseStart_19079 baseEnd_19079 := by
    simpa [prefixWord, tailWord_19079, baseEnd_19079] using wordTrace_append hprefix tailTrace_19079
  have hstable : (prefixWord ++ tailWord_19079).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19079).length < 2 ^ (prefixWord ++ tailWord_19079).sum := by decide
  have hdescent : baseEnd_19079 < baseStart_19079 := by decide
  rcases family_descends (prefixWord ++ tailWord_19079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19111 : List Nat := [1, 1, 6, 3, 1, 2, 1, 4]
def baseStart_19111 : Nat := 118140960795 + 19111 * 2 ^ 59
def prefixEnd_19111 : Nat := 4983230072969 + 3 ^ 40 * 19111 * 2
def baseEnd_19111 : Nat := 5815187430032569970143

theorem tailTrace_19111 : CollatzResearch.WordTrace tailWord_19111 prefixEnd_19111 5815187430032569970143 := by
  unfold tailWord_19111
  simp only [CollatzResearch.WordTrace]
  refine ⟨697035433771585744057187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 464690289181057162704791 697035433771585744057187)
  ·
    refine ⟨1045553150657378616085781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 697035433771585744057187 1045553150657378616085781)
    ·
      refine ⟨49010303937064622629021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1045553150657378616085781 49010303937064622629021)
      ·
        refine ⟨18378863976399233485883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49010303937064622629021 18378863976399233485883)
        ·
          refine ⟨27568295964598850228825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18378863976399233485883 27568295964598850228825)
          ·
            refine ⟨20676221973449137671619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27568295964598850228825 20676221973449137671619)
            ·
              refine ⟨31014332960173706507429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20676221973449137671619 31014332960173706507429)
              ·
                refine ⟨5815187430032569970143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31014332960173706507429 5815187430032569970143)
                ·
                  rfl

theorem cell19_19111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 4].length) (baseStart_19111 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19111 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19111 prefixEnd_19111 := by exact prefixLift 19111
  have htrace : WordTrace (prefixWord ++ tailWord_19111) baseStart_19111 baseEnd_19111 := by
    simpa [prefixWord, tailWord_19111, baseEnd_19111] using wordTrace_append hprefix tailTrace_19111
  have hstable : (prefixWord ++ tailWord_19111).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19111).length < 2 ^ (prefixWord ++ tailWord_19111).sum := by decide
  have hdescent : baseEnd_19111 < baseStart_19111 := by decide
  rcases family_descends (prefixWord ++ tailWord_19111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19231 : List Nat := [1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_19231 : Nat := 118140960795 + 19231 * 2 ^ 59
def prefixEnd_19231 : Nat := 4983230072969 + 3 ^ 40 * 19231 * 2
def baseEnd_19231 : Nat := 5851701609907847303149

theorem tailTrace_19231 : CollatzResearch.WordTrace tailWord_19231 prefixEnd_19231 5851701609907847303149 := by
  unfold tailWord_19231
  simp only [CollatzResearch.WordTrace]
  refine ⟨701412193336846238425547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 467608128891230825617031 701412193336846238425547)
  ·
    refine ⟨1052118290005269357638321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 701412193336846238425547 1052118290005269357638321)
    ·
      refine ⟨789088717503952018228741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1052118290005269357638321 789088717503952018228741)
      ·
        refine ⟨147954134531991003417889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 789088717503952018228741 147954134531991003417889)
        ·
          refine ⟨110965600898993252563417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147954134531991003417889 110965600898993252563417)
          ·
            refine ⟨83224200674244939422563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110965600898993252563417 83224200674244939422563)
            ·
              refine ⟨124836301011367409133845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83224200674244939422563 124836301011367409133845)
              ·
                refine ⟨5851701609907847303149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124836301011367409133845 5851701609907847303149)
                ·
                  rfl

theorem cell19_19231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_19231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19231 prefixEnd_19231 := by exact prefixLift 19231
  have htrace : WordTrace (prefixWord ++ tailWord_19231) baseStart_19231 baseEnd_19231 := by
    simpa [prefixWord, tailWord_19231, baseEnd_19231] using wordTrace_append hprefix tailTrace_19231
  have hstable : (prefixWord ++ tailWord_19231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19231).length < 2 ^ (prefixWord ++ tailWord_19231).sum := by decide
  have hdescent : baseEnd_19231 < baseStart_19231 := by decide
  rcases family_descends (prefixWord ++ tailWord_19231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19250 : List Nat := [3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_19250 : Nat := 118140960795 + 19250 * 2 ^ 59
def prefixEnd_19250 : Nat := 4983230072969 + 3 ^ 40 * 19250 * 2
def baseEnd_19250 : Nat := 5857483021721432880875

theorem tailTrace_19250 : CollatzResearch.WordTrace tailWord_19250 prefixEnd_19250 5857483021721432880875 := by
  unfold tailWord_19250
  simp only [CollatzResearch.WordTrace]
  refine ⟨175526295067003120841801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 468070120178674988911469 175526295067003120841801)
  ·
    refine ⟨131644721300252340631351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175526295067003120841801 131644721300252340631351)
    ·
      refine ⟨197467081950378510947027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131644721300252340631351 197467081950378510947027)
      ·
        refine ⟨296200622925567766420541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197467081950378510947027 296200622925567766420541)
        ·
          refine ⟨111075233597087912407703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296200622925567766420541 111075233597087912407703)
          ·
            refine ⟨166612850395631868611555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111075233597087912407703 166612850395631868611555)
            ·
              refine ⟨249919275593447802917333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166612850395631868611555 249919275593447802917333)
              ·
                refine ⟨5857483021721432880875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 249919275593447802917333 5857483021721432880875)
                ·
                  rfl

theorem cell19_19250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_19250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19250 prefixEnd_19250 := by exact prefixLift 19250
  have htrace : WordTrace (prefixWord ++ tailWord_19250) baseStart_19250 baseEnd_19250 := by
    simpa [prefixWord, tailWord_19250, baseEnd_19250] using wordTrace_append hprefix tailTrace_19250
  have hstable : (prefixWord ++ tailWord_19250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19250).length < 2 ^ (prefixWord ++ tailWord_19250).sum := by decide
  have hdescent : baseEnd_19250 < baseStart_19250 := by decide
  rcases family_descends (prefixWord ++ tailWord_19250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19265 : List Nat := [1, 2, 5, 3, 2, 6]
def baseStart_19265 : Nat := 118140960795 + 19265 * 2 ^ 59
def prefixEnd_19265 : Nat := 4983230072969 + 3 ^ 40 * 19265 * 2
def baseEnd_19265 : Nat := 651338588245093616389

theorem tailTrace_19265 : CollatzResearch.WordTrace tailWord_19265 prefixEnd_19265 651338588245093616389 := by
  unfold tailWord_19265
  simp only [CollatzResearch.WordTrace]
  refine ⟨702652275213670045163249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 468434850142446696775499 702652275213670045163249)
  ·
    refine ⟨526989206410252533872437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 702652275213670045163249 526989206410252533872437)
    ·
      refine ⟨49405238100961175050541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 526989206410252533872437 49405238100961175050541)
      ·
        refine ⟨18526964287860440643953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49405238100961175050541 18526964287860440643953)
        ·
          refine ⟨13895223215895330482965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18526964287860440643953 13895223215895330482965)
          ·
            refine ⟨651338588245093616389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13895223215895330482965 651338588245093616389)
            ·
              rfl

theorem cell19_19265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 6].length) (baseStart_19265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19265 prefixEnd_19265 := by exact prefixLift 19265
  have htrace : WordTrace (prefixWord ++ tailWord_19265) baseStart_19265 baseEnd_19265 := by
    simpa [prefixWord, tailWord_19265, baseEnd_19265] using wordTrace_append hprefix tailTrace_19265
  have hstable : (prefixWord ++ tailWord_19265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19265).length < 2 ^ (prefixWord ++ tailWord_19265).sum := by decide
  have hdescent : baseEnd_19265 < baseStart_19265 := by decide
  rcases family_descends (prefixWord ++ tailWord_19265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19284 : List Nat := [2, 4, 1, 1, 4, 2, 1, 4]
def baseStart_19284 : Nat := 118140960795 + 19284 * 2 ^ 59
def prefixEnd_19284 : Nat := 4983230072969 + 3 ^ 40 * 19284 * 2
def baseEnd_19284 : Nat := 5867828706019428125227

theorem tailTrace_19284 : CollatzResearch.WordTrace tailWord_19284 prefixEnd_19284 5867828706019428125227 := by
  unfold tailWord_19284
  simp only [CollatzResearch.WordTrace]
  refine ⟨351672631072418145052453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 468896841429890860069937 351672631072418145052453)
  ·
    refine ⟨65938618326078402197335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 351672631072418145052453 65938618326078402197335)
    ·
      refine ⟨98907927489117603296003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65938618326078402197335 98907927489117603296003)
      ·
        refine ⟨148361891233676404944005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98907927489117603296003 148361891233676404944005)
        ·
          refine ⟨27817854606314325927001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148361891233676404944005 27817854606314325927001)
          ·
            refine ⟨20863390954735744445251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27817854606314325927001 20863390954735744445251)
            ·
              refine ⟨31295086432103616667877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20863390954735744445251 31295086432103616667877)
              ·
                refine ⟨5867828706019428125227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31295086432103616667877 5867828706019428125227)
                ·
                  rfl

theorem cell19_19284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_19284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19284 prefixEnd_19284 := by exact prefixLift 19284
  have htrace : WordTrace (prefixWord ++ tailWord_19284) baseStart_19284 baseEnd_19284 := by
    simpa [prefixWord, tailWord_19284, baseEnd_19284] using wordTrace_append hprefix tailTrace_19284
  have hstable : (prefixWord ++ tailWord_19284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19284).length < 2 ^ (prefixWord ++ tailWord_19284).sum := by decide
  have hdescent : baseEnd_19284 < baseStart_19284 := by decide
  rcases family_descends (prefixWord ++ tailWord_19284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19362 : List Nat := [3, 3, 1, 2, 2, 2, 1, 5]
def baseStart_19362 : Nat := 118140960795 + 19362 * 2 ^ 59
def prefixEnd_19362 : Nat := 4983230072969 + 3 ^ 40 * 19362 * 2
def baseEnd_19362 : Nat := 5891562922938358391681

theorem tailTrace_19362 : CollatzResearch.WordTrace tailWord_19362 prefixEnd_19362 5891562922938358391681 := by
  unfold tailWord_19362
  simp only [CollatzResearch.WordTrace]
  refine ⟨176547538965563902861085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 470793437241503740962893 176547538965563902861085)
  ·
    refine ⟨66205327112086463572907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176547538965563902861085 66205327112086463572907)
    ·
      refine ⟨99307990668129695359361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66205327112086463572907 99307990668129695359361)
      ·
        refine ⟨74480993001097271519521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99307990668129695359361 74480993001097271519521)
        ·
          refine ⟨55860744750822953639641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74480993001097271519521 55860744750822953639641)
          ·
            refine ⟨41895558563117215229731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55860744750822953639641 41895558563117215229731)
            ·
              refine ⟨62843337844675822844597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41895558563117215229731 62843337844675822844597)
              ·
                refine ⟨5891562922938358391681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62843337844675822844597 5891562922938358391681)
                ·
                  rfl

theorem cell19_19362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_19362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19362 prefixEnd_19362 := by exact prefixLift 19362
  have htrace : WordTrace (prefixWord ++ tailWord_19362) baseStart_19362 baseEnd_19362 := by
    simpa [prefixWord, tailWord_19362, baseEnd_19362] using wordTrace_append hprefix tailTrace_19362
  have hstable : (prefixWord ++ tailWord_19362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19362).length < 2 ^ (prefixWord ++ tailWord_19362).sum := by decide
  have hdescent : baseEnd_19362 < baseStart_19362 := by decide
  rcases family_descends (prefixWord ++ tailWord_19362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19364 : List Nat := [2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_19364 : Nat := 118140960795 + 19364 * 2 ^ 59
def prefixEnd_19364 : Nat := 4983230072969 + 3 ^ 40 * 19364 * 2
def baseEnd_19364 : Nat := 5892171492602946347231

theorem tailTrace_19364 : CollatzResearch.WordTrace tailWord_19364 prefixEnd_19364 5892171492602946347231 := by
  unfold tailWord_19364
  simp only [CollatzResearch.WordTrace]
  refine ⟨353131550927504976508573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 470842067903339968678097 353131550927504976508573)
  ·
    refine ⟨132424331597814366190715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 353131550927504976508573 132424331597814366190715)
    ·
      refine ⟨198636497396721549286073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132424331597814366190715 198636497396721549286073)
      ·
        refine ⟨148977373047541161964555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198636497396721549286073 148977373047541161964555)
        ·
          refine ⟨223466059571311742946833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148977373047541161964555 223466059571311742946833)
          ·
            refine ⟨167599544678483807210125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223466059571311742946833 167599544678483807210125)
            ·
              refine ⟨62849829254431427703797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167599544678483807210125 62849829254431427703797)
              ·
                refine ⟨5892171492602946347231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62849829254431427703797 5892171492602946347231)
                ·
                  rfl

theorem cell19_19364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_19364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19364 prefixEnd_19364 := by exact prefixLift 19364
  have htrace : WordTrace (prefixWord ++ tailWord_19364) baseStart_19364 baseEnd_19364 := by
    simpa [prefixWord, tailWord_19364, baseEnd_19364] using wordTrace_append hprefix tailTrace_19364
  have hstable : (prefixWord ++ tailWord_19364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19364).length < 2 ^ (prefixWord ++ tailWord_19364).sum := by decide
  have hdescent : baseEnd_19364 < baseStart_19364 := by decide
  rcases family_descends (prefixWord ++ tailWord_19364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19400 : List Nat := [2, 1, 3, 1, 5, 1, 2, 4]
def baseStart_19400 : Nat := 118140960795 + 19400 * 2 ^ 59
def prefixEnd_19400 : Nat := 4983230072969 + 3 ^ 40 * 19400 * 2
def baseEnd_19400 : Nat := 5903125746565529547133

theorem tailTrace_19400 : CollatzResearch.WordTrace tailWord_19400 prefixEnd_19400 5903125746565529547133 := by
  unfold tailWord_19400
  simp only [CollatzResearch.WordTrace]
  refine ⟨353788064862294050663827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 471717419816392067551769 353788064862294050663827)
  ·
    refine ⟨530682097293441075995741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 353788064862294050663827 530682097293441075995741)
    ·
      refine ⟨199005786485040403498403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 530682097293441075995741 199005786485040403498403)
      ·
        refine ⟨298508679727560605247605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199005786485040403498403 298508679727560605247605)
        ·
          refine ⟨27985188724458806741963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 298508679727560605247605 27985188724458806741963)
          ·
            refine ⟨41977783086688210112945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27985188724458806741963 41977783086688210112945)
            ·
              refine ⟨31483337315016157584709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41977783086688210112945 31483337315016157584709)
              ·
                refine ⟨5903125746565529547133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31483337315016157584709 5903125746565529547133)
                ·
                  rfl

theorem cell19_19400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_19400 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19400 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19400 prefixEnd_19400 := by exact prefixLift 19400
  have htrace : WordTrace (prefixWord ++ tailWord_19400) baseStart_19400 baseEnd_19400 := by
    simpa [prefixWord, tailWord_19400, baseEnd_19400] using wordTrace_append hprefix tailTrace_19400
  have hstable : (prefixWord ++ tailWord_19400).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19400).length < 2 ^ (prefixWord ++ tailWord_19400).sum := by decide
  have hdescent : baseEnd_19400 < baseStart_19400 := by decide
  rcases family_descends (prefixWord ++ tailWord_19400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_19438 : List Nat := [4, 1, 2, 1, 5, 6]
def baseStart_19438 : Nat := 118140960795 + 19438 * 2 ^ 59
def prefixEnd_19438 : Nat := 4983230072969 + 3 ^ 40 * 19438 * 2
def baseEnd_19438 : Nat := 657187618910300078065

theorem tailTrace_19438 : CollatzResearch.WordTrace tailWord_19438 prefixEnd_19438 657187618910300078065 := by
  unfold tailWord_19438
  simp only [CollatzResearch.WordTrace]
  refine ⟨88620262948365073901371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 472641402391280394140645 88620262948365073901371)
  ·
    refine ⟨132930394422547610852057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88620262948365073901371 132930394422547610852057)
    ·
      refine ⟨99697795816910708139043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132930394422547610852057 99697795816910708139043)
      ·
        refine ⟨149546693725366062208565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99697795816910708139043 149546693725366062208565)
        ·
          refine ⟨14020002536753068332053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149546693725366062208565 14020002536753068332053)
          ·
            refine ⟨657187618910300078065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14020002536753068332053 657187618910300078065)
            ·
              rfl

theorem cell19_19438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 6].length) (baseStart_19438 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_19438 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_19438 prefixEnd_19438 := by exact prefixLift 19438
  have htrace : WordTrace (prefixWord ++ tailWord_19438) baseStart_19438 baseEnd_19438 := by
    simpa [prefixWord, tailWord_19438, baseEnd_19438] using wordTrace_append hprefix tailTrace_19438
  have hstable : (prefixWord ++ tailWord_19438).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_19438).length < 2 ^ (prefixWord ++ tailWord_19438).sum := by decide
  have hdescent : baseEnd_19438 < baseStart_19438 := by decide
  rcases family_descends (prefixWord ++ tailWord_19438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
