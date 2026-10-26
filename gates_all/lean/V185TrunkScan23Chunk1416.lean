import V185TrunkScan23Chunk1415

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8387746 : List Nat := [3, 3, 1, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_8387746 : Nat := 118140960795 + 8387746 * 2 ^ 59
def prefixEnd_8387746 : Nat := 4983230072969 + 3 ^ 40 * 8387746 * 2
def baseEnd_8387746 : Nat := 4306945305827045138900465

theorem tailTrace_8387746 : CollatzResearch.WordTrace tailWord_8387746 prefixEnd_8387746 4306945305827045138900465 := by
  unfold tailWord_8387746
  simp only [CollatzResearch.WordTrace]
  refine ⟨76481557367659057453431773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203950819647090819875818061 76481557367659057453431773)
  ·
    refine ⟨28680584012872146545036915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76481557367659057453431773 28680584012872146545036915)
    ·
      refine ⟨43020876019308219817555373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28680584012872146545036915 43020876019308219817555373)
      ·
        refine ⟨16132828507240582431583265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43020876019308219817555373 16132828507240582431583265)
        ·
          refine ⟨12099621380430436823687449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16132828507240582431583265 12099621380430436823687449)
          ·
            refine ⟨9074716035322827617765587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12099621380430436823687449 9074716035322827617765587)
            ·
              refine ⟨13612074052984241426648381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9074716035322827617765587 13612074052984241426648381)
              ·
                refine ⟨5104527769869090534993143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13612074052984241426648381 5104527769869090534993143)
                ·
                  refine ⟨7656791654803635802489715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5104527769869090534993143 7656791654803635802489715)
                  ·
                    refine ⟨11485187482205453703734573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7656791654803635802489715 11485187482205453703734573)
                    ·
                      refine ⟨4306945305827045138900465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11485187482205453703734573 4306945305827045138900465)
                      ·
                        rfl

theorem cell23_8387746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_8387746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387746 prefixEnd_8387746 := by exact prefixLift 8387746
  have htrace : WordTrace (prefixWord ++ tailWord_8387746) baseStart_8387746 baseEnd_8387746 := by
    simpa [prefixWord, tailWord_8387746, baseEnd_8387746] using wordTrace_append hprefix tailTrace_8387746
  have hstable : (prefixWord ++ tailWord_8387746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387746).length < 2 ^ (prefixWord ++ tailWord_8387746).sum := by decide
  have hdescent : baseEnd_8387746 < baseStart_8387746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387789 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_8387789 : Nat := 118140960795 + 8387789 * 2 ^ 59
def prefixEnd_8387789 : Nat := 4983230072969 + 3 ^ 40 * 8387789 * 2
def baseEnd_8387789 : Nat := 4306967385495188470662767

theorem tailTrace_8387789 : CollatzResearch.WordTrace tailWord_8387789 prefixEnd_8387789 4306967385495188470662767 := by
  unfold tailWord_8387789
  simp only [CollatzResearch.WordTrace]
  refine ⟨305927797809480448157542421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203951865206320298771694947 305927797809480448157542421)
  ·
    refine ⟨14340365522319396007384801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 305927797809480448157542421 14340365522319396007384801)
    ·
      refine ⟨10755274141739547005538601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14340365522319396007384801 10755274141739547005538601)
      ·
        refine ⟨8066455606304660254153951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10755274141739547005538601 8066455606304660254153951)
        ·
          refine ⟨12099683409456990381230927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8066455606304660254153951 12099683409456990381230927)
          ·
            refine ⟨18149525114185485571846391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099683409456990381230927 18149525114185485571846391)
            ·
              refine ⟨27224287671278228357769587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18149525114185485571846391 27224287671278228357769587)
              ·
                refine ⟨40836431506917342536654381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27224287671278228357769587 40836431506917342536654381)
                ·
                  refine ⟨15313661815094003451245393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40836431506917342536654381 15313661815094003451245393)
                  ·
                    refine ⟨11485246361320502588434045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15313661815094003451245393 11485246361320502588434045)
                    ·
                      refine ⟨4306967385495188470662767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11485246361320502588434045 4306967385495188470662767)
                      ·
                        rfl

theorem cell23_8387789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_8387789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387789 prefixEnd_8387789 := by exact prefixLift 8387789
  have htrace : WordTrace (prefixWord ++ tailWord_8387789) baseStart_8387789 baseEnd_8387789 := by
    simpa [prefixWord, tailWord_8387789, baseEnd_8387789] using wordTrace_append hprefix tailTrace_8387789
  have hstable : (prefixWord ++ tailWord_8387789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387789).length < 2 ^ (prefixWord ++ tailWord_8387789).sum := by decide
  have hdescent : baseEnd_8387789 < baseStart_8387789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387791 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 4]
def baseStart_8387791 : Nat := 118140960795 + 8387791 * 2 ^ 59
def prefixEnd_8387791 : Nat := 4983230072969 + 3 ^ 40 * 8387791 * 2
def baseEnd_8387791 : Nat := 4306968412456497462837757

theorem tailTrace_8387791 : CollatzResearch.WordTrace tailWord_8387791 prefixEnd_8387791 4306968412456497462837757 := by
  unfold tailWord_8387791
  simp only [CollatzResearch.WordTrace]
  refine ⟨305927870755473202499115227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203951913836982134999410151 305927870755473202499115227)
  ·
    refine ⟨458891806133209803748672841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305927870755473202499115227 458891806133209803748672841)
    ·
      refine ⟨344168854599907352811504631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458891806133209803748672841 344168854599907352811504631)
      ·
        refine ⟨516253281899861029217256947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344168854599907352811504631 516253281899861029217256947)
        ·
          refine ⟨774379922849791543825885421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516253281899861029217256947 774379922849791543825885421)
          ·
            refine ⟨290392471068671828934707033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 774379922849791543825885421 290392471068671828934707033)
            ·
              refine ⟨217794353301503871701030275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290392471068671828934707033 217794353301503871701030275)
              ·
                refine ⟨326691529952255807551545413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217794353301503871701030275 326691529952255807551545413)
                ·
                  refine ⟨61254661866047963915914765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 326691529952255807551545413 61254661866047963915914765)
                  ·
                    refine ⟨22970498199767986468468037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61254661866047963915914765 22970498199767986468468037)
                    ·
                      refine ⟨4306968412456497462837757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22970498199767986468468037 4306968412456497462837757)
                      ·
                        rfl

theorem cell23_8387791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_8387791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387791 prefixEnd_8387791 := by exact prefixLift 8387791
  have htrace : WordTrace (prefixWord ++ tailWord_8387791) baseStart_8387791 baseEnd_8387791 := by
    simpa [prefixWord, tailWord_8387791, baseEnd_8387791] using wordTrace_append hprefix tailTrace_8387791
  have hstable : (prefixWord ++ tailWord_8387791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387791).length < 2 ^ (prefixWord ++ tailWord_8387791).sum := by decide
  have hdescent : baseEnd_8387791 < baseStart_8387791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387801 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 4, 6]
def baseStart_8387801 : Nat := 118140960795 + 8387801 * 2 ^ 59
def prefixEnd_8387801 : Nat := 4983230072969 + 3 ^ 40 * 8387801 * 2
def baseEnd_8387801 : Nat := 1435657849087680807904237

theorem tailTrace_8387801 : CollatzResearch.WordTrace tailWord_8387801 prefixEnd_8387801 1435657849087680807904237 := by
  unfold tailWord_8387801
  simp only [CollatzResearch.WordTrace]
  refine ⟨305928235485436974206979257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203952156990291316137986171 305928235485436974206979257)
  ·
    refine ⟨229446176614077730655234443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305928235485436974206979257 229446176614077730655234443)
    ·
      refine ⟨344169264921116595982851665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229446176614077730655234443 344169264921116595982851665)
      ·
        refine ⟨258126948690837446987138749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344169264921116595982851665 258126948690837446987138749)
        ·
          refine ⟨96797605759064042620177031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258126948690837446987138749 96797605759064042620177031)
          ·
            refine ⟨145196408638596063930265547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96797605759064042620177031 145196408638596063930265547)
            ·
              refine ⟨217794612957894095895398321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145196408638596063930265547 217794612957894095895398321)
              ·
                refine ⟨163345959718420571921548741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217794612957894095895398321 163345959718420571921548741)
                ·
                  refine ⟨30627367447203857235290389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163345959718420571921548741 30627367447203857235290389)
                  ·
                    refine ⟨1435657849087680807904237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30627367447203857235290389 1435657849087680807904237)
                    ·
                      rfl

theorem cell23_8387801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_8387801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387801 prefixEnd_8387801 := by exact prefixLift 8387801
  have htrace : WordTrace (prefixWord ++ tailWord_8387801) baseStart_8387801 baseEnd_8387801 := by
    simpa [prefixWord, tailWord_8387801, baseEnd_8387801] using wordTrace_append hprefix tailTrace_8387801
  have hstable : (prefixWord ++ tailWord_8387801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387801).length < 2 ^ (prefixWord ++ tailWord_8387801).sum := by decide
  have hdescent : baseEnd_8387801 < baseStart_8387801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387882 : List Nat := [3, 1, 4, 2, 1, 1, 2, 4, 5]
def baseStart_8387882 : Nat := 118140960795 + 8387882 * 2 ^ 59
def prefixEnd_8387882 : Nat := 4983230072969 + 3 ^ 40 * 8387882 * 2
def baseEnd_8387882 : Nat := 478557237688450734088871

theorem tailTrace_8387882 : CollatzResearch.WordTrace tailWord_8387882 prefixEnd_8387882 478557237688450734088871 := by
  unfold tailWord_8387882
  simp only [CollatzResearch.WordTrace]
  refine ⟨76482797449535881260169475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203954126532095683360451933 76482797449535881260169475)
  ·
    refine ⟨114724196174303821890254213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76482797449535881260169475 114724196174303821890254213)
    ·
      refine ⟨21510786782681966604422665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114724196174303821890254213 21510786782681966604422665)
      ·
        refine ⟨16133090087011474953316999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21510786782681966604422665 16133090087011474953316999)
        ·
          refine ⟨24199635130517212429975499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16133090087011474953316999 24199635130517212429975499)
          ·
            refine ⟨36299452695775818644963249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24199635130517212429975499 36299452695775818644963249)
            ·
              refine ⟨27224589521831863983722437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36299452695775818644963249 27224589521831863983722437)
              ·
                refine ⟨5104610535343474496947957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27224589521831863983722437 5104610535343474496947957)
                ·
                  refine ⟨478557237688450734088871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5104610535343474496947957 478557237688450734088871)
                  ·
                    rfl

theorem cell23_8387882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_8387882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387882 prefixEnd_8387882 := by exact prefixLift 8387882
  have htrace : WordTrace (prefixWord ++ tailWord_8387882) baseStart_8387882 baseEnd_8387882 := by
    simpa [prefixWord, tailWord_8387882, baseEnd_8387882] using wordTrace_append hprefix tailTrace_8387882
  have hstable : (prefixWord ++ tailWord_8387882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387882).length < 2 ^ (prefixWord ++ tailWord_8387882).sum := by decide
  have hdescent : baseEnd_8387882 < baseStart_8387882 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387898 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_8387898 : Nat := 118140960795 + 8387898 * 2 ^ 59
def prefixEnd_8387898 : Nat := 4983230072969 + 3 ^ 40 * 8387898 * 2
def baseEnd_8387898 : Nat := 4307023354886528544199765

theorem tailTrace_8387898 : CollatzResearch.WordTrace tailWord_8387898 prefixEnd_8387898 4307023354886528544199765 := by
  unfold tailWord_8387898
  simp only [CollatzResearch.WordTrace]
  refine ⟨76482943341521389943315087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203954515577390373182173565 76482943341521389943315087)
  ·
    refine ⟨114724415012282084914972631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76482943341521389943315087 114724415012282084914972631)
    ·
      refine ⟨172086622518423127372458947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114724415012282084914972631 172086622518423127372458947)
      ·
        refine ⟨258129933777634691058688421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172086622518423127372458947 258129933777634691058688421)
        ·
          refine ⟨48399362583306504573504079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258129933777634691058688421 48399362583306504573504079)
          ·
            refine ⟨72599043874959756860256119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48399362583306504573504079 72599043874959756860256119)
            ·
              refine ⟨108898565812439635290384179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72599043874959756860256119 108898565812439635290384179)
              ·
                refine ⟨163347848718659452935576269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108898565812439635290384179 163347848718659452935576269)
                ·
                  refine ⟨61255443269497294850841101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163347848718659452935576269 61255443269497294850841101)
                  ·
                    refine ⟨22970791226061485569065413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61255443269497294850841101 22970791226061485569065413)
                    ·
                      refine ⟨4307023354886528544199765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22970791226061485569065413 4307023354886528544199765)
                      ·
                        rfl

theorem cell23_8387898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_8387898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387898 prefixEnd_8387898 := by exact prefixLift 8387898
  have htrace : WordTrace (prefixWord ++ tailWord_8387898) baseStart_8387898 baseEnd_8387898 := by
    simpa [prefixWord, tailWord_8387898, baseEnd_8387898] using wordTrace_append hprefix tailTrace_8387898
  have hstable : (prefixWord ++ tailWord_8387898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387898).length < 2 ^ (prefixWord ++ tailWord_8387898).sum := by decide
  have hdescent : baseEnd_8387898 < baseStart_8387898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387933 : List Nat := [1, 4, 5, 1, 1, 1, 3, 2, 5]
def baseStart_8387933 : Nat := 118140960795 + 8387933 * 2 ^ 59
def prefixEnd_8387933 : Nat := 4983230072969 + 3 ^ 40 * 8387933 * 2
def baseEnd_8387933 : Nat := 478560147412159545251345

theorem tailTrace_8387933 : CollatzResearch.WordTrace tailWord_8387933 prefixEnd_8387933 478560147412159545251345 := by
  unfold tailWord_8387933
  simp only [CollatzResearch.WordTrace]
  refine ⟨305933049920958760750784453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203955366613972507167189635 305933049920958760750784453)
  ·
    refine ⟨57362446860179767640772085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305933049920958760750784453 57362446860179767640772085)
    ·
      refine ⟨5377729393141853216322383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57362446860179767640772085 5377729393141853216322383)
      ·
        refine ⟨8066594089712779824483575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5377729393141853216322383 8066594089712779824483575)
        ·
          refine ⟨12099891134569169736725363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8066594089712779824483575 12099891134569169736725363)
          ·
            refine ⟨18149836701853754605088045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099891134569169736725363 18149836701853754605088045)
            ·
              refine ⟨6806188763195157976908017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18149836701853754605088045 6806188763195157976908017)
              ·
                refine ⟨5104641572396368482681013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6806188763195157976908017 5104641572396368482681013)
                ·
                  refine ⟨478560147412159545251345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5104641572396368482681013 478560147412159545251345)
                  ·
                    rfl

theorem cell23_8387933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_8387933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387933 prefixEnd_8387933 := by exact prefixLift 8387933
  have htrace : WordTrace (prefixWord ++ tailWord_8387933) baseStart_8387933 baseEnd_8387933 := by
    simpa [prefixWord, tailWord_8387933, baseEnd_8387933] using wordTrace_append hprefix tailTrace_8387933
  have hstable : (prefixWord ++ tailWord_8387933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387933).length < 2 ^ (prefixWord ++ tailWord_8387933).sum := by decide
  have hdescent : baseEnd_8387933 < baseStart_8387933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387966 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_8387966 : Nat := 118140960795 + 8387966 * 2 ^ 59
def prefixEnd_8387966 : Nat := 4983230072969 + 3 ^ 40 * 8387966 * 2
def baseEnd_8387966 : Nat := 4307058271571034278149453

theorem tailTrace_8387966 : CollatzResearch.WordTrace tailWord_8387966 prefixEnd_8387966 4307058271571034278149453 := by
  unfold tailWord_8387966
  simp only [CollatzResearch.WordTrace]
  refine ⟨38241781691229900923341969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203956169019892804924490501 38241781691229900923341969)
  ·
    refine ⟨28681336268422425692506477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38241781691229900923341969 28681336268422425692506477)
    ·
      refine ⟨10755501100658409634689929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28681336268422425692506477 10755501100658409634689929)
      ·
        refine ⟨8066625825493807226017447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10755501100658409634689929 8066625825493807226017447)
        ·
          refine ⟨12099938738240710839026171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8066625825493807226017447 12099938738240710839026171)
          ·
            refine ⟨18149908107361066258539257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099938738240710839026171 18149908107361066258539257)
            ·
              refine ⟨13612431080520799693904443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18149908107361066258539257 13612431080520799693904443)
              ·
                refine ⟨20418646620781199540856665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13612431080520799693904443 20418646620781199540856665)
                ·
                  refine ⟨15313984965585899655642499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20418646620781199540856665 15313984965585899655642499)
                  ·
                    refine ⟨22970977448378849483463749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15313984965585899655642499 22970977448378849483463749)
                    ·
                      refine ⟨4307058271571034278149453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22970977448378849483463749 4307058271571034278149453)
                      ·
                        rfl

theorem cell23_8387966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_8387966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387966 prefixEnd_8387966 := by exact prefixLift 8387966
  have htrace : WordTrace (prefixWord ++ tailWord_8387966) baseStart_8387966 baseEnd_8387966 := by
    simpa [prefixWord, tailWord_8387966, baseEnd_8387966] using wordTrace_append hprefix tailTrace_8387966
  have hstable : (prefixWord ++ tailWord_8387966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387966).length < 2 ^ (prefixWord ++ tailWord_8387966).sum := by decide
  have hdescent : baseEnd_8387966 < baseStart_8387966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387969 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_8387969 : Nat := 118140960795 + 8387969 * 2 ^ 59
def prefixEnd_8387969 : Nat := 4983230072969 + 3 ^ 40 * 8387969 * 2
def baseEnd_8387969 : Nat := 4307059812012997766411939

theorem tailTrace_8387969 : CollatzResearch.WordTrace tailWord_8387969 prefixEnd_8387969 4307059812012997766411939 := by
  unfold tailWord_8387969
  simp only [CollatzResearch.WordTrace]
  refine ⟨305934362948828338899094961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203956241965885559266063307 305934362948828338899094961)
  ·
    refine ⟨229450772211621254174321221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305934362948828338899094961 229450772211621254174321221)
    ·
      refine ⟨43022019789678985157685229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229450772211621254174321221 43022019789678985157685229)
      ·
        refine ⟨16133257421129619434131961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43022019789678985157685229 16133257421129619434131961)
        ·
          refine ⟨12099943065847214575598971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16133257421129619434131961 12099943065847214575598971)
          ·
            refine ⟨18149914598770821863398457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099943065847214575598971 18149914598770821863398457)
            ·
              refine ⟨13612435949078116397548843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18149914598770821863398457 13612435949078116397548843)
              ·
                refine ⟨20418653923617174596323265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13612435949078116397548843 20418653923617174596323265)
                ·
                  refine ⟨15313990442712880947242449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20418653923617174596323265 15313990442712880947242449)
                  ·
                    refine ⟨11485492832034660710431837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15313990442712880947242449 11485492832034660710431837)
                    ·
                      refine ⟨4307059812012997766411939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11485492832034660710431837 4307059812012997766411939)
                      ·
                        rfl

theorem cell23_8387969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_8387969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387969 prefixEnd_8387969 := by exact prefixLift 8387969
  have htrace : WordTrace (prefixWord ++ tailWord_8387969) baseStart_8387969 baseEnd_8387969 := by
    simpa [prefixWord, tailWord_8387969, baseEnd_8387969] using wordTrace_append hprefix tailTrace_8387969
  have hstable : (prefixWord ++ tailWord_8387969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387969).length < 2 ^ (prefixWord ++ tailWord_8387969).sum := by decide
  have hdescent : baseEnd_8387969 < baseStart_8387969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388035 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 4]
def baseStart_8388035 : Nat := 118140960795 + 8388035 * 2 ^ 59
def prefixEnd_8388035 : Nat := 4983230072969 + 3 ^ 40 * 8388035 * 2
def baseEnd_8388035 : Nat := 4307093701736194508186635

theorem tailTrace_8388035 : CollatzResearch.WordTrace tailWord_8388035 prefixEnd_8388035 4307093701736194508186635 := by
  unfold tailWord_8388035
  simp only [CollatzResearch.WordTrace]
  refine ⟨305936770166589232170997559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203957846777726154780665039 305936770166589232170997559)
  ·
    refine ⟨458905155249883848256496339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305936770166589232170997559 458905155249883848256496339)
    ·
      refine ⟨688357732874825772384744509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458905155249883848256496339 688357732874825772384744509)
      ·
        refine ⟨258134149828059664644279191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 688357732874825772384744509 258134149828059664644279191)
        ·
          refine ⟨387201224742089496966418787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258134149828059664644279191 387201224742089496966418787)
          ·
            refine ⟨580801837113134245449628181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387201224742089496966418787 580801837113134245449628181)
            ·
              refine ⟨27225086114678167755451321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 580801837113134245449628181 27225086114678167755451321)
              ·
                refine ⟨20418814586008625816588491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27225086114678167755451321 20418814586008625816588491)
                ·
                  refine ⟨30628221879012938724882737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20418814586008625816588491 30628221879012938724882737)
                  ·
                    refine ⟨22971166409259704043662053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30628221879012938724882737 22971166409259704043662053)
                    ·
                      refine ⟨4307093701736194508186635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22971166409259704043662053 4307093701736194508186635)
                      ·
                        rfl

theorem cell23_8388035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_8388035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388035 prefixEnd_8388035 := by exact prefixLift 8388035
  have htrace : WordTrace (prefixWord ++ tailWord_8388035) baseStart_8388035 baseEnd_8388035 := by
    simpa [prefixWord, tailWord_8388035, baseEnd_8388035] using wordTrace_append hprefix tailTrace_8388035
  have hstable : (prefixWord ++ tailWord_8388035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388035).length < 2 ^ (prefixWord ++ tailWord_8388035).sum := by decide
  have hdescent : baseEnd_8388035 < baseStart_8388035 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388036 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_8388036 : Nat := 118140960795 + 8388036 * 2 ^ 59
def prefixEnd_8388036 : Nat := 4983230072969 + 3 ^ 40 * 8388036 * 2
def baseEnd_8388036 : Nat := 1435698071738949668091377

theorem tailTrace_8388036 : CollatzResearch.WordTrace tailWord_8388036 prefixEnd_8388036 1435698071738949668091377 := by
  unfold tailWord_8388036
  simp only [CollatzResearch.WordTrace]
  refine ⟨152968403319792804670891981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203957871093057072894522641 152968403319792804670891981)
  ·
    refine ⟨57363151244922301751584493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152968403319792804670891981 57363151244922301751584493)
    ·
      refine ⟨21511181716845863156844185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57363151244922301751584493 21511181716845863156844185)
      ·
        refine ⟨16133386287634397367633139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21511181716845863156844185 16133386287634397367633139)
        ·
          refine ⟨24200079431451596051449709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16133386287634397367633139 24200079431451596051449709)
          ·
            refine ⟨9075029786794348519293641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24200079431451596051449709 9075029786794348519293641)
            ·
              refine ⟨6806272340095761389470231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9075029786794348519293641 6806272340095761389470231)
              ·
                refine ⟨10209408510143642084205347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6806272340095761389470231 10209408510143642084205347)
                ·
                  refine ⟨15314112765215463126308021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10209408510143642084205347 15314112765215463126308021)
                  ·
                    refine ⟨1435698071738949668091377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15314112765215463126308021 1435698071738949668091377)
                    ·
                      rfl

theorem cell23_8388036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_8388036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388036 prefixEnd_8388036 := by exact prefixLift 8388036
  have htrace : WordTrace (prefixWord ++ tailWord_8388036) baseStart_8388036 baseEnd_8388036 := by
    simpa [prefixWord, tailWord_8388036, baseEnd_8388036] using wordTrace_append hprefix tailTrace_8388036
  have hstable : (prefixWord ++ tailWord_8388036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388036).length < 2 ^ (prefixWord ++ tailWord_8388036).sum := by decide
  have hdescent : baseEnd_8388036 < baseStart_8388036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388055 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 3]
def baseStart_8388055 : Nat := 118140960795 + 8388055 * 2 ^ 59
def prefixEnd_8388055 : Nat := 4983230072969 + 3 ^ 40 * 8388055 * 2
def baseEnd_8388055 : Nat := 4307103971349284429936543

theorem tailTrace_8388055 : CollatzResearch.WordTrace tailWord_8388055 prefixEnd_8388055 4307103971349284429936543 := by
  unfold tailWord_8388055
  simp only [CollatzResearch.WordTrace]
  refine ⟨305937499626516775586725619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203958333084344517057817079 305937499626516775586725619)
  ·
    refine ⟨458906249439775163380088429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305937499626516775586725619 458906249439775163380088429)
    ·
      refine ⟨172089843539915686267533161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458906249439775163380088429 172089843539915686267533161)
      ·
        refine ⟨129067382654936764700649871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172089843539915686267533161 129067382654936764700649871)
        ·
          refine ⟨193601073982405147050974807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129067382654936764700649871 193601073982405147050974807)
          ·
            refine ⟨290401610973607720576462211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193601073982405147050974807 290401610973607720576462211)
            ·
              refine ⟨435602416460411580864693317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290401610973607720576462211 435602416460411580864693317)
              ·
                refine ⟨81675453086327171412129997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435602416460411580864693317 81675453086327171412129997)
                ·
                  refine ⟨30628294907372689279548749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81675453086327171412129997 30628294907372689279548749)
                  ·
                    refine ⟨11485610590264758479830781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30628294907372689279548749 11485610590264758479830781)
                    ·
                      refine ⟨4307103971349284429936543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11485610590264758479830781 4307103971349284429936543)
                      ·
                        rfl

theorem cell23_8388055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_8388055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388055 prefixEnd_8388055 := by exact prefixLift 8388055
  have htrace : WordTrace (prefixWord ++ tailWord_8388055) baseStart_8388055 baseEnd_8388055 := by
    simpa [prefixWord, tailWord_8388055, baseEnd_8388055] using wordTrace_append hprefix tailTrace_8388055
  have hstable : (prefixWord ++ tailWord_8388055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388055).length < 2 ^ (prefixWord ++ tailWord_8388055).sum := by decide
  have hdescent : baseEnd_8388055 < baseStart_8388055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388056 : List Nat := [2, 1, 2, 2, 2, 1, 4, 4, 1, 2, 2]
def baseStart_8388056 : Nat := 118140960795 + 8388056 * 2 ^ 59
def prefixEnd_8388056 : Nat := 4983230072969 + 3 ^ 40 * 8388056 * 2
def baseEnd_8388056 : Nat := 4307104484829938926024039

theorem tailTrace_8388056 : CollatzResearch.WordTrace tailWord_8388056 prefixEnd_8388056 4307104484829938926024039 := by
  unfold tailWord_8388056
  simp only [CollatzResearch.WordTrace]
  refine ⟨152968768049756576378756011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203958357399675435171674681 152968768049756576378756011)
  ·
    refine ⟨229453152074634864568134017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152968768049756576378756011 229453152074634864568134017)
    ·
      refine ⟨172089864055976148426100513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229453152074634864568134017 172089864055976148426100513)
      ·
        refine ⟨129067398041982111319575385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172089864055976148426100513 129067398041982111319575385)
        ·
          refine ⟨96800548531486583489681539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129067398041982111319575385 96800548531486583489681539)
          ·
            refine ⟨145200822797229875234522309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96800548531486583489681539 145200822797229875234522309)
            ·
              refine ⟨27225154274480601606472933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145200822797229875234522309 27225154274480601606472933)
              ·
                refine ⟨5104716426465112801213675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27225154274480601606472933 5104716426465112801213675)
                ·
                  refine ⟨7657074639697669201820513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5104716426465112801213675 7657074639697669201820513)
                  ·
                    refine ⟨5742805979773251901365385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7657074639697669201820513 5742805979773251901365385)
                    ·
                      refine ⟨4307104484829938926024039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742805979773251901365385 4307104484829938926024039)
                      ·
                        rfl

theorem cell23_8388056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_8388056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388056 prefixEnd_8388056 := by exact prefixLift 8388056
  have htrace : WordTrace (prefixWord ++ tailWord_8388056) baseStart_8388056 baseEnd_8388056 := by
    simpa [prefixWord, tailWord_8388056, baseEnd_8388056] using wordTrace_append hprefix tailTrace_8388056
  have hstable : (prefixWord ++ tailWord_8388056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388056).length < 2 ^ (prefixWord ++ tailWord_8388056).sum := by decide
  have hdescent : baseEnd_8388056 < baseStart_8388056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388069 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 4]
def baseStart_8388069 : Nat := 118140960795 + 8388069 * 2 ^ 59
def prefixEnd_8388069 : Nat := 4983230072969 + 3 ^ 40 * 8388069 * 2
def baseEnd_8388069 : Nat := 4307111160078447375161479

theorem tailTrace_8388069 : CollatzResearch.WordTrace tailWord_8388069 prefixEnd_8388069 4307111160078447375161479 := by
  unfold tailWord_8388069
  simp only [CollatzResearch.WordTrace]
  refine ⟨305938010248466055977735261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203958673498977370651823507 305938010248466055977735261)
  ·
    refine ⟨114726753843174770991650723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305938010248466055977735261 114726753843174770991650723)
    ·
      refine ⟨172090130764762156487476085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114726753843174770991650723 172090130764762156487476085)
      ·
        refine ⟨16133449759196452170700883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172090130764762156487476085 16133449759196452170700883)
        ·
          refine ⟨24200174638794678256051325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16133449759196452170700883 24200174638794678256051325)
          ·
            refine ⟨9075065489548004346019247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24200174638794678256051325 9075065489548004346019247)
            ·
              refine ⟨13612598234322006519028871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9075065489548004346019247 13612598234322006519028871)
              ·
                refine ⟨20418897351483009778543307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13612598234322006519028871 20418897351483009778543307)
                ·
                  refine ⟨30628346027224514667814961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20418897351483009778543307 30628346027224514667814961)
                  ·
                    refine ⟨22971259520418386000861221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30628346027224514667814961 22971259520418386000861221)
                    ·
                      refine ⟨4307111160078447375161479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22971259520418386000861221 4307111160078447375161479)
                      ·
                        rfl

theorem cell23_8388069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_8388069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388069 prefixEnd_8388069 := by exact prefixLift 8388069
  have htrace : WordTrace (prefixWord ++ tailWord_8388069) baseStart_8388069 baseEnd_8388069 := by
    simpa [prefixWord, tailWord_8388069, baseEnd_8388069] using wordTrace_append hprefix tailTrace_8388069
  have hstable : (prefixWord ++ tailWord_8388069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388069).length < 2 ^ (prefixWord ++ tailWord_8388069).sum := by decide
  have hdescent : baseEnd_8388069 < baseStart_8388069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388150 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_8388150 : Nat := 118140960795 + 8388150 * 2 ^ 59
def prefixEnd_8388150 : Nat := 4983230072969 + 3 ^ 40 * 8388150 * 2
def baseEnd_8388150 : Nat := 4307152752011461558248607

theorem tailTrace_8388150 : CollatzResearch.WordTrace tailWord_8388150 prefixEnd_8388150 4307152752011461558248607 := by
  unfold tailWord_8388150
  simp only [CollatzResearch.WordTrace]
  refine ⟨19121310285073287925714619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203960643040781737874289269 19121310285073287925714619)
  ·
    refine ⟨28681965427609931888571929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19121310285073287925714619 28681965427609931888571929)
    ·
      refine ⟨21511474070707448916428947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28681965427609931888571929 21511474070707448916428947)
      ·
        refine ⟨32267211106061173374643421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21511474070707448916428947 32267211106061173374643421)
        ·
          refine ⟨12100204164772940015491283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32267211106061173374643421 12100204164772940015491283)
          ·
            refine ⟨18150306247159410023236925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12100204164772940015491283 18150306247159410023236925)
            ·
              refine ⟨6806364842684778758713847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18150306247159410023236925 6806364842684778758713847)
              ·
                refine ⟨10209547264027168138070771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6806364842684778758713847 10209547264027168138070771)
                ·
                  refine ⟨15314320896040752207106157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10209547264027168138070771 15314320896040752207106157)
                  ·
                    refine ⟨5742870336015282077664809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15314320896040752207106157 5742870336015282077664809)
                    ·
                      refine ⟨4307152752011461558248607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742870336015282077664809 4307152752011461558248607)
                      ·
                        rfl

theorem cell23_8388150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_8388150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388150 prefixEnd_8388150 := by exact prefixLift 8388150
  have htrace : WordTrace (prefixWord ++ tailWord_8388150) baseStart_8388150 baseEnd_8388150 := by
    simpa [prefixWord, tailWord_8388150, baseEnd_8388150] using wordTrace_append hprefix tailTrace_8388150
  have hstable : (prefixWord ++ tailWord_8388150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388150).length < 2 ^ (prefixWord ++ tailWord_8388150).sum := by decide
  have hdescent : baseEnd_8388150 < baseStart_8388150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388229 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 3, 4]
def baseStart_8388229 : Nat := 118140960795 + 8388229 * 2 ^ 59
def prefixEnd_8388229 : Nat := 4983230072969 + 3 ^ 40 * 8388229 * 2
def baseEnd_8388229 : Nat := 1435731105661055583053581

theorem tailTrace_8388229 : CollatzResearch.WordTrace tailWord_8388229 prefixEnd_8388229 1435731105661055583053581 := by
  unfold tailWord_8388229
  simp only [CollatzResearch.WordTrace]
  refine ⟨305943845927886403303559741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203962563951924268869039827 305943845927886403303559741)
  ·
    refine ⟨114728942222957401238834903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305943845927886403303559741 114728942222957401238834903)
    ·
      refine ⟨172093413334436101858252355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114728942222957401238834903 172093413334436101858252355)
      ·
        refine ⟨258140120001654152787378533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172093413334436101858252355 258140120001654152787378533)
        ·
          refine ⟨48401272500310153647633475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258140120001654152787378533 48401272500310153647633475)
          ·
            refine ⟨72601908750465230471450213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48401272500310153647633475 72601908750465230471450213)
            ·
              refine ⟨13612857890712230713396915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72601908750465230471450213 13612857890712230713396915)
              ·
                refine ⟨20419286836068346070095373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13612857890712230713396915 20419286836068346070095373)
                ·
                  refine ⟨7657232563525629776285765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20419286836068346070095373 7657232563525629776285765)
                  ·
                    refine ⟨1435731105661055583053581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7657232563525629776285765 1435731105661055583053581)
                    ·
                      rfl

theorem cell23_8388229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_8388229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388229 prefixEnd_8388229 := by exact prefixLift 8388229
  have htrace : WordTrace (prefixWord ++ tailWord_8388229) baseStart_8388229 baseEnd_8388229 := by
    simpa [prefixWord, tailWord_8388229, baseEnd_8388229] using wordTrace_append hprefix tailTrace_8388229
  have hstable : (prefixWord ++ tailWord_8388229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388229).length < 2 ^ (prefixWord ++ tailWord_8388229).sum := by decide
  have hdescent : baseEnd_8388229 < baseStart_8388229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388306 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_8388306 : Nat := 118140960795 + 8388306 * 2 ^ 59
def prefixEnd_8388306 : Nat := 4983230072969 + 3 ^ 40 * 8388306 * 2
def baseEnd_8388306 : Nat := 1435744284997854315965963

theorem tailTrace_8388306 : CollatzResearch.WordTrace tailWord_8388306 prefixEnd_8388306 1435744284997854315965963 := by
  unfold tailWord_8388306
  simp only [CollatzResearch.WordTrace]
  refine ⟨76486663587151861363528193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203964436232404963636075181 76486663587151861363528193)
  ·
    refine ⟨57364997690363896022646145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76486663587151861363528193 57364997690363896022646145)
    ·
      refine ⟨43023748267772922016984609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57364997690363896022646145 43023748267772922016984609)
      ·
        refine ⟨32267811200829691512738457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43023748267772922016984609 32267811200829691512738457)
        ·
          refine ⟨24200858400622268634553843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32267811200829691512738457 24200858400622268634553843)
          ·
            refine ⟨36301287600933402951830765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24200858400622268634553843 36301287600933402951830765)
            ·
              refine ⟨13612982850350026106936537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36301287600933402951830765 13612982850350026106936537)
              ·
                refine ⟨10209737137762519580202403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13612982850350026106936537 10209737137762519580202403)
                ·
                  refine ⟨15314605706643779370303605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10209737137762519580202403 15314605706643779370303605)
                  ·
                    refine ⟨1435744284997854315965963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15314605706643779370303605 1435744284997854315965963)
                    ·
                      rfl

theorem cell23_8388306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_8388306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388306 prefixEnd_8388306 := by exact prefixLift 8388306
  have htrace : WordTrace (prefixWord ++ tailWord_8388306) baseStart_8388306 baseEnd_8388306 := by
    simpa [prefixWord, tailWord_8388306, baseEnd_8388306] using wordTrace_append hprefix tailTrace_8388306
  have hstable : (prefixWord ++ tailWord_8388306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388306).length < 2 ^ (prefixWord ++ tailWord_8388306).sum := by decide
  have hdescent : baseEnd_8388306 < baseStart_8388306 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388323 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 1, 5]
def baseStart_8388323 : Nat := 118140960795 + 8388323 * 2 ^ 59
def prefixEnd_8388323 : Nat := 4983230072969 + 3 ^ 40 * 8388323 * 2
def baseEnd_8388323 : Nat := 1435747194721563127128437

theorem tailTrace_8388323 : CollatzResearch.WordTrace tailWord_8388323 prefixEnd_8388323 1435747194721563127128437 := by
  unfold tailWord_8388323
  simp only [CollatzResearch.WordTrace]
  refine ⟨305947274389545857357481623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203964849593030571571654415 305947274389545857357481623)
  ·
    refine ⟨458920911584318786036222435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305947274389545857357481623 458920911584318786036222435)
    ·
      refine ⟨688381367376478179054333653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458920911584318786036222435 688381367376478179054333653)
      ·
        refine ⟨16133938297886207321585945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 688381367376478179054333653 16133938297886207321585945)
        ·
          refine ⟨12100453723414655491189459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16133938297886207321585945 12100453723414655491189459)
          ·
            refine ⟨18150680585121983236784189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12100453723414655491189459 18150680585121983236784189)
            ·
              refine ⟨6806505219420743713794071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18150680585121983236784189 6806505219420743713794071)
              ·
                refine ⟨10209757829131115570691107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6806505219420743713794071 10209757829131115570691107)
                ·
                  refine ⟨15314636743696673356036661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10209757829131115570691107 15314636743696673356036661)
                  ·
                    refine ⟨1435747194721563127128437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15314636743696673356036661 1435747194721563127128437)
                    ·
                      rfl

theorem cell23_8388323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 5].length) (baseStart_8388323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388323 prefixEnd_8388323 := by exact prefixLift 8388323
  have htrace : WordTrace (prefixWord ++ tailWord_8388323) baseStart_8388323 baseEnd_8388323 := by
    simpa [prefixWord, tailWord_8388323, baseEnd_8388323] using wordTrace_append hprefix tailTrace_8388323
  have hstable : (prefixWord ++ tailWord_8388323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388323).length < 2 ^ (prefixWord ++ tailWord_8388323).sum := by decide
  have hdescent : baseEnd_8388323 < baseStart_8388323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388356 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_8388356 : Nat := 118140960795 + 8388356 * 2 ^ 59
def prefixEnd_8388356 : Nat := 4983230072969 + 3 ^ 40 * 8388356 * 2
def baseEnd_8388356 : Nat := 4307258529026287752272659

theorem tailTrace_8388356 : CollatzResearch.WordTrace tailWord_8388356 prefixEnd_8388356 4307258529026287752272659 := by
  unfold tailWord_8388356
  simp only [CollatzResearch.WordTrace]
  refine ⟨152974238999213151996716461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203965651998950869328955281 152974238999213151996716461)
  ·
    refine ⟨57365339624704931998768673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152974238999213151996716461 57365339624704931998768673)
    ·
      refine ⟨43024004718528698999076505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57365339624704931998768673 43024004718528698999076505)
      ·
        refine ⟨32268003538896524249307379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43024004718528698999076505 32268003538896524249307379)
        ·
          refine ⟨48402005308344786373961069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32268003538896524249307379 48402005308344786373961069)
          ·
            refine ⟨18150751990629294890235401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48402005308344786373961069 18150751990629294890235401)
            ·
              refine ⟨13613063992971971167676551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18150751990629294890235401 13613063992971971167676551)
              ·
                refine ⟨20419595989457956751514827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13613063992971971167676551 20419595989457956751514827)
                ·
                  refine ⟨30629393984186935127272241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20419595989457956751514827 30629393984186935127272241)
                  ·
                    refine ⟨22972045488140201345454181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30629393984186935127272241 22972045488140201345454181)
                    ·
                      refine ⟨4307258529026287752272659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22972045488140201345454181 4307258529026287752272659)
                      ·
                        rfl

theorem cell23_8388356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_8388356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388356 prefixEnd_8388356 := by exact prefixLift 8388356
  have htrace : WordTrace (prefixWord ++ tailWord_8388356) baseStart_8388356 baseEnd_8388356 := by
    simpa [prefixWord, tailWord_8388356, baseEnd_8388356] using wordTrace_append hprefix tailTrace_8388356
  have hstable : (prefixWord ++ tailWord_8388356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388356).length < 2 ^ (prefixWord ++ tailWord_8388356).sum := by decide
  have hdescent : baseEnd_8388356 < baseStart_8388356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388410 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3]
def baseStart_8388410 : Nat := 118140960795 + 8388410 * 2 ^ 59
def prefixEnd_8388410 : Nat := 4983230072969 + 3 ^ 40 * 8388410 * 2
def baseEnd_8388410 : Nat := 4307286256981630540997411

theorem tailTrace_8388410 : CollatzResearch.WordTrace tailWord_8388410 prefixEnd_8388410 4307286256981630540997411 := by
  unfold tailWord_8388410
  simp only [CollatzResearch.WordTrace]
  refine ⟨76487611885057667803974671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203966965026820447477265789 76487611885057667803974671)
  ·
    refine ⟨114731417827586501705962007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76487611885057667803974671 114731417827586501705962007)
    ·
      refine ⟨172097126741379752558943011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114731417827586501705962007 172097126741379752558943011)
      ·
        refine ⟨258145690112069628838414517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172097126741379752558943011 258145690112069628838414517)
        ·
          refine ⟨24201158448006527703601361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 258145690112069628838414517 24201158448006527703601361)
          ·
            refine ⟨18150868836004895777701021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24201158448006527703601361 18150868836004895777701021)
            ·
              refine ⟨6806575813501835916637883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18150868836004895777701021 6806575813501835916637883)
              ·
                refine ⟨10209863720252753874956825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6806575813501835916637883 10209863720252753874956825)
                ·
                  refine ⟨7657397790189565406217619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10209863720252753874956825 7657397790189565406217619)
                  ·
                    refine ⟨11486096685284348109326429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7657397790189565406217619 11486096685284348109326429)
                    ·
                      refine ⟨4307286256981630540997411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11486096685284348109326429 4307286256981630540997411)
                      ·
                        rfl

theorem cell23_8388410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3].length) (baseStart_8388410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388410 prefixEnd_8388410 := by exact prefixLift 8388410
  have htrace : WordTrace (prefixWord ++ tailWord_8388410) baseStart_8388410 baseEnd_8388410 := by
    simpa [prefixWord, tailWord_8388410, baseEnd_8388410] using wordTrace_append hprefix tailTrace_8388410
  have hstable : (prefixWord ++ tailWord_8388410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388410).length < 2 ^ (prefixWord ++ tailWord_8388410).sum := by decide
  have hdescent : baseEnd_8388410 < baseStart_8388410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388433 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 4, 2, 2]
def baseStart_8388433 : Nat := 118140960795 + 8388433 * 2 ^ 59
def prefixEnd_8388433 : Nat := 4983230072969 + 3 ^ 40 * 8388433 * 2
def baseEnd_8388433 : Nat := 4307298067036683951009805

theorem tailTrace_8388433 : CollatzResearch.WordTrace tailWord_8388433 prefixEnd_8388433 4307298067036683951009805 := by
  unfold tailWord_8388433
  simp only [CollatzResearch.WordTrace]
  refine ⟨305951286419147346143985953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203967524279431564095990635 305951286419147346143985953)
  ·
    refine ⟨229463464814360509607989465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305951286419147346143985953 229463464814360509607989465)
    ·
      refine ⟨172097598610770382205992099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229463464814360509607989465 172097598610770382205992099)
      ·
        refine ⟨258146397916155573308988149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172097598610770382205992099 258146397916155573308988149)
        ·
          refine ⟨24201224804639584997717639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 258146397916155573308988149 24201224804639584997717639)
          ·
            refine ⟨36301837206959377496576459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24201224804639584997717639 36301837206959377496576459)
            ·
              refine ⟨54452755810439066244864689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36301837206959377496576459 54452755810439066244864689)
              ·
                refine ⟨40839566857829299683648517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54452755810439066244864689 40839566857829299683648517)
                ·
                  refine ⟨7657418785842993690684097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40839566857829299683648517 7657418785842993690684097)
                  ·
                    refine ⟨5743064089382245268013073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7657418785842993690684097 5743064089382245268013073)
                    ·
                      refine ⟨4307298067036683951009805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5743064089382245268013073 4307298067036683951009805)
                      ·
                        rfl

theorem cell23_8388433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 2, 2].length) (baseStart_8388433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388433 prefixEnd_8388433 := by exact prefixLift 8388433
  have htrace : WordTrace (prefixWord ++ tailWord_8388433) baseStart_8388433 baseEnd_8388433 := by
    simpa [prefixWord, tailWord_8388433, baseEnd_8388433] using wordTrace_append hprefix tailTrace_8388433
  have hstable : (prefixWord ++ tailWord_8388433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388433).length < 2 ^ (prefixWord ++ tailWord_8388433).sum := by decide
  have hdescent : baseEnd_8388433 < baseStart_8388433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388436 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_8388436 : Nat := 118140960795 + 8388436 * 2 ^ 59
def prefixEnd_8388436 : Nat := 4983230072969 + 3 ^ 40 * 8388436 * 2
def baseEnd_8388436 : Nat := 4307299607478647439272291

theorem tailTrace_8388436 : CollatzResearch.WordTrace tailWord_8388436 prefixEnd_8388436 4307299607478647439272291 := by
  unfold tailWord_8388436
  simp only [CollatzResearch.WordTrace]
  refine ⟨152975697919068238828172581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203967597225424318437563441 152975697919068238828172581)
  ·
    refine ⟨28682943359825294780282359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152975697919068238828172581 28682943359825294780282359)
    ·
      refine ⟨43024415039737942170423539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28682943359825294780282359 43024415039737942170423539)
      ·
        refine ⟨64536622559606913255635309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43024415039737942170423539 64536622559606913255635309)
        ·
          refine ⟨24201233459852592470863241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64536622559606913255635309 24201233459852592470863241)
          ·
            refine ⟨18150925094889444353147431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24201233459852592470863241 18150925094889444353147431)
            ·
              refine ⟨27226387642334166529721147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18150925094889444353147431 27226387642334166529721147)
              ·
                refine ⟨40839581463501249794581721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27226387642334166529721147 40839581463501249794581721)
                ·
                  refine ⟨30629686097625937345936291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40839581463501249794581721 30629686097625937345936291)
                  ·
                    refine ⟨45944529146438906018904437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30629686097625937345936291 45944529146438906018904437)
                    ·
                      refine ⟨4307299607478647439272291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45944529146438906018904437 4307299607478647439272291)
                      ·
                        rfl

theorem cell23_8388436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_8388436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388436 prefixEnd_8388436 := by exact prefixLift 8388436
  have htrace : WordTrace (prefixWord ++ tailWord_8388436) baseStart_8388436 baseEnd_8388436 := by
    simpa [prefixWord, tailWord_8388436, baseEnd_8388436] using wordTrace_append hprefix tailTrace_8388436
  have hstable : (prefixWord ++ tailWord_8388436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388436).length < 2 ^ (prefixWord ++ tailWord_8388436).sum := by decide
  have hdescent : baseEnd_8388436 < baseStart_8388436 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388450 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_8388450 : Nat := 118140960795 + 8388450 * 2 ^ 59
def prefixEnd_8388450 : Nat := 4983230072969 + 3 ^ 40 * 8388450 * 2
def baseEnd_8388450 : Nat := 4307306796207810384497227

theorem tailTrace_8388450 : CollatzResearch.WordTrace tailWord_8388450 prefixEnd_8388450 4307306796207810384497227 := by
  unfold tailWord_8388450
  simp only [CollatzResearch.WordTrace]
  refine ⟨76487976615021439511838701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203967937640057172031569869 76487976615021439511838701)
  ·
    refine ⟨28682991230633039816939513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76487976615021439511838701 28682991230633039816939513)
    ·
      refine ⟨21512243422974779862704635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28682991230633039816939513 21512243422974779862704635)
      ·
        refine ⟨32268365134462169794056953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21512243422974779862704635 32268365134462169794056953)
        ·
          refine ⟨24201273850846627345542715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32268365134462169794056953 24201273850846627345542715)
          ·
            refine ⟨36301910776269941018314073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24201273850846627345542715 36301910776269941018314073)
            ·
              refine ⟨27226433082202455763735555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36301910776269941018314073 27226433082202455763735555)
              ·
                refine ⟨40839649623303683645603333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27226433082202455763735555 40839649623303683645603333)
                ·
                  refine ⟨7657434304369440683550625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40839649623303683645603333 7657434304369440683550625)
                  ·
                    refine ⟨5743075728277080512662969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7657434304369440683550625 5743075728277080512662969)
                    ·
                      refine ⟨4307306796207810384497227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5743075728277080512662969 4307306796207810384497227)
                      ·
                        rfl

theorem cell23_8388450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_8388450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388450 prefixEnd_8388450 := by exact prefixLift 8388450
  have htrace : WordTrace (prefixWord ++ tailWord_8388450) baseStart_8388450 baseEnd_8388450 := by
    simpa [prefixWord, tailWord_8388450, baseEnd_8388450] using wordTrace_append hprefix tailTrace_8388450
  have hstable : (prefixWord ++ tailWord_8388450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388450).length < 2 ^ (prefixWord ++ tailWord_8388450).sum := by decide
  have hdescent : baseEnd_8388450 < baseStart_8388450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388533 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 3, 4]
def baseStart_8388533 : Nat := 118140960795 + 8388533 * 2 ^ 59
def prefixEnd_8388533 : Nat := 4983230072969 + 3 ^ 40 * 8388533 * 2
def baseEnd_8388533 : Nat := 1435783138367377853253115

theorem tailTrace_8388533 : CollatzResearch.WordTrace tailWord_8388533 prefixEnd_8388533 1435783138367377853253115 := by
  unfold tailWord_8388533
  simp only [CollatzResearch.WordTrace]
  refine ⟨305954933718785063222626253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203969955812523375481750835 305954933718785063222626253)
  ·
    refine ⟨114733100144544398708484845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305954933718785063222626253 114733100144544398708484845)
    ·
      refine ⟨43024912554204149515681817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114733100144544398708484845 43024912554204149515681817)
      ·
        refine ⟨32268684415653112136761363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43024912554204149515681817 32268684415653112136761363)
        ·
          refine ⟨48403026623479668205142045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32268684415653112136761363 48403026623479668205142045)
          ·
            refine ⟨18151134983804875576928267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48403026623479668205142045 18151134983804875576928267)
            ·
              refine ⟨27226702475707313365392401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18151134983804875576928267 27226702475707313365392401)
              ·
                refine ⟨20420026856780485024044301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27226702475707313365392401 20420026856780485024044301)
                ·
                  refine ⟨7657510071292681884016613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20420026856780485024044301 7657510071292681884016613)
                  ·
                    refine ⟨1435783138367377853253115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7657510071292681884016613 1435783138367377853253115)
                    ·
                      rfl

theorem cell23_8388533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_8388533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388533 prefixEnd_8388533 := by exact prefixLift 8388533
  have htrace : WordTrace (prefixWord ++ tailWord_8388533) baseStart_8388533 baseEnd_8388533 := by
    simpa [prefixWord, tailWord_8388533, baseEnd_8388533] using wordTrace_append hprefix tailTrace_8388533
  have hstable : (prefixWord ++ tailWord_8388533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388533).length < 2 ^ (prefixWord ++ tailWord_8388533).sum := by decide
  have hdescent : baseEnd_8388533 < baseStart_8388533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8388590 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_8388590 : Nat := 118140960795 + 8388590 * 2 ^ 59
def prefixEnd_8388590 : Nat := 4983230072969 + 3 ^ 40 * 8388590 * 2
def baseEnd_8388590 : Nat := 4307378683499439836746583

theorem tailTrace_8388590 : CollatzResearch.WordTrace tailWord_8388590 prefixEnd_8388590 4307378683499439836746583 := by
  unfold tailWord_8388590
  simp only [CollatzResearch.WordTrace]
  refine ⟨38244626584947320244681403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203971341786385707971634149 38244626584947320244681403)
  ·
    refine ⟨57366939877420980367022105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38244626584947320244681403 57366939877420980367022105)
    ·
      refine ⟨43025204908065735275266579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57366939877420980367022105 43025204908065735275266579)
      ·
        refine ⟨64537807362098602912899869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43025204908065735275266579 64537807362098602912899869)
        ·
          refine ⟨24201677760786976092337451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64537807362098602912899869 24201677760786976092337451)
          ·
            refine ⟨36302516641180464138506177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24201677760786976092337451 36302516641180464138506177)
            ·
              refine ⟨27226887480885348103879633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36302516641180464138506177 27226887480885348103879633)
              ·
                refine ⟨20420165610664011077909725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27226887480885348103879633 20420165610664011077909725)
                ·
                  refine ⟨7657562103999004154216147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20420165610664011077909725 7657562103999004154216147)
                  ·
                    refine ⟨11486343155998506231324221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7657562103999004154216147 11486343155998506231324221)
                    ·
                      refine ⟨4307378683499439836746583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11486343155998506231324221 4307378683499439836746583)
                      ·
                        rfl

theorem cell23_8388590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_8388590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8388590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8388590 prefixEnd_8388590 := by exact prefixLift 8388590
  have htrace : WordTrace (prefixWord ++ tailWord_8388590) baseStart_8388590 baseEnd_8388590 := by
    simpa [prefixWord, tailWord_8388590, baseEnd_8388590] using wordTrace_append hprefix tailTrace_8388590
  have hstable : (prefixWord ++ tailWord_8388590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8388590).length < 2 ^ (prefixWord ++ tailWord_8388590).sum := by decide
  have hdescent : baseEnd_8388590 < baseStart_8388590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8388590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
