import V185TrunkScan22Chunk263

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2354760 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 11]
def baseStart_2354760 : Nat := 118140960795 + 2354760 * 2 ^ 59
def prefixEnd_2354760 : Nat := 4983230072969 + 3 ^ 40 * 2354760 * 2
def baseEnd_2354760 : Nat := 268694156884736049860147

theorem tailTrace_2354760 : CollatzResearch.WordTrace tailWord_2354760 prefixEnd_2354760 268694156884736049860147 := by
  unfold tailWord_2354760
  simp only [CollatzResearch.WordTrace]
  refine ⟨42942576474557077917718867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57256768632742770556958489 42942576474557077917718867)
  ·
    refine ⟨64413864711835616876578301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42942576474557077917718867 64413864711835616876578301)
    ·
      refine ⟨24155199266938356328716863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64413864711835616876578301 24155199266938356328716863)
      ·
        refine ⟨36232798900407534493075295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24155199266938356328716863 36232798900407534493075295)
        ·
          refine ⟨54349198350611301739612943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36232798900407534493075295 54349198350611301739612943)
          ·
            refine ⟨81523797525916952609419415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54349198350611301739612943 81523797525916952609419415)
            ·
              refine ⟨122285696288875428914129123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81523797525916952609419415 122285696288875428914129123)
              ·
                refine ⟨183428544433313143371193685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122285696288875428914129123 183428544433313143371193685)
                ·
                  refine ⟨268694156884736049860147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 183428544433313143371193685 268694156884736049860147)
                  ·
                    rfl

theorem cell22_2354760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_2354760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354760 prefixEnd_2354760 := by exact prefixLift 2354760
  have htrace : WordTrace (prefixWord ++ tailWord_2354760) baseStart_2354760 baseEnd_2354760 := by
    simpa [prefixWord, tailWord_2354760, baseEnd_2354760] using wordTrace_append hprefix tailTrace_2354760
  have hstable : (prefixWord ++ tailWord_2354760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354760).length < 2 ^ (prefixWord ++ tailWord_2354760).sum := by decide
  have hdescent : baseEnd_2354760 < baseStart_2354760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354764 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 3, 3]
def baseStart_2354764 : Nat := 118140960795 + 2354764 * 2 ^ 59
def prefixEnd_2354764 : Nat := 4983230072969 + 3 ^ 40 * 2354764 * 2
def baseEnd_2354764 : Nat := 806083839935953472480429

theorem tailTrace_2354764 : CollatzResearch.WordTrace tailWord_2354764 prefixEnd_2354764 806083839935953472480429 := by
  unfold tailWord_2354764
  simp only [CollatzResearch.WordTrace]
  refine ⟨42942649420549832259291673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57256865894066443012388897 42942649420549832259291673)
  ·
    refine ⟨32206987065412374194468755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42942649420549832259291673 32206987065412374194468755)
    ·
      refine ⟨48310480598118561291703133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32206987065412374194468755 48310480598118561291703133)
      ·
        refine ⟨18116430224294460484388675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48310480598118561291703133 18116430224294460484388675)
        ·
          refine ⟨27174645336441690726583013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18116430224294460484388675 27174645336441690726583013)
          ·
            refine ⟨5095246000582817011234315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27174645336441690726583013 5095246000582817011234315)
            ·
              refine ⟨7642869000874225516851473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5095246000582817011234315 7642869000874225516851473)
              ·
                refine ⟨5732151750655669137638605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7642869000874225516851473 5732151750655669137638605)
                ·
                  refine ⟨2149556906495875926614477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5732151750655669137638605 2149556906495875926614477)
                  ·
                    refine ⟨806083839935953472480429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2149556906495875926614477 806083839935953472480429)
                    ·
                      rfl

theorem cell22_2354764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_2354764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354764 prefixEnd_2354764 := by exact prefixLift 2354764
  have htrace : WordTrace (prefixWord ++ tailWord_2354764) baseStart_2354764 baseEnd_2354764 := by
    simpa [prefixWord, tailWord_2354764, baseEnd_2354764] using wordTrace_append hprefix tailTrace_2354764
  have hstable : (prefixWord ++ tailWord_2354764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354764).length < 2 ^ (prefixWord ++ tailWord_2354764).sum := by decide
  have hdescent : baseEnd_2354764 < baseStart_2354764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354794 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_2354794 : Nat := 118140960795 + 2354794 * 2 ^ 59
def prefixEnd_2354794 : Nat := 4983230072969 + 3 ^ 40 * 2354794 * 2
def baseEnd_2354794 : Nat := 268698036516347798076779

theorem tailTrace_2354794 : CollatzResearch.WordTrace tailWord_2354794 prefixEnd_2354794 268698036516347798076779 := by
  unfold tailWord_2354794
  simp only [CollatzResearch.WordTrace]
  refine ⟨21471598257747744910543859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57257595353993986428116957 21471598257747744910543859)
  ·
    refine ⟨32207397386621617365815789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21471598257747744910543859 32207397386621617365815789)
    ·
      refine ⟨12077774019983106512180921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32207397386621617365815789 12077774019983106512180921)
      ·
        refine ⟨9058330514987329884135691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12077774019983106512180921 9058330514987329884135691)
        ·
          refine ⟨13587495772480994826203537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9058330514987329884135691 13587495772480994826203537)
          ·
            refine ⟨10190621829360746119652653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13587495772480994826203537 10190621829360746119652653)
            ·
              refine ⟨3821483186010279794869745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10190621829360746119652653 3821483186010279794869745)
              ·
                refine ⟨2866112389507709846152309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3821483186010279794869745 2866112389507709846152309)
                ·
                  refine ⟨268698036516347798076779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2866112389507709846152309 268698036516347798076779)
                  ·
                    rfl

theorem cell22_2354794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_2354794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354794 prefixEnd_2354794 := by exact prefixLift 2354794
  have htrace : WordTrace (prefixWord ++ tailWord_2354794) baseStart_2354794 baseEnd_2354794 := by
    simpa [prefixWord, tailWord_2354794, baseEnd_2354794] using wordTrace_append hprefix tailTrace_2354794
  have hstable : (prefixWord ++ tailWord_2354794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354794).length < 2 ^ (prefixWord ++ tailWord_2354794).sum := by decide
  have hdescent : baseEnd_2354794 < baseStart_2354794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354837 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_2354837 : Nat := 118140960795 + 2354837 * 2 ^ 59
def prefixEnd_2354837 : Nat := 4983230072969 + 3 ^ 40 * 2354837 * 2
def baseEnd_2354837 : Nat := 806108829327805615405205

theorem tailTrace_2354837 : CollatzResearch.WordTrace tailWord_2354837 prefixEnd_2354837 806108829327805615405205 := by
  unfold tailWord_2354837
  simp only [CollatzResearch.WordTrace]
  refine ⟨85887961369835197985990765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57258640913223465323993843 85887961369835197985990765)
  ·
    refine ⟨32207985513688199244746537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85887961369835197985990765 32207985513688199244746537)
    ·
      refine ⟨24155989135266149433559903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32207985513688199244746537 24155989135266149433559903)
      ·
        refine ⟨36233983702899224150339855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24155989135266149433559903 36233983702899224150339855)
        ·
          refine ⟨54350975554348836225509783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36233983702899224150339855 54350975554348836225509783)
          ·
            refine ⟨81526463331523254338264675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54350975554348836225509783 81526463331523254338264675)
            ·
              refine ⟨122289694997284881507397013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81526463331523254338264675 122289694997284881507397013)
              ·
                refine ⟨5732329452997728820659235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122289694997284881507397013 5732329452997728820659235)
                ·
                  refine ⟨8598494179496593230988853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5732329452997728820659235 8598494179496593230988853)
                  ·
                    refine ⟨806108829327805615405205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8598494179496593230988853 806108829327805615405205)
                    ·
                      rfl

theorem cell22_2354837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_2354837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354837 prefixEnd_2354837 := by exact prefixLift 2354837
  have htrace : WordTrace (prefixWord ++ tailWord_2354837) baseStart_2354837 baseEnd_2354837 := by
    simpa [prefixWord, tailWord_2354837, baseEnd_2354837] using wordTrace_append hprefix tailTrace_2354837
  have hstable : (prefixWord ++ tailWord_2354837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354837).length < 2 ^ (prefixWord ++ tailWord_2354837).sum := by decide
  have hdescent : baseEnd_2354837 < baseStart_2354837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354867 : List Nat := [1, 1, 1, 2, 3, 3, 4, 7]
def baseStart_2354867 : Nat := 118140960795 + 2354867 * 2 ^ 59
def prefixEnd_2354867 : Nat := 4983230072969 + 3 ^ 40 * 2354867 * 2
def baseEnd_2354867 : Nat := 89568788771210615239457

theorem tailTrace_2354867 : CollatzResearch.WordTrace tailWord_2354867 prefixEnd_2354867 89568788771210615239457 := by
  unfold tailWord_2354867
  simp only [CollatzResearch.WordTrace]
  refine ⟨85889055559726513109582855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57259370373151008739721903 85889055559726513109582855)
  ·
    refine ⟨128833583339589769664374283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85889055559726513109582855 128833583339589769664374283)
    ·
      refine ⟨193250375009384654496561425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128833583339589769664374283 193250375009384654496561425)
      ·
        refine ⟨144937781257038490872421069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193250375009384654496561425 144937781257038490872421069)
        ·
          refine ⟨54351667971389434077157901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144937781257038490872421069 54351667971389434077157901)
          ·
            refine ⟨20381875489271037778934213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54351667971389434077157901 20381875489271037778934213)
            ·
              refine ⟨3821601654238319583550165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20381875489271037778934213 3821601654238319583550165)
              ·
                refine ⟨89568788771210615239457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3821601654238319583550165 89568788771210615239457)
                ·
                  rfl

theorem cell22_2354867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 7].length) (baseStart_2354867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354867 prefixEnd_2354867 := by exact prefixLift 2354867
  have htrace : WordTrace (prefixWord ++ tailWord_2354867) baseStart_2354867 baseEnd_2354867 := by
    simpa [prefixWord, tailWord_2354867, baseEnd_2354867] using wordTrace_append hprefix tailTrace_2354867
  have hstable : (prefixWord ++ tailWord_2354867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354867).length < 2 ^ (prefixWord ++ tailWord_2354867).sum := by decide
  have hdescent : baseEnd_2354867 < baseStart_2354867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354871 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 2, 3]
def baseStart_2354871 : Nat := 118140960795 + 2354871 * 2 ^ 59
def prefixEnd_2354871 : Nat := 4983230072969 + 3 ^ 40 * 2354871 * 2
def baseEnd_2354871 : Nat := 806120468222640860055101

theorem tailTrace_2354871 : CollatzResearch.WordTrace tailWord_2354871 prefixEnd_2354871 806120468222640860055101 := by
  unfold tailWord_2354871
  simp only [CollatzResearch.WordTrace]
  refine ⟨85889201451712021792728467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57259467634474681195152311 85889201451712021792728467)
  ·
    refine ⟨128833802177568032689092701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85889201451712021792728467 128833802177568032689092701)
    ·
      refine ⟨48312675816588012258409763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128833802177568032689092701 48312675816588012258409763)
      ·
        refine ⟨72469013724882018387614645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48312675816588012258409763 72469013724882018387614645)
        ·
          refine ⟨6793970036707689223838873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72469013724882018387614645 6793970036707689223838873)
          ·
            refine ⟨5095477527530766917879155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6793970036707689223838873 5095477527530766917879155)
            ·
              refine ⟨7643216291296150376818733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5095477527530766917879155 7643216291296150376818733)
              ·
                refine ⟨2866206109236056391307025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7643216291296150376818733 2866206109236056391307025)
                ·
                  refine ⟨2149654581927042293480269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2866206109236056391307025 2149654581927042293480269)
                  ·
                    refine ⟨806120468222640860055101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2149654581927042293480269 806120468222640860055101)
                    ·
                      rfl

theorem cell22_2354871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_2354871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354871 prefixEnd_2354871 := by exact prefixLift 2354871
  have htrace : WordTrace (prefixWord ++ tailWord_2354871) baseStart_2354871 baseEnd_2354871 := by
    simpa [prefixWord, tailWord_2354871, baseEnd_2354871] using wordTrace_append hprefix tailTrace_2354871
  have hstable : (prefixWord ++ tailWord_2354871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354871).length < 2 ^ (prefixWord ++ tailWord_2354871).sum := by decide
  have hdescent : baseEnd_2354871 < baseStart_2354871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354912 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 7]
def baseStart_2354912 : Nat := 118140960795 + 2354912 * 2 ^ 59
def prefixEnd_2354912 : Nat := 4983230072969 + 3 ^ 40 * 2354912 * 2
def baseEnd_2354912 : Nat := 268711501120176806593325

theorem tailTrace_2354912 : CollatzResearch.WordTrace tailWord_2354912 prefixEnd_2354912 268711501120176806593325 := by
  unfold tailWord_2354912
  simp only [CollatzResearch.WordTrace]
  refine ⟨42945348422281742897485495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57260464563042323863313993 42945348422281742897485495)
  ·
    refine ⟨64418022633422614346228243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42945348422281742897485495 64418022633422614346228243)
    ·
      refine ⟨96627033950133921519342365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64418022633422614346228243 96627033950133921519342365)
      ·
        refine ⟨36235137731300220569753387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96627033950133921519342365 36235137731300220569753387)
        ·
          refine ⟨54352706596950330854630081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36235137731300220569753387 54352706596950330854630081)
          ·
            refine ⟨40764529947712748140972561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54352706596950330854630081 40764529947712748140972561)
            ·
              refine ⟨30573397460784561105729421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40764529947712748140972561 30573397460784561105729421)
              ·
                refine ⟨11465024047794210414648533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30573397460784561105729421 11465024047794210414648533)
                ·
                  refine ⟨268711501120176806593325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11465024047794210414648533 268711501120176806593325)
                  ·
                    rfl

theorem cell22_2354912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_2354912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354912 prefixEnd_2354912 := by exact prefixLift 2354912
  have htrace : WordTrace (prefixWord ++ tailWord_2354912) baseStart_2354912 baseEnd_2354912 := by
    simpa [prefixWord, tailWord_2354912, baseEnd_2354912] using wordTrace_append hprefix tailTrace_2354912
  have hstable : (prefixWord ++ tailWord_2354912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354912).length < 2 ^ (prefixWord ++ tailWord_2354912).sum := by decide
  have hdescent : baseEnd_2354912 < baseStart_2354912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2354929 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 5]
def baseStart_2354929 : Nat := 118140960795 + 2354929 * 2 ^ 59
def prefixEnd_2354929 : Nat := 4983230072969 + 3 ^ 40 * 2354929 * 2
def baseEnd_2354929 : Nat := 268713440935982680701641

theorem tailTrace_2354929 : CollatzResearch.WordTrace tailWord_2354929 prefixEnd_2354929 268713440935982680701641 := by
  unfold tailWord_2354929
  simp only [CollatzResearch.WordTrace]
  refine ⟨85891316885501897698339841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57260877923667931798893227 85891316885501897698339841)
  ·
    refine ⟨64418487664126423273754881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85891316885501897698339841 64418487664126423273754881)
    ·
      refine ⟨48313865748094817455316161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64418487664126423273754881 48313865748094817455316161)
      ·
        refine ⟨36235399311071113091487121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48313865748094817455316161 36235399311071113091487121)
        ·
          refine ⟨27176549483303334818615341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36235399311071113091487121 27176549483303334818615341)
          ·
            refine ⟨10191206056238750556980753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27176549483303334818615341 10191206056238750556980753)
            ·
              refine ⟨7643404542179062917735565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10191206056238750556980753 7643404542179062917735565)
              ·
                refine ⟨2866276703317148594150837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7643404542179062917735565 2866276703317148594150837)
                ·
                  refine ⟨268713440935982680701641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2866276703317148594150837 268713440935982680701641)
                  ·
                    rfl

theorem cell22_2354929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_2354929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2354929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2354929 prefixEnd_2354929 := by exact prefixLift 2354929
  have htrace : WordTrace (prefixWord ++ tailWord_2354929) baseStart_2354929 baseEnd_2354929 := by
    simpa [prefixWord, tailWord_2354929, baseEnd_2354929] using wordTrace_append hprefix tailTrace_2354929
  have hstable : (prefixWord ++ tailWord_2354929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2354929).length < 2 ^ (prefixWord ++ tailWord_2354929).sum := by decide
  have hdescent : baseEnd_2354929 < baseStart_2354929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2354929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355004 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_2355004 : Nat := 118140960795 + 2355004 * 2 ^ 59
def prefixEnd_2355004 : Nat := 4983230072969 + 3 ^ 40 * 2355004 * 2
def baseEnd_2355004 : Nat := 806165996840672846479693

theorem tailTrace_2355004 : CollatzResearch.WordTrace tailWord_2355004 prefixEnd_2355004 806165996840672846479693 := by
  unfold tailWord_2355004
  simp only [CollatzResearch.WordTrace]
  refine ⟨42947026180115092753660033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57262701573486790338213377 42947026180115092753660033)
  ·
    refine ⟨32210269635086319565245025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42947026180115092753660033 32210269635086319565245025)
    ·
      refine ⟨24157702226314739673933769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32210269635086319565245025 24157702226314739673933769)
      ·
        refine ⟨18118276669736054755450327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24157702226314739673933769 18118276669736054755450327)
        ·
          refine ⟨27177415004604082133175491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18118276669736054755450327 27177415004604082133175491)
          ·
            refine ⟨40766122506906123199763237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27177415004604082133175491 40766122506906123199763237)
            ·
              refine ⟨7643647970044898099955607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40766122506906123199763237 7643647970044898099955607)
              ·
                refine ⟨11465471955067347149933411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7643647970044898099955607 11465471955067347149933411)
                ·
                  refine ⟨17198207932601020724900117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11465471955067347149933411 17198207932601020724900117)
                  ·
                    refine ⟨806165996840672846479693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17198207932601020724900117 806165996840672846479693)
                    ·
                      rfl

theorem cell22_2355004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_2355004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355004 prefixEnd_2355004 := by exact prefixLift 2355004
  have htrace : WordTrace (prefixWord ++ tailWord_2355004) baseStart_2355004 baseEnd_2355004 := by
    simpa [prefixWord, tailWord_2355004, baseEnd_2355004] using wordTrace_append hprefix tailTrace_2355004
  have hstable : (prefixWord ++ tailWord_2355004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355004).length < 2 ^ (prefixWord ++ tailWord_2355004).sum := by decide
  have hdescent : baseEnd_2355004 < baseStart_2355004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355040 : List Nat := [2, 1, 1, 3, 3, 4, 2, 1, 2, 3]
def baseStart_2355040 : Nat := 118140960795 + 2355040 * 2 ^ 59
def prefixEnd_2355040 : Nat := 4983230072969 + 3 ^ 40 * 2355040 * 2
def baseEnd_2355040 : Nat := 806178320376380752579583

theorem tailTrace_2355040 : CollatzResearch.WordTrace tailWord_2355040 prefixEnd_2355040 806178320376380752579583 := by
  unfold tailWord_2355040
  simp only [CollatzResearch.WordTrace]
  refine ⟨42947682694049881827815287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57263576925399842437087049 42947682694049881827815287)
  ·
    refine ⟨64421524041074822741722931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42947682694049881827815287 64421524041074822741722931)
    ·
      refine ⟨96632286061612234112584397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64421524041074822741722931 96632286061612234112584397)
      ·
        refine ⟨36237107273104587792219149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96632286061612234112584397 36237107273104587792219149)
        ·
          refine ⟨13588915227414220422082181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36237107273104587792219149 13588915227414220422082181)
          ·
            refine ⟨2547921605140166329140409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13588915227414220422082181 2547921605140166329140409)
            ·
              refine ⟨1910941203855124746855307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2547921605140166329140409 1910941203855124746855307)
              ·
                refine ⟨2866411805782687120282961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910941203855124746855307 2866411805782687120282961)
                ·
                  refine ⟨2149808854337015340212221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2866411805782687120282961 2149808854337015340212221)
                  ·
                    refine ⟨806178320376380752579583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2149808854337015340212221 806178320376380752579583)
                    ·
                      rfl

theorem cell22_2355040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 2, 3].length) (baseStart_2355040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355040 prefixEnd_2355040 := by exact prefixLift 2355040
  have htrace : WordTrace (prefixWord ++ tailWord_2355040) baseStart_2355040 baseEnd_2355040 := by
    simpa [prefixWord, tailWord_2355040, baseEnd_2355040] using wordTrace_append hprefix tailTrace_2355040
  have hstable : (prefixWord ++ tailWord_2355040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355040).length < 2 ^ (prefixWord ++ tailWord_2355040).sum := by decide
  have hdescent : baseEnd_2355040 < baseStart_2355040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355081 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 5]
def baseStart_2355081 : Nat := 118140960795 + 2355081 * 2 ^ 59
def prefixEnd_2355081 : Nat := 4983230072969 + 3 ^ 40 * 2355081 * 2
def baseEnd_2355081 : Nat := 268730785171423437434819

theorem tailTrace_2355081 : CollatzResearch.WordTrace tailWord_2355081 prefixEnd_2355081 268730785171423437434819 := by
  unfold tailWord_2355081
  simp only [CollatzResearch.WordTrace]
  refine ⟨85896860780951227657873097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57264573853967485105248731 85896860780951227657873097)
  ·
    refine ⟨64422645585713420743404823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85896860780951227657873097 64422645585713420743404823)
    ·
      refine ⟨96633968378570131115107235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64422645585713420743404823 96633968378570131115107235)
      ·
        refine ⟨144950952567855196672660853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96633968378570131115107235 144950952567855196672660853)
        ·
          refine ⟨13589151803236424688061955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144950952567855196672660853 13589151803236424688061955)
          ·
            refine ⟨20383727704854637032092933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13589151803236424688061955 20383727704854637032092933)
            ·
              refine ⟨3821948944660244443517425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20383727704854637032092933 3821948944660244443517425)
              ·
                refine ⟨2866461708495183332638069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3821948944660244443517425 2866461708495183332638069)
                ·
                  refine ⟨268730785171423437434819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2866461708495183332638069 268730785171423437434819)
                  ·
                    rfl

theorem cell22_2355081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_2355081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355081 prefixEnd_2355081 := by exact prefixLift 2355081
  have htrace : WordTrace (prefixWord ++ tailWord_2355081) baseStart_2355081 baseEnd_2355081 := by
    simpa [prefixWord, tailWord_2355081, baseEnd_2355081] using wordTrace_append hprefix tailTrace_2355081
  have hstable : (prefixWord ++ tailWord_2355081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355081).length < 2 ^ (prefixWord ++ tailWord_2355081).sum := by decide
  have hdescent : baseEnd_2355081 < baseStart_2355081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355102 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_2355102 : Nat := 118140960795 + 2355102 * 2 ^ 59
def prefixEnd_2355102 : Nat := 4983230072969 + 3 ^ 40 * 2355102 * 2
def baseEnd_2355102 : Nat := 806199544243433257529393

theorem tailTrace_2355102 : CollatzResearch.WordTrace tailWord_2355102 prefixEnd_2355102 806199544243433257529393 := by
  unfold tailWord_2355102
  simp only [CollatzResearch.WordTrace]
  refine ⟨10737203339234393530548445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57265084475916765496258373 10737203339234393530548445)
  ·
    refine ⟨4026451252212897573955667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10737203339234393530548445 4026451252212897573955667)
    ·
      refine ⟨6039676878319346360933501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4026451252212897573955667 6039676878319346360933501)
      ·
        refine ⟨2264878829369754885350063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6039676878319346360933501 2264878829369754885350063)
        ·
          refine ⟨3397318244054632328025095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2264878829369754885350063 3397318244054632328025095)
          ·
            refine ⟨5095977366081948492037643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3397318244054632328025095 5095977366081948492037643)
            ·
              refine ⟨7643966049122922738056465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5095977366081948492037643 7643966049122922738056465)
              ·
                refine ⟨5732974536842192053542349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7643966049122922738056465 5732974536842192053542349)
                ·
                  refine ⟨2149865451315822020078381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5732974536842192053542349 2149865451315822020078381)
                  ·
                    refine ⟨806199544243433257529393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2149865451315822020078381 806199544243433257529393)
                    ·
                      rfl

theorem cell22_2355102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_2355102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355102 prefixEnd_2355102 := by exact prefixLift 2355102
  have htrace : WordTrace (prefixWord ++ tailWord_2355102) baseStart_2355102 baseEnd_2355102 := by
    simpa [prefixWord, tailWord_2355102, baseEnd_2355102] using wordTrace_append hprefix tailTrace_2355102
  have hstable : (prefixWord ++ tailWord_2355102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355102).length < 2 ^ (prefixWord ++ tailWord_2355102).sum := by decide
  have hdescent : baseEnd_2355102 < baseStart_2355102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355132 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 5]
def baseStart_2355132 : Nat := 118140960795 + 2355132 * 2 ^ 59
def prefixEnd_2355132 : Nat := 4983230072969 + 3 ^ 40 * 2355132 * 2
def baseEnd_2355132 : Nat := 268736604618841059759767

theorem tailTrace_2355132 : CollatzResearch.WordTrace tailWord_2355132 prefixEnd_2355132 268736604618841059759767 := by
  unfold tailWord_2355132
  simp only [CollatzResearch.WordTrace]
  refine ⟨42949360451883231683989825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57265813935844308911986433 42949360451883231683989825)
  ·
    refine ⟨32212020338912423762992369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42949360451883231683989825 32212020338912423762992369)
    ·
      refine ⟨24159015254184317822244277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32212020338912423762992369 24159015254184317822244277)
      ·
        refine ⟨2264907680079779795835401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24159015254184317822244277 2264907680079779795835401)
        ·
          refine ⟨1698680760059834846876551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2264907680079779795835401 1698680760059834846876551)
          ·
            refine ⟨2548021140089752270314827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698680760059834846876551 2548021140089752270314827)
            ·
              refine ⟨3822031710134628405472241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548021140089752270314827 3822031710134628405472241)
              ·
                refine ⟨2866523782600971304104181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3822031710134628405472241 2866523782600971304104181)
                ·
                  refine ⟨268736604618841059759767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2866523782600971304104181 268736604618841059759767)
                  ·
                    rfl

theorem cell22_2355132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_2355132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355132 prefixEnd_2355132 := by exact prefixLift 2355132
  have htrace : WordTrace (prefixWord ++ tailWord_2355132) baseStart_2355132 baseEnd_2355132 := by
    simpa [prefixWord, tailWord_2355132, baseEnd_2355132] using wordTrace_append hprefix tailTrace_2355132
  have hstable : (prefixWord ++ tailWord_2355132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355132).length < 2 ^ (prefixWord ++ tailWord_2355132).sum := by decide
  have hdescent : baseEnd_2355132 < baseStart_2355132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355139 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 5, 6]
def baseStart_2355139 : Nat := 118140960795 + 2355139 * 2 ^ 59
def prefixEnd_2355139 : Nat := 4983230072969 + 3 ^ 40 * 2355139 * 2
def baseEnd_2355139 : Nat := 806212210099577494354279

theorem tailTrace_2355139 : CollatzResearch.WordTrace tailWord_2355139 prefixEnd_2355139 806212210099577494354279 := by
  unfold tailWord_2355139
  simp only [CollatzResearch.WordTrace]
  refine ⟨85898976214741103563484471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57265984143160735708989647 85898976214741103563484471)
  ·
    refine ⟨128848464322111655345226707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85898976214741103563484471 128848464322111655345226707)
    ·
      refine ⟨193272696483167483017840061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128848464322111655345226707 193272696483167483017840061)
      ·
        refine ⟨72477261181187806131690023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193272696483167483017840061 72477261181187806131690023)
        ·
          refine ⟨108715891771781709197535035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72477261181187806131690023 108715891771781709197535035)
          ·
            refine ⟨163073837657672563796302553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108715891771781709197535035 163073837657672563796302553)
            ·
              refine ⟨122305378243254422847226915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163073837657672563796302553 122305378243254422847226915)
              ·
                refine ⟨183458067364881634270840373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122305378243254422847226915 183458067364881634270840373)
                ·
                  refine ⟨17199193815457653212891285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183458067364881634270840373 17199193815457653212891285)
                  ·
                    refine ⟨806212210099577494354279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17199193815457653212891285 806212210099577494354279)
                    ·
                      rfl

theorem cell22_2355139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_2355139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355139 prefixEnd_2355139 := by exact prefixLift 2355139
  have htrace : WordTrace (prefixWord ++ tailWord_2355139) baseStart_2355139 baseEnd_2355139 := by
    simpa [prefixWord, tailWord_2355139, baseEnd_2355139] using wordTrace_append hprefix tailTrace_2355139
  have hstable : (prefixWord ++ tailWord_2355139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355139).length < 2 ^ (prefixWord ++ tailWord_2355139).sum := by decide
  have hdescent : baseEnd_2355139 < baseStart_2355139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355156 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2355156 : Nat := 118140960795 + 2355156 * 2 ^ 59
def prefixEnd_2355156 : Nat := 4983230072969 + 3 ^ 40 * 2355156 * 2
def baseEnd_2355156 : Nat := 806218029546995116679227

theorem tailTrace_2355156 : CollatzResearch.WordTrace tailWord_2355156 prefixEnd_2355156 806218029546995116679227 := by
  unfold tailWord_2355156
  simp only [CollatzResearch.WordTrace]
  refine ⟨42949798127839757733426661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57266397503786343644568881 42949798127839757733426661)
  ·
    refine ⟨8053087148969954575017499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42949798127839757733426661 8053087148969954575017499)
    ·
      refine ⟨12079630723454931862526249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8053087148969954575017499 12079630723454931862526249)
      ·
        refine ⟨9059723042591198896894687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12079630723454931862526249 9059723042591198896894687)
        ·
          refine ⟨13589584563886798345342031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9059723042591198896894687 13589584563886798345342031)
          ·
            refine ⟨20384376845830197518013047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13589584563886798345342031 20384376845830197518013047)
            ·
              refine ⟨30576565268745296277019571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20384376845830197518013047 30576565268745296277019571)
              ·
                refine ⟨45864847903117944415529357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30576565268745296277019571 45864847903117944415529357)
                ·
                  refine ⟨17199317963669229155823509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45864847903117944415529357 17199317963669229155823509)
                  ·
                    refine ⟨806218029546995116679227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17199317963669229155823509 806218029546995116679227)
                    ·
                      rfl

theorem cell22_2355156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2355156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355156 prefixEnd_2355156 := by exact prefixLift 2355156
  have htrace : WordTrace (prefixWord ++ tailWord_2355156) baseStart_2355156 baseEnd_2355156 := by
    simpa [prefixWord, tailWord_2355156, baseEnd_2355156] using wordTrace_append hprefix tailTrace_2355156
  have hstable : (prefixWord ++ tailWord_2355156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355156).length < 2 ^ (prefixWord ++ tailWord_2355156).sum := by decide
  have hdescent : baseEnd_2355156 < baseStart_2355156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355171 : List Nat := [1, 1, 1, 6, 1, 3, 1, 8]
def baseStart_2355171 : Nat := 118140960795 + 2355171 * 2 ^ 59
def prefixEnd_2355171 : Nat := 4983230072969 + 3 ^ 40 * 2355171 * 2
def baseEnd_2355171 : Nat := 89580351594837786394909

theorem tailTrace_2355171 : CollatzResearch.WordTrace tailWord_2355171 prefixEnd_2355171 89580351594837786394909 := by
  unfold tailWord_2355171
  simp only [CollatzResearch.WordTrace]
  refine ⟨85900143350625173028649367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57266762233750115352432911 85900143350625173028649367)
  ·
    refine ⟨128850215025937759542974051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85900143350625173028649367 128850215025937759542974051)
    ·
      refine ⟨193275322538906639314461077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128850215025937759542974051 193275322538906639314461077)
      ·
        refine ⟨9059780744011248717865363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 193275322538906639314461077 9059780744011248717865363)
        ·
          refine ⟨13589671116016873076798045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9059780744011248717865363 13589671116016873076798045)
          ·
            refine ⟨5096126668506327403799267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13589671116016873076798045 5096126668506327403799267)
            ·
              refine ⟨7644190002759491105698901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5096126668506327403799267 7644190002759491105698901)
              ·
                refine ⟨89580351594837786394909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7644190002759491105698901 89580351594837786394909)
                ·
                  rfl

theorem cell22_2355171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 8].length) (baseStart_2355171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355171 prefixEnd_2355171 := by exact prefixLift 2355171
  have htrace : WordTrace (prefixWord ++ tailWord_2355171) baseStart_2355171 baseEnd_2355171 := by
    simpa [prefixWord, tailWord_2355171, baseEnd_2355171] using wordTrace_append hprefix tailTrace_2355171
  have hstable : (prefixWord ++ tailWord_2355171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355171).length < 2 ^ (prefixWord ++ tailWord_2355171).sum := by decide
  have hdescent : baseEnd_2355171 < baseStart_2355171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355190 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_2355190 : Nat := 118140960795 + 2355190 * 2 ^ 59
def prefixEnd_2355190 : Nat := 4983230072969 + 3 ^ 40 * 2355190 * 2
def baseEnd_2355190 : Nat := 806229668441830361329123

theorem tailTrace_2355190 : CollatzResearch.WordTrace tailWord_2355190 prefixEnd_2355190 806229668441830361329123 := by
  unfold tailWord_2355190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5368802271097271204599439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57267224225037559515727349 5368802271097271204599439)
  ·
    refine ⟨8053203406645906806899159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5368802271097271204599439 8053203406645906806899159)
    ·
      refine ⟨12079805109968860210348739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8053203406645906806899159 12079805109968860210348739)
      ·
        refine ⟨18119707664953290315523109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12079805109968860210348739 18119707664953290315523109)
        ·
          refine ⟨3397445187178741934160583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18119707664953290315523109 3397445187178741934160583)
          ·
            refine ⟨5096167780768112901240875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3397445187178741934160583 5096167780768112901240875)
            ·
              refine ⟨7644251671152169351861313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5096167780768112901240875 7644251671152169351861313)
              ·
                refine ⟨5733188753364127013895985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7644251671152169351861313 5733188753364127013895985)
                ·
                  refine ⟨4299891565023095260421989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5733188753364127013895985 4299891565023095260421989)
                  ·
                    refine ⟨806229668441830361329123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4299891565023095260421989 806229668441830361329123)
                    ·
                      rfl

theorem cell22_2355190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_2355190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355190 prefixEnd_2355190 := by exact prefixLift 2355190
  have htrace : WordTrace (prefixWord ++ tailWord_2355190) baseStart_2355190 baseEnd_2355190 := by
    simpa [prefixWord, tailWord_2355190, baseEnd_2355190] using wordTrace_append hprefix tailTrace_2355190
  have hstable : (prefixWord ++ tailWord_2355190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355190).length < 2 ^ (prefixWord ++ tailWord_2355190).sum := by decide
  have hdescent : baseEnd_2355190 < baseStart_2355190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355201 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2355201 : Nat := 118140960795 + 2355201 * 2 ^ 59
def prefixEnd_2355201 : Nat := 4983230072969 + 3 ^ 40 * 2355201 * 2
def baseEnd_2355201 : Nat := 806233433966629999304089

theorem tailTrace_2355201 : CollatzResearch.WordTrace tailWord_2355201 prefixEnd_2355201 806233433966629999304089 := by
  unfold tailWord_2355201
  simp only [CollatzResearch.WordTrace]
  refine ⟨85901237540516488152241457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57267491693677658768160971 85901237540516488152241457)
  ·
    refine ⟨64425928155387366114181093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85901237540516488152241457 64425928155387366114181093)
    ·
      refine ⟨12079861529135131146408955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64425928155387366114181093 12079861529135131146408955)
      ·
        refine ⟨18119792293702696719613433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12079861529135131146408955 18119792293702696719613433)
        ·
          refine ⟨13589844220277022539710075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18119792293702696719613433 13589844220277022539710075)
          ·
            refine ⟨20384766330415533809565113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13589844220277022539710075 20384766330415533809565113)
            ·
              refine ⟨15288574747811650357173835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20384766330415533809565113 15288574747811650357173835)
              ·
                refine ⟨22932862121717475535760753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15288574747811650357173835 22932862121717475535760753)
                ·
                  refine ⟨17199646591288106651820565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22932862121717475535760753 17199646591288106651820565)
                  ·
                    refine ⟨806233433966629999304089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17199646591288106651820565 806233433966629999304089)
                    ·
                      rfl

theorem cell22_2355201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2355201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355201 prefixEnd_2355201 := by exact prefixLift 2355201
  have htrace : WordTrace (prefixWord ++ tailWord_2355201) baseStart_2355201 baseEnd_2355201 := by
    simpa [prefixWord, tailWord_2355201, baseEnd_2355201] using wordTrace_append hprefix tailTrace_2355201
  have hstable : (prefixWord ++ tailWord_2355201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355201).length < 2 ^ (prefixWord ++ tailWord_2355201).sum := by decide
  have hdescent : baseEnd_2355201 < baseStart_2355201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355216 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 5]
def baseStart_2355216 : Nat := 118140960795 + 2355216 * 2 ^ 59
def prefixEnd_2355216 : Nat := 4983230072969 + 3 ^ 40 * 2355216 * 2
def baseEnd_2355216 : Nat := 268746189591058320059681

theorem tailTrace_2355216 : CollatzResearch.WordTrace tailWord_2355216 prefixEnd_2355216 268746189591058320059681 := by
  unfold tailWord_2355216
  simp only [CollatzResearch.WordTrace]
  refine ⟨42950892317731072857018751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57267856423641430476025001 42950892317731072857018751)
  ·
    refine ⟨64426338476596609285528127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42950892317731072857018751 64426338476596609285528127)
    ·
      refine ⟨96639507714894913928292191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64426338476596609285528127 96639507714894913928292191)
      ·
        refine ⟨144959261572342370892438287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96639507714894913928292191 144959261572342370892438287)
        ·
          refine ⟨217438892358513556338657431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144959261572342370892438287 217438892358513556338657431)
          ·
            refine ⟨326158338537770334507986147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217438892358513556338657431 326158338537770334507986147)
            ·
              refine ⟨489237507806655501761979221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326158338537770334507986147 489237507806655501761979221)
              ·
                refine ⟨2866626022304622080636597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 489237507806655501761979221 2866626022304622080636597)
                ·
                  refine ⟨268746189591058320059681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2866626022304622080636597 268746189591058320059681)
                  ·
                    rfl

theorem cell22_2355216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_2355216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355216 prefixEnd_2355216 := by exact prefixLift 2355216
  have htrace : WordTrace (prefixWord ++ tailWord_2355216) baseStart_2355216 baseEnd_2355216 := by
    simpa [prefixWord, tailWord_2355216, baseEnd_2355216] using wordTrace_append hprefix tailTrace_2355216
  have hstable : (prefixWord ++ tailWord_2355216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355216).length < 2 ^ (prefixWord ++ tailWord_2355216).sum := by decide
  have hdescent : baseEnd_2355216 < baseStart_2355216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355278 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 6]
def baseStart_2355278 : Nat := 118140960795 + 2355278 * 2 ^ 59
def prefixEnd_2355278 : Nat := 4983230072969 + 3 ^ 40 * 2355278 * 2
def baseEnd_2355278 : Nat := 268753264213409155042951

theorem tailTrace_2355278 : CollatzResearch.WordTrace tailWord_2355278 prefixEnd_2355278 268753264213409155042951 := by
  unfold tailWord_2355278
  simp only [CollatzResearch.WordTrace]
  refine ⟨10738005745154691287849311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57269363974158353535196325 10738005745154691287849311)
  ·
    refine ⟨16107008617732036931773967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10738005745154691287849311 16107008617732036931773967)
    ·
      refine ⟨24160512926598055397660951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16107008617732036931773967 24160512926598055397660951)
      ·
        refine ⟨36240769389897083096491427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24160512926598055397660951 36240769389897083096491427)
        ·
          refine ⟨54361154084845624644737141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36240769389897083096491427 54361154084845624644737141)
          ·
            refine ⟨5096358195454277310444107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54361154084845624644737141 5096358195454277310444107)
            ·
              refine ⟨7644537293181415965666161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5096358195454277310444107 7644537293181415965666161)
              ·
                refine ⟨5733402969886061974249621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7644537293181415965666161 5733402969886061974249621)
                ·
                  refine ⟨268753264213409155042951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5733402969886061974249621 268753264213409155042951)
                  ·
                    rfl

theorem cell22_2355278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_2355278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355278 prefixEnd_2355278 := by exact prefixLift 2355278
  have htrace : WordTrace (prefixWord ++ tailWord_2355278) baseStart_2355278 baseEnd_2355278 := by
    simpa [prefixWord, tailWord_2355278, baseEnd_2355278] using wordTrace_append hprefix tailTrace_2355278
  have hstable : (prefixWord ++ tailWord_2355278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355278).length < 2 ^ (prefixWord ++ tailWord_2355278).sum := by decide
  have hdescent : baseEnd_2355278 < baseStart_2355278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355310 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_2355310 : Nat := 118140960795 + 2355310 * 2 ^ 59
def prefixEnd_2355310 : Nat := 4983230072969 + 3 ^ 40 * 2355310 * 2
def baseEnd_2355310 : Nat := 806270746894190048328755

theorem tailTrace_2355310 : CollatzResearch.WordTrace tailWord_2355310 prefixEnd_2355310 806270746894190048328755 := by
  unfold tailWord_2355310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10738151637140199970994923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57270142064747733178639589 10738151637140199970994923)
  ·
    refine ⟨16107227455710299956492385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10738151637140199970994923 16107227455710299956492385)
    ·
      refine ⟨12080420591782724967369289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16107227455710299956492385 12080420591782724967369289)
      ·
        refine ⟨9060315443837043725526967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12080420591782724967369289 9060315443837043725526967)
        ·
          refine ⟨13590473165755565588290451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9060315443837043725526967 13590473165755565588290451)
          ·
            refine ⟨20385709748633348382435677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13590473165755565588290451 20385709748633348382435677)
            ·
              refine ⟨7644641155737505643413379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20385709748633348382435677 7644641155737505643413379)
              ·
                refine ⟨11466961733606258465120069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7644641155737505643413379 11466961733606258465120069)
                ·
                  refine ⟨2150055325051173462210013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11466961733606258465120069 2150055325051173462210013)
                  ·
                    refine ⟨806270746894190048328755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2150055325051173462210013 806270746894190048328755)
                    ·
                      rfl

theorem cell22_2355310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_2355310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355310 prefixEnd_2355310 := by exact prefixLift 2355310
  have htrace : WordTrace (prefixWord ++ tailWord_2355310) baseStart_2355310 baseEnd_2355310 := by
    simpa [prefixWord, tailWord_2355310, baseEnd_2355310] using wordTrace_append hprefix tailTrace_2355310
  have hstable : (prefixWord ++ tailWord_2355310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355310).length < 2 ^ (prefixWord ++ tailWord_2355310).sum := by decide
  have hdescent : baseEnd_2355310 < baseStart_2355310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355428 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_2355428 : Nat := 118140960795 + 2355428 * 2 ^ 59
def prefixEnd_2355428 : Nat := 4983230072969 + 3 ^ 40 * 2355428 * 2
def baseEnd_2355428 : Nat := 806311140705677073878393

theorem tailTrace_2355428 : CollatzResearch.WordTrace tailWord_2355428 prefixEnd_2355428 806311140705677073878393 := by
  unfold tailWord_2355428
  simp only [CollatzResearch.WordTrace]
  refine ⟨42954758455347052960377469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57273011273796070613836625 42954758455347052960377469)
  ·
    refine ⟨16108034420755144860141551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42954758455347052960377469 16108034420755144860141551)
    ·
      refine ⟨24162051631132717290212327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16108034420755144860141551 24162051631132717290212327)
      ·
        refine ⟨36243077446699075935318491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24162051631132717290212327 36243077446699075935318491)
        ·
          refine ⟨54364616170048613902977737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36243077446699075935318491 54364616170048613902977737)
          ·
            refine ⟨40773462127536460427233303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54364616170048613902977737 40773462127536460427233303)
            ·
              refine ⟨61160193191304690640849955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40773462127536460427233303 61160193191304690640849955)
              ·
                refine ⟨91740289786957035961274933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61160193191304690640849955 91740289786957035961274933)
                ·
                  refine ⟨8600652167527222121369525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91740289786957035961274933 8600652167527222121369525)
                  ·
                    refine ⟨806311140705677073878393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8600652167527222121369525 806311140705677073878393)
                    ·
                      rfl

theorem cell22_2355428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_2355428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355428 prefixEnd_2355428 := by exact prefixLift 2355428
  have htrace : WordTrace (prefixWord ++ tailWord_2355428) baseStart_2355428 baseEnd_2355428 := by
    simpa [prefixWord, tailWord_2355428, baseEnd_2355428] using wordTrace_append hprefix tailTrace_2355428
  have hstable : (prefixWord ++ tailWord_2355428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355428).length < 2 ^ (prefixWord ++ tailWord_2355428).sum := by decide
  have hdescent : baseEnd_2355428 < baseStart_2355428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355443 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 1, 6]
def baseStart_2355443 : Nat := 118140960795 + 2355443 * 2 ^ 59
def prefixEnd_2355443 : Nat := 4983230072969 + 3 ^ 40 * 2355443 * 2
def baseEnd_2355443 : Nat := 806316275512222034753347

theorem tailTrace_2355443 : CollatzResearch.WordTrace tailWord_2355443 prefixEnd_2355443 806316275512222034753347 := by
  unfold tailWord_2355443
  simp only [CollatzResearch.WordTrace]
  refine ⟨85910064005639763482550983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57273376003759842321700655 85910064005639763482550983)
  ·
    refine ⟨128865096008459645223826475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85910064005639763482550983 128865096008459645223826475)
    ·
      refine ⟨193297644012689467835739713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128865096008459645223826475 193297644012689467835739713)
      ·
        refine ⟨144973233009517100876804785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193297644012689467835739713 144973233009517100876804785)
        ·
          refine ⟨108729924757137825657603589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144973233009517100876804785 108729924757137825657603589)
          ·
            refine ⟨20386860891963342310800673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108729924757137825657603589 20386860891963342310800673)
            ·
              refine ⟨15290145668972506733100505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20386860891963342310800673 15290145668972506733100505)
              ·
                refine ⟨11467609251729380049825379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15290145668972506733100505 11467609251729380049825379)
                ·
                  refine ⟨17201413877594070074738069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11467609251729380049825379 17201413877594070074738069)
                  ·
                    refine ⟨806316275512222034753347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17201413877594070074738069 806316275512222034753347)
                    ·
                      rfl

theorem cell22_2355443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_2355443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355443 prefixEnd_2355443 := by exact prefixLift 2355443
  have htrace : WordTrace (prefixWord ++ tailWord_2355443) baseStart_2355443 baseEnd_2355443 := by
    simpa [prefixWord, tailWord_2355443, baseEnd_2355443] using wordTrace_append hprefix tailTrace_2355443
  have hstable : (prefixWord ++ tailWord_2355443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355443).length < 2 ^ (prefixWord ++ tailWord_2355443).sum := by decide
  have hdescent : baseEnd_2355443 < baseStart_2355443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355479 : List Nat := [1, 1, 3, 4, 1, 4, 1, 2, 2, 3]
def baseStart_2355479 : Nat := 118140960795 + 2355479 * 2 ^ 59
def prefixEnd_2355479 : Nat := 4983230072969 + 3 ^ 40 * 2355479 * 2
def baseEnd_2355479 : Nat := 806328599047929940853237

theorem tailTrace_2355479 : CollatzResearch.WordTrace tailWord_2355479 prefixEnd_2355479 806328599047929940853237 := by
  unfold tailWord_2355479
  simp only [CollatzResearch.WordTrace]
  refine ⟨85911377033509341630861491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57274251355672894420574327 85911377033509341630861491)
  ·
    refine ⟨128867065550264012446292237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85911377033509341630861491 128867065550264012446292237)
    ·
      refine ⟨48325149581349004667359589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128867065550264012446292237 48325149581349004667359589)
      ·
        refine ⟨9060965546502938375129923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48325149581349004667359589 9060965546502938375129923)
        ·
          refine ⟨13591448319754407562694885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9060965546502938375129923 13591448319754407562694885)
          ·
            refine ⟨2548396559953951418005291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13591448319754407562694885 2548396559953951418005291)
            ·
              refine ⟨3822594839930927127007937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548396559953951418005291 3822594839930927127007937)
              ·
                refine ⟨2866946129948195345255953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3822594839930927127007937 2866946129948195345255953)
                ·
                  refine ⟨2150209597461146508941965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2866946129948195345255953 2150209597461146508941965)
                  ·
                    refine ⟨806328599047929940853237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2150209597461146508941965 806328599047929940853237)
                    ·
                      rfl

theorem cell22_2355479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_2355479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355479 prefixEnd_2355479 := by exact prefixLift 2355479
  have htrace : WordTrace (prefixWord ++ tailWord_2355479) baseStart_2355479 baseEnd_2355479 := by
    simpa [prefixWord, tailWord_2355479, baseEnd_2355479] using wordTrace_append hprefix tailTrace_2355479
  have hstable : (prefixWord ++ tailWord_2355479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355479).length < 2 ^ (prefixWord ++ tailWord_2355479).sum := by decide
  have hdescent : baseEnd_2355479 < baseStart_2355479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355496 : List Nat := [2, 1, 5, 1, 3, 1, 3, 1, 2, 3]
def baseStart_2355496 : Nat := 118140960795 + 2355496 * 2 ^ 59
def prefixEnd_2355496 : Nat := 4983230072969 + 3 ^ 40 * 2355496 * 2
def baseEnd_2355496 : Nat := 806334418495347563178185

theorem tailTrace_2355496 : CollatzResearch.WordTrace tailWord_2355496 prefixEnd_2355496 806334418495347563178185 := by
  unfold tailWord_2355496
  simp only [CollatzResearch.WordTrace]
  refine ⟨42955998537223876767115171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57274664716298502356153561 42955998537223876767115171)
  ·
    refine ⟨64433997805835815150672757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42955998537223876767115171 64433997805835815150672757)
    ·
      refine ⟨6040687294297107670375571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64433997805835815150672757 6040687294297107670375571)
      ·
        refine ⟨9061030941445661505563357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6040687294297107670375571 9061030941445661505563357)
        ·
          refine ⟨3397886603042123064586259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9061030941445661505563357 3397886603042123064586259)
          ·
            refine ⟨5096829904563184596879389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3397886603042123064586259 5096829904563184596879389)
            ·
              refine ⟨1911311214211194223829771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5096829904563184596879389 1911311214211194223829771)
              ·
                refine ⟨2866966821316791335744657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911311214211194223829771 2866966821316791335744657)
                ·
                  refine ⟨2150225115987593501808493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2866966821316791335744657 2150225115987593501808493)
                  ·
                    refine ⟨806334418495347563178185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2150225115987593501808493 806334418495347563178185)
                    ·
                      rfl

theorem cell22_2355496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_2355496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355496 prefixEnd_2355496 := by exact prefixLift 2355496
  have htrace : WordTrace (prefixWord ++ tailWord_2355496) baseStart_2355496 baseEnd_2355496 := by
    simpa [prefixWord, tailWord_2355496, baseEnd_2355496] using wordTrace_append hprefix tailTrace_2355496
  have hstable : (prefixWord ++ tailWord_2355496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355496).length < 2 ^ (prefixWord ++ tailWord_2355496).sum := by decide
  have hdescent : baseEnd_2355496 < baseStart_2355496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355541 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 3, 3]
def baseStart_2355541 : Nat := 118140960795 + 2355541 * 2 ^ 59
def prefixEnd_2355541 : Nat := 4983230072969 + 3 ^ 40 * 2355541 * 2
def baseEnd_2355541 : Nat := 806349822914982445803047

theorem tailTrace_2355541 : CollatzResearch.WordTrace tailWord_2355541 prefixEnd_2355541 806349822914982445803047 := by
  unfold tailWord_2355541
  simp only [CollatzResearch.WordTrace]
  refine ⟨85913638359284726219618477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57275758906189817479745651 85913638359284726219618477)
  ·
    refine ⟨32217614384731772332356929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85913638359284726219618477 32217614384731772332356929)
    ·
      refine ⟨24163210788548829249267697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32217614384731772332356929 24163210788548829249267697)
      ·
        refine ⟨18122408091411621936950773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24163210788548829249267697 18122408091411621936950773)
        ·
          refine ⟨1698975758569839556589135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18122408091411621936950773 1698975758569839556589135)
          ·
            refine ⟨2548463637854759334883703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698975758569839556589135 2548463637854759334883703)
            ·
              refine ⟨3822695456782139002325555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548463637854759334883703 3822695456782139002325555)
              ·
                refine ⟨5734043185173208503488333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3822695456782139002325555 5734043185173208503488333)
                ·
                  refine ⟨2150266194439953188808125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5734043185173208503488333 2150266194439953188808125)
                  ·
                    refine ⟨806349822914982445803047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2150266194439953188808125 806349822914982445803047)
                    ·
                      rfl

theorem cell22_2355541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_2355541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355541 prefixEnd_2355541 := by exact prefixLift 2355541
  have htrace : WordTrace (prefixWord ++ tailWord_2355541) baseStart_2355541 baseEnd_2355541 := by
    simpa [prefixWord, tailWord_2355541, baseEnd_2355541] using wordTrace_append hprefix tailTrace_2355541
  have hstable : (prefixWord ++ tailWord_2355541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355541).length < 2 ^ (prefixWord ++ tailWord_2355541).sum := by decide
  have hdescent : baseEnd_2355541 < baseStart_2355541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355554 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 5]
def baseStart_2355554 : Nat := 118140960795 + 2355554 * 2 ^ 59
def prefixEnd_2355554 : Nat := 4983230072969 + 3 ^ 40 * 2355554 * 2
def baseEnd_2355554 : Nat := 268784757693551581742669

theorem tailTrace_2355554 : CollatzResearch.WordTrace tailWord_2355554 prefixEnd_2355554 268784757693551581742669 := by
  unfold tailWord_2355554
  simp only [CollatzResearch.WordTrace]
  refine ⟨21478528127059407359960429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57276075005491752959894477 21478528127059407359960429)
  ·
    refine ⟨8054448047647277759985161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21478528127059407359960429 8054448047647277759985161)
    ·
      refine ⟨6040836035735458319988871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8054448047647277759985161 6040836035735458319988871)
      ·
        refine ⟨9061254053603187479983307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6040836035735458319988871 9061254053603187479983307)
        ·
          refine ⟨13591881080404781219974961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9061254053603187479983307 13591881080404781219974961)
          ·
            refine ⟨10193910810303585914981221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13591881080404781219974961 10193910810303585914981221)
            ·
              refine ⟨1911358276931922359058979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10193910810303585914981221 1911358276931922359058979)
              ·
                refine ⟨2867037415397883538588469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911358276931922359058979 2867037415397883538588469)
                ·
                  refine ⟨268784757693551581742669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2867037415397883538588469 268784757693551581742669)
                  ·
                    rfl

theorem cell22_2355554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_2355554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355554 prefixEnd_2355554 := by exact prefixLift 2355554
  have htrace : WordTrace (prefixWord ++ tailWord_2355554) baseStart_2355554 baseEnd_2355554 := by
    simpa [prefixWord, tailWord_2355554, baseEnd_2355554] using wordTrace_append hprefix tailTrace_2355554
  have hstable : (prefixWord ++ tailWord_2355554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355554).length < 2 ^ (prefixWord ++ tailWord_2355554).sum := by decide
  have hdescent : baseEnd_2355554 < baseStart_2355554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355565 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 8]
def baseStart_2355565 : Nat := 118140960795 + 2355565 * 2 ^ 59
def prefixEnd_2355565 : Nat := 4983230072969 + 3 ^ 40 * 2355565 * 2
def baseEnd_2355565 : Nat := 268786012868484794400991

theorem tailTrace_2355565 : CollatzResearch.WordTrace tailWord_2355565 prefixEnd_2355565 268786012868484794400991 := by
  unfold tailWord_2355565
  simp only [CollatzResearch.WordTrace]
  refine ⟨85914513711197778318492149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57276342474131852212328099 85914513711197778318492149)
  ·
    refine ⟨8054485660424791717358639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85914513711197778318492149 8054485660424791717358639)
    ·
      refine ⟨12081728490637187576037959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8054485660424791717358639 12081728490637187576037959)
      ·
        refine ⟨18122592735955781364056939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12081728490637187576037959 18122592735955781364056939)
        ·
          refine ⟨27183889103933672046085409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18122592735955781364056939 27183889103933672046085409)
          ·
            refine ⟨20387916827950254034564057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27183889103933672046085409 20387916827950254034564057)
            ·
              refine ⟨15290937620962690525923043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20387916827950254034564057 15290937620962690525923043)
              ·
                refine ⟨22936406431444035788884565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15290937620962690525923043 22936406431444035788884565)
                ·
                  refine ⟨268786012868484794400991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22936406431444035788884565 268786012868484794400991)
                  ·
                    rfl

theorem cell22_2355565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_2355565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355565 prefixEnd_2355565 := by exact prefixLift 2355565
  have htrace : WordTrace (prefixWord ++ tailWord_2355565) baseStart_2355565 baseEnd_2355565 := by
    simpa [prefixWord, tailWord_2355565, baseEnd_2355565] using wordTrace_append hprefix tailTrace_2355565
  have hstable : (prefixWord ++ tailWord_2355565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355565).length < 2 ^ (prefixWord ++ tailWord_2355565).sum := by decide
  have hdescent : baseEnd_2355565 < baseStart_2355565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355614 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2355614 : Nat := 118140960795 + 2355614 * 2 ^ 59
def prefixEnd_2355614 : Nat := 4983230072969 + 3 ^ 40 * 2355614 * 2
def baseEnd_2355614 : Nat := 806374812306834588727823

theorem tailTrace_2355614 : CollatzResearch.WordTrace tailWord_2355614 prefixEnd_2355614 806374812306834588727823 := by
  unfold tailWord_2355614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10739537611002532460878237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57277533925346839791350597 10739537611002532460878237)
  ·
    refine ⟨4027326604125949672829339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10739537611002532460878237 4027326604125949672829339)
    ·
      refine ⟨6040989906188924509244009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4027326604125949672829339 6040989906188924509244009)
      ·
        refine ⟨4530742429641693381933007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6040989906188924509244009 4530742429641693381933007)
        ·
          refine ⟨6796113644462540072899511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4530742429641693381933007 6796113644462540072899511)
          ·
            refine ⟨10194170466693810109349267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6796113644462540072899511 10194170466693810109349267)
            ·
              refine ⟨15291255700040715164023901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10194170466693810109349267 15291255700040715164023901)
              ·
                refine ⟨5734220887515268186508963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15291255700040715164023901 5734220887515268186508963)
                ·
                  refine ⟨8601331331272902279763445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5734220887515268186508963 8601331331272902279763445)
                  ·
                    refine ⟨806374812306834588727823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8601331331272902279763445 806374812306834588727823)
                    ·
                      rfl

theorem cell22_2355614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2355614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355614 prefixEnd_2355614 := by exact prefixLift 2355614
  have htrace : WordTrace (prefixWord ++ tailWord_2355614) baseStart_2355614 baseEnd_2355614 := by
    simpa [prefixWord, tailWord_2355614, baseEnd_2355614] using wordTrace_append hprefix tailTrace_2355614
  have hstable : (prefixWord ++ tailWord_2355614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355614).length < 2 ^ (prefixWord ++ tailWord_2355614).sum := by decide
  have hdescent : baseEnd_2355614 < baseStart_2355614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355629 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2355629 : Nat := 118140960795 + 2355629 * 2 ^ 59
def prefixEnd_2355629 : Nat := 4983230072969 + 3 ^ 40 * 2355629 * 2
def baseEnd_2355629 : Nat := 806379947113379549602777

theorem tailTrace_2355629 : CollatzResearch.WordTrace tailWord_2355629 prefixEnd_2355629 806379947113379549602777 := by
  unfold tailWord_2355629
  simp only [CollatzResearch.WordTrace]
  refine ⟨85916847982965917248821941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57277898655310611499214627 85916847982965917248821941)
  ·
    refine ⟨8054704498403054742077057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85916847982965917248821941 8054704498403054742077057)
    ·
      refine ⟨6041028373802291056557793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8054704498403054742077057 6041028373802291056557793)
      ·
        refine ⟨4530771280351718292418345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6041028373802291056557793 4530771280351718292418345)
        ·
          refine ⟨3398078460263788719313759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4530771280351718292418345 3398078460263788719313759)
          ·
            refine ⟨5097117690395683078970639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3398078460263788719313759 5097117690395683078970639)
            ·
              refine ⟨7645676535593524618455959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5097117690395683078970639 7645676535593524618455959)
              ·
                refine ⟨11468514803390286927683939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7645676535593524618455959 11468514803390286927683939)
                ·
                  refine ⟨17202772205085430391525909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11468514803390286927683939 17202772205085430391525909)
                  ·
                    refine ⟨806379947113379549602777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17202772205085430391525909 806379947113379549602777)
                    ·
                      rfl

theorem cell22_2355629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2355629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355629 prefixEnd_2355629 := by exact prefixLift 2355629
  have htrace : WordTrace (prefixWord ++ tailWord_2355629) baseStart_2355629 baseEnd_2355629 := by
    simpa [prefixWord, tailWord_2355629, baseEnd_2355629] using wordTrace_append hprefix tailTrace_2355629
  have hstable : (prefixWord ++ tailWord_2355629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355629).length < 2 ^ (prefixWord ++ tailWord_2355629).sum := by decide
  have hdescent : baseEnd_2355629 < baseStart_2355629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355693 : List Nat := [1, 5, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_2355693 : Nat := 118140960795 + 2355693 * 2 ^ 59
def prefixEnd_2355693 : Nat := 4983230072969 + 3 ^ 40 * 2355693 * 2
def baseEnd_2355693 : Nat := 806401855621304716002581

theorem tailTrace_2355693 : CollatzResearch.WordTrace tailWord_2355693 prefixEnd_2355693 806401855621304716002581 := by
  unfold tailWord_2355693
  simp only [CollatzResearch.WordTrace]
  refine ⟨85919182254734056179151733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57279454836489370786101155 85919182254734056179151733)
  ·
    refine ⟨8054923336381317766795475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85919182254734056179151733 8054923336381317766795475)
    ·
      refine ⟨12082385004571976650193213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8054923336381317766795475 12082385004571976650193213)
      ·
        refine ⟨4530894376714491243822455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12082385004571976650193213 4530894376714491243822455)
        ·
          refine ⟨6796341565071736865733683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4530894376714491243822455 6796341565071736865733683)
          ·
            refine ⟨10194512347607605298600525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6796341565071736865733683 10194512347607605298600525)
            ·
              refine ⟨3822942130352851986975197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10194512347607605298600525 3822942130352851986975197)
              ·
                refine ⟨1433603298882319495115699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3822942130352851986975197 1433603298882319495115699)
                ·
                  refine ⟨2150404948323479242673549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1433603298882319495115699 2150404948323479242673549)
                  ·
                    refine ⟨806401855621304716002581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2150404948323479242673549 806401855621304716002581)
                    ·
                      rfl

theorem cell22_2355693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_2355693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355693 prefixEnd_2355693 := by exact prefixLift 2355693
  have htrace : WordTrace (prefixWord ++ tailWord_2355693) baseStart_2355693 baseEnd_2355693 := by
    simpa [prefixWord, tailWord_2355693, baseEnd_2355693] using wordTrace_append hprefix tailTrace_2355693
  have hstable : (prefixWord ++ tailWord_2355693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355693).length < 2 ^ (prefixWord ++ tailWord_2355693).sum := by decide
  have hdescent : baseEnd_2355693 < baseStart_2355693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355717 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 6]
def baseStart_2355717 : Nat := 118140960795 + 2355717 * 2 ^ 59
def prefixEnd_2355717 : Nat := 4983230072969 + 3 ^ 40 * 2355717 * 2
def baseEnd_2355717 : Nat := 268803357103925551134169

theorem tailTrace_2355717 : CollatzResearch.WordTrace tailWord_2355717 prefixEnd_2355717 268803357103925551134169 := by
  unfold tailWord_2355717
  simp only [CollatzResearch.WordTrace]
  refine ⟨85920057606647108278025405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57280038404431405518683603 85920057606647108278025405)
  ·
    refine ⟨32220021602492665604259527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85920057606647108278025405 32220021602492665604259527)
    ·
      refine ⟨48330032403738998406389291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32220021602492665604259527 48330032403738998406389291)
      ·
        refine ⟨72495048605608497609583937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48330032403738998406389291 72495048605608497609583937)
        ·
          refine ⟨54371286454206373207187953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72495048605608497609583937 54371286454206373207187953)
          ·
            refine ⟨40778464840654779905390965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54371286454206373207187953 40778464840654779905390965)
            ·
              refine ⟨3822981078811385616130403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40778464840654779905390965 3822981078811385616130403)
              ·
                refine ⟨5734471618217078424195605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3822981078811385616130403 5734471618217078424195605)
                ·
                  refine ⟨268803357103925551134169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5734471618217078424195605 268803357103925551134169)
                  ·
                    rfl

theorem cell22_2355717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_2355717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355717 prefixEnd_2355717 := by exact prefixLift 2355717
  have htrace : WordTrace (prefixWord ++ tailWord_2355717) baseStart_2355717 baseEnd_2355717 := by
    simpa [prefixWord, tailWord_2355717, baseEnd_2355717] using wordTrace_append hprefix tailTrace_2355717
  have hstable : (prefixWord ++ tailWord_2355717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355717).length < 2 ^ (prefixWord ++ tailWord_2355717).sum := by decide
  have hdescent : baseEnd_2355717 < baseStart_2355717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355736 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 1, 4]
def baseStart_2355736 : Nat := 118140960795 + 2355736 * 2 ^ 59
def prefixEnd_2355736 : Nat := 4983230072969 + 3 ^ 40 * 2355736 * 2
def baseEnd_2355736 : Nat := 806416575400066937177449

theorem tailTrace_2355736 : CollatzResearch.WordTrace tailWord_2355736 prefixEnd_2355736 806416575400066937177449 := by
  unfold tailWord_2355736
  simp only [CollatzResearch.WordTrace]
  refine ⟨42960375296789137261483531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57280500395718849681978041 42960375296789137261483531)
  ·
    refine ⟨64440562945183705892225297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42960375296789137261483531 64440562945183705892225297)
    ·
      refine ⟨48330422208887779419168973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64440562945183705892225297 48330422208887779419168973)
      ·
        refine ⟨18123908328332917282188365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48330422208887779419168973 18123908328332917282188365)
        ·
          refine ⟨6796465623124843980820637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18123908328332917282188365 6796465623124843980820637)
          ·
            refine ⟨2548674608671816492807739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6796465623124843980820637 2548674608671816492807739)
            ·
              refine ⟨3823011913007724739211609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2548674608671816492807739 3823011913007724739211609)
              ·
                refine ⟨2867258934755793554408707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3823011913007724739211609 2867258934755793554408707)
                ·
                  refine ⟨4300888402133690331613061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867258934755793554408707 4300888402133690331613061)
                  ·
                    refine ⟨806416575400066937177449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4300888402133690331613061 806416575400066937177449)
                    ·
                      rfl

theorem cell22_2355736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_2355736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355736 prefixEnd_2355736 := by exact prefixLift 2355736
  have htrace : WordTrace (prefixWord ++ tailWord_2355736) baseStart_2355736 baseEnd_2355736 := by
    simpa [prefixWord, tailWord_2355736, baseEnd_2355736] using wordTrace_append hprefix tailTrace_2355736
  have hstable : (prefixWord ++ tailWord_2355736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355736).length < 2 ^ (prefixWord ++ tailWord_2355736).sum := by decide
  have hdescent : baseEnd_2355736 < baseStart_2355736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355824 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 7]
def baseStart_2355824 : Nat := 118140960795 + 2355824 * 2 ^ 59
def prefixEnd_2355824 : Nat := 4983230072969 + 3 ^ 40 * 2355824 * 2
def baseEnd_2355824 : Nat := 268815566532821346992393

theorem tailTrace_2355824 : CollatzResearch.WordTrace tailWord_2355824 prefixEnd_2355824 268815566532821346992393 := by
  unfold tailWord_2355824
  simp only [CollatzResearch.WordTrace]
  refine ⟨42961980108629732776085263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57282640144839643701447017 42961980108629732776085263)
  ·
    refine ⟨64442970162944599164127895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42961980108629732776085263 64442970162944599164127895)
    ·
      refine ⟨96664455244416898746191843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64442970162944599164127895 96664455244416898746191843)
      ·
        refine ⟨144996682866625348119287765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96664455244416898746191843 144996682866625348119287765)
        ·
          refine ⟨3398359754686531596545807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 144996682866625348119287765 3398359754686531596545807)
          ·
            refine ⟨5097539632029797394818711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3398359754686531596545807 5097539632029797394818711)
            ·
              refine ⟨7646309448044696092228067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5097539632029797394818711 7646309448044696092228067)
              ·
                refine ⟨11469464172067044138342101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7646309448044696092228067 11469464172067044138342101)
                ·
                  refine ⟨268815566532821346992393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11469464172067044138342101 268815566532821346992393)
                  ·
                    rfl

theorem cell22_2355824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_2355824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355824 prefixEnd_2355824 := by exact prefixLift 2355824
  have htrace : WordTrace (prefixWord ++ tailWord_2355824) baseStart_2355824 baseEnd_2355824 := by
    simpa [prefixWord, tailWord_2355824, baseEnd_2355824] using wordTrace_append hprefix tailTrace_2355824
  have hstable : (prefixWord ++ tailWord_2355824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355824).length < 2 ^ (prefixWord ++ tailWord_2355824).sum := by decide
  have hdescent : baseEnd_2355824 < baseStart_2355824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355841 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 5]
def baseStart_2355841 : Nat := 118140960795 + 2355841 * 2 ^ 59
def prefixEnd_2355841 : Nat := 4983230072969 + 3 ^ 40 * 2355841 * 2
def baseEnd_2355841 : Nat := 268817506348627221100709

theorem tailTrace_2355841 : CollatzResearch.WordTrace tailWord_2355841 prefixEnd_2355841 268817506348627221100709 := by
  unfold tailWord_2355841
  simp only [CollatzResearch.WordTrace]
  refine ⟨85924580258197877455539377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57283053505465251637026251 85924580258197877455539377)
  ·
    refine ⟨64443435193648408091654533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85924580258197877455539377 64443435193648408091654533)
    ·
      refine ⟨12083144098809076517185225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64443435193648408091654533 12083144098809076517185225)
      ·
        refine ⟨9062358074106807387888919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12083144098809076517185225 9062358074106807387888919)
        ·
          refine ⟨13593537111160211081833379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9062358074106807387888919 13593537111160211081833379)
          ·
            refine ⟨20390305666740316622750069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13593537111160211081833379 20390305666740316622750069)
            ·
              refine ⟨1911591156256904683382819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20390305666740316622750069 1911591156256904683382819)
              ·
                refine ⟨2867386734385357025074229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911591156256904683382819 2867386734385357025074229)
                ·
                  refine ⟨268817506348627221100709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2867386734385357025074229 268817506348627221100709)
                  ·
                    rfl

theorem cell22_2355841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 5].length) (baseStart_2355841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355841 prefixEnd_2355841 := by exact prefixLift 2355841
  have htrace : WordTrace (prefixWord ++ tailWord_2355841) baseStart_2355841 baseEnd_2355841 := by
    simpa [prefixWord, tailWord_2355841, baseEnd_2355841] using wordTrace_append hprefix tailTrace_2355841
  have hstable : (prefixWord ++ tailWord_2355841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355841).length < 2 ^ (prefixWord ++ tailWord_2355841).sum := by decide
  have hdescent : baseEnd_2355841 < baseStart_2355841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355852 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 8]
def baseStart_2355852 : Nat := 118140960795 + 2355852 * 2 ^ 59
def prefixEnd_2355852 : Nat := 4983230072969 + 3 ^ 40 * 2355852 * 2
def baseEnd_2355852 : Nat := 268818761523560433759031

theorem tailTrace_2355852 : CollatzResearch.WordTrace tailWord_2355852 prefixEnd_2355852 268818761523560433759031 := by
  unfold tailWord_2355852
  simp only [CollatzResearch.WordTrace]
  refine ⟨42962490730579013167094905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57283320974105350889459873 42962490730579013167094905)
  ·
    refine ⟨32221868047934259875321179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42962490730579013167094905 32221868047934259875321179)
    ·
      refine ⟨48332802071901389812981769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32221868047934259875321179 48332802071901389812981769)
      ·
        refine ⟨36249601553926042359736327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48332802071901389812981769 36249601553926042359736327)
        ·
          refine ⟨54374402330889063539604491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36249601553926042359736327 54374402330889063539604491)
          ·
            refine ⟨81561603496333595309406737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54374402330889063539604491 81561603496333595309406737)
            ·
              refine ⟨61171202622250196482055053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81561603496333595309406737 61171202622250196482055053)
              ·
                refine ⟨22939200983343823680770645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61171202622250196482055053 22939200983343823680770645)
                ·
                  refine ⟨268818761523560433759031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22939200983343823680770645 268818761523560433759031)
                  ·
                    rfl

theorem cell22_2355852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_2355852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355852 prefixEnd_2355852 := by exact prefixLift 2355852
  have htrace : WordTrace (prefixWord ++ tailWord_2355852) baseStart_2355852 baseEnd_2355852 := by
    simpa [prefixWord, tailWord_2355852, baseEnd_2355852] using wordTrace_append hprefix tailTrace_2355852
  have hstable : (prefixWord ++ tailWord_2355852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355852).length < 2 ^ (prefixWord ++ tailWord_2355852).sum := by decide
  have hdescent : baseEnd_2355852 < baseStart_2355852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355867 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 7, 5]
def baseStart_2355867 : Nat := 118140960795 + 2355867 * 2 ^ 59
def prefixEnd_2355867 : Nat := 4983230072969 + 3 ^ 40 * 2355867 * 2
def baseEnd_2355867 : Nat := 806461419377226262152047

theorem tailTrace_2355867 : CollatzResearch.WordTrace tailWord_2355867 prefixEnd_2355867 806461419377226262152047 := by
  unfold tailWord_2355867
  simp only [CollatzResearch.WordTrace]
  refine ⟨85925528556103683895985855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57283685704069122597323903 85925528556103683895985855)
  ·
    refine ⟨128888292834155525843978783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85925528556103683895985855 128888292834155525843978783)
    ·
      refine ⟨193332439251233288765968175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128888292834155525843978783 193332439251233288765968175)
      ·
        refine ⟨289998658876849933148952263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193332439251233288765968175 289998658876849933148952263)
        ·
          refine ⟨434997988315274899723428395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289998658876849933148952263 434997988315274899723428395)
          ·
            refine ⟨652496982472912349585142593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434997988315274899723428395 652496982472912349585142593)
            ·
              refine ⟨489372736854684262188856945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652496982472912349585142593 489372736854684262188856945)
              ·
                refine ⟨367029552641013196641642709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489372736854684262188856945 367029552641013196641642709)
                ·
                  refine ⟨8602255140023746796288501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 367029552641013196641642709 8602255140023746796288501)
                  ·
                    refine ⟨806461419377226262152047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8602255140023746796288501 806461419377226262152047)
                    ·
                      rfl

theorem cell22_2355867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_2355867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355867 prefixEnd_2355867 := by exact prefixLift 2355867
  have htrace : WordTrace (prefixWord ++ tailWord_2355867) baseStart_2355867 baseEnd_2355867 := by
    simpa [prefixWord, tailWord_2355867, baseEnd_2355867] using wordTrace_append hprefix tailTrace_2355867
  have hstable : (prefixWord ++ tailWord_2355867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355867).length < 2 ^ (prefixWord ++ tailWord_2355867).sum := by decide
  have hdescent : baseEnd_2355867 < baseStart_2355867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355914 : List Nat := [3, 1, 2, 1, 4, 1, 2, 8]
def baseStart_2355914 : Nat := 118140960795 + 2355914 * 2 ^ 59
def prefixEnd_2355914 : Nat := 4983230072969 + 3 ^ 40 * 2355914 * 2
def baseEnd_2355914 : Nat := 89608612048637089580767

theorem tailTrace_2355914 : CollatzResearch.WordTrace tailWord_2355914 prefixEnd_2355914 89608612048637089580767 := by
  unfold tailWord_2355914
  simp only [CollatzResearch.WordTrace]
  refine ⟨21481810696733352730736699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57284828524622273948631197 21481810696733352730736699)
  ·
    refine ⟨32222716045100029096105049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21481810696733352730736699 32222716045100029096105049)
    ·
      refine ⟨24167037033825021822078787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32222716045100029096105049 24167037033825021822078787)
      ·
        refine ⟨36250555550737532733118181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24167037033825021822078787 36250555550737532733118181)
        ·
          refine ⟨6796979165763287387459659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36250555550737532733118181 6796979165763287387459659)
          ·
            refine ⟨10195468748644931081189489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6796979165763287387459659 10195468748644931081189489)
            ·
              refine ⟨7646601561483698310892117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10195468748644931081189489 7646601561483698310892117)
              ·
                refine ⟨89608612048637089580767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7646601561483698310892117 89608612048637089580767)
                ·
                  rfl

theorem cell22_2355914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_2355914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355914 prefixEnd_2355914 := by exact prefixLift 2355914
  have htrace : WordTrace (prefixWord ++ tailWord_2355914) baseStart_2355914 baseEnd_2355914 := by
    simpa [prefixWord, tailWord_2355914, baseEnd_2355914] using wordTrace_append hprefix tailTrace_2355914
  have hstable : (prefixWord ++ tailWord_2355914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355914).length < 2 ^ (prefixWord ++ tailWord_2355914).sum := by decide
  have hdescent : baseEnd_2355914 < baseStart_2355914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355916 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_2355916 : Nat := 118140960795 + 2355916 * 2 ^ 59
def prefixEnd_2355916 : Nat := 4983230072969 + 3 ^ 40 * 2355916 * 2
def baseEnd_2355916 : Nat := 806478193078606467676897

theorem tailTrace_2355916 : CollatzResearch.WordTrace tailWord_2355916 prefixEnd_2355916 806478193078606467676897 := by
  unfold tailWord_2355916
  simp only [CollatzResearch.WordTrace]
  refine ⟨42963657866463082632259801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57284877155284110176346401 42963657866463082632259801)
  ·
    refine ⟨32222743399847311974194851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42963657866463082632259801 32222743399847311974194851)
    ·
      refine ⟨48334115099770967961292277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32222743399847311974194851 48334115099770967961292277)
      ·
        refine ⟨4531323290603528246371151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48334115099770967961292277 4531323290603528246371151)
        ·
          refine ⟨6796984935905292369556727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4531323290603528246371151 6796984935905292369556727)
          ·
            refine ⟨10195477403857938554335091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6796984935905292369556727 10195477403857938554335091)
            ·
              refine ⟨15293216105786907831502637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10195477403857938554335091 15293216105786907831502637)
              ·
                refine ⟨5734956039670090436813489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15293216105786907831502637 5734956039670090436813489)
                ·
                  refine ⟨4301217029752567827610117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5734956039670090436813489 4301217029752567827610117)
                  ·
                    refine ⟨806478193078606467676897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4301217029752567827610117 806478193078606467676897)
                    ·
                      rfl

theorem cell22_2355916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_2355916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355916 prefixEnd_2355916 := by exact prefixLift 2355916
  have htrace : WordTrace (prefixWord ++ tailWord_2355916) baseStart_2355916 baseEnd_2355916 := by
    simpa [prefixWord, tailWord_2355916, baseEnd_2355916] using wordTrace_append hprefix tailTrace_2355916
  have hstable : (prefixWord ++ tailWord_2355916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355916).length < 2 ^ (prefixWord ++ tailWord_2355916).sum := by decide
  have hdescent : baseEnd_2355916 < baseStart_2355916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2355946 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 3, 3]
def baseStart_2355946 : Nat := 118140960795 + 2355946 * 2 ^ 59
def prefixEnd_2355946 : Nat := 4983230072969 + 3 ^ 40 * 2355946 * 2
def baseEnd_2355946 : Nat := 806488462691696389426805

theorem tailTrace_2355946 : CollatzResearch.WordTrace tailWord_2355946 prefixEnd_2355946 806488462691696389426805 := by
  unfold tailWord_2355946
  simp only [CollatzResearch.WordTrace]
  refine ⟨21482102480704370097027923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57285606615211653592074461 21482102480704370097027923)
  ·
    refine ⟨32223153721056555145541885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21482102480704370097027923 32223153721056555145541885)
    ·
      refine ⟨12083682645396208179578207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32223153721056555145541885 12083682645396208179578207)
      ·
        refine ⟨18125523968094312269367311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12083682645396208179578207 18125523968094312269367311)
        ·
          refine ⟨27188285952141468404050967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18125523968094312269367311 27188285952141468404050967)
          ·
            refine ⟨40782428928212202606076451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27188285952141468404050967 40782428928212202606076451)
            ·
              refine ⟨61173643392318303909114677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40782428928212202606076451 61173643392318303909114677)
              ·
                refine ⟨5735029068029840991479501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61173643392318303909114677 5735029068029840991479501)
                ·
                  refine ⟨2150635900511190371804813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5735029068029840991479501 2150635900511190371804813)
                  ·
                    refine ⟨806488462691696389426805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2150635900511190371804813 806488462691696389426805)
                    ·
                      rfl

theorem cell22_2355946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_2355946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2355946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2355946 prefixEnd_2355946 := by exact prefixLift 2355946
  have htrace : WordTrace (prefixWord ++ tailWord_2355946) baseStart_2355946 baseEnd_2355946 := by
    simpa [prefixWord, tailWord_2355946, baseEnd_2355946] using wordTrace_append hprefix tailTrace_2355946
  have hstable : (prefixWord ++ tailWord_2355946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2355946).length < 2 ^ (prefixWord ++ tailWord_2355946).sum := by decide
  have hdescent : baseEnd_2355946 < baseStart_2355946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2355946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356021 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 6]
def baseStart_2356021 : Nat := 118140960795 + 2356021 * 2 ^ 59
def prefixEnd_2356021 : Nat := 4983230072969 + 3 ^ 40 * 2356021 * 2
def baseEnd_2356021 : Nat := 268838045574807064600525

theorem tailTrace_2356021 : CollatzResearch.WordTrace tailWord_2356021 prefixEnd_2356021 268838045574807064600525 := by
  unfold tailWord_2356021
  simp only [CollatzResearch.WordTrace]
  refine ⟨85931145397545768197091917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57287430265030512131394611 85931145397545768197091917)
  ·
    refine ⟨32224179524079663073909469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85931145397545768197091917 32224179524079663073909469)
    ·
      refine ⟨12084067321529873652716051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32224179524079663073909469 12084067321529873652716051)
      ·
        refine ⟨18126100982294810479074077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12084067321529873652716051 18126100982294810479074077)
        ·
          refine ⟨6797287868360553929652779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18126100982294810479074077 6797287868360553929652779)
          ·
            refine ⟨10195931802540830894479169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6797287868360553929652779 10195931802540830894479169)
            ·
              refine ⟨7646948851905623170859377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10195931802540830894479169 7646948851905623170859377)
              ·
                refine ⟨5735211638929217378144533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7646948851905623170859377 5735211638929217378144533)
                ·
                  refine ⟨268838045574807064600525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5735211638929217378144533 268838045574807064600525)
                  ·
                    rfl

theorem cell22_2356021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_2356021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356021 prefixEnd_2356021 := by exact prefixLift 2356021
  have htrace : WordTrace (prefixWord ++ tailWord_2356021) baseStart_2356021 baseEnd_2356021 := by
    simpa [prefixWord, tailWord_2356021, baseEnd_2356021] using wordTrace_append hprefix tailTrace_2356021
  have hstable : (prefixWord ++ tailWord_2356021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356021).length < 2 ^ (prefixWord ++ tailWord_2356021).sum := by decide
  have hdescent : baseEnd_2356021 < baseStart_2356021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356053 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 2, 3]
def baseStart_2356053 : Nat := 118140960795 + 2356053 * 2 ^ 59
def prefixEnd_2356053 : Nat := 4983230072969 + 3 ^ 40 * 2356053 * 2
def baseEnd_2356053 : Nat := 806525090978383777001477

theorem tailTrace_2356053 : CollatzResearch.WordTrace tailWord_2356053 prefixEnd_2356053 806525090978383777001477 := by
  unfold tailWord_2356053
  simp only [CollatzResearch.WordTrace]
  refine ⟨85932312533429837662256813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57288208355619891774837875 85932312533429837662256813)
  ·
    refine ⟨32224617200036189123346305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85932312533429837662256813 32224617200036189123346305)
    ·
      refine ⟨24168462900027141842509729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32224617200036189123346305 24168462900027141842509729)
      ·
        refine ⟨18126347175020356381882297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24168462900027141842509729 18126347175020356381882297)
        ·
          refine ⟨13594760381265267286411723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18126347175020356381882297 13594760381265267286411723)
          ·
            refine ⟨20392140571897900929617585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13594760381265267286411723 20392140571897900929617585)
            ·
              refine ⟨15294105428923425697213189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20392140571897900929617585 15294105428923425697213189)
              ·
                refine ⟨2867644767923142318227473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15294105428923425697213189 2867644767923142318227473)
                ·
                  refine ⟨2150733575942356738670605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2867644767923142318227473 2150733575942356738670605)
                  ·
                    refine ⟨806525090978383777001477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2150733575942356738670605 806525090978383777001477)
                    ·
                      rfl

theorem cell22_2356053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_2356053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356053 prefixEnd_2356053 := by exact prefixLift 2356053
  have htrace : WordTrace (prefixWord ++ tailWord_2356053) baseStart_2356053 baseEnd_2356053 := by
    simpa [prefixWord, tailWord_2356053, baseEnd_2356053] using wordTrace_append hprefix tailTrace_2356053
  have hstable : (prefixWord ++ tailWord_2356053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356053).length < 2 ^ (prefixWord ++ tailWord_2356053).sum := by decide
  have hdescent : baseEnd_2356053 < baseStart_2356053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356055 : List Nat := [1, 1, 3, 2, 4, 2, 3, 2, 4]
def baseStart_2356055 : Nat := 118140960795 + 2356055 * 2 ^ 59
def prefixEnd_2356055 : Nat := 4983230072969 + 3 ^ 40 * 2356055 * 2
def baseEnd_2356055 : Nat := 268841925206418812817157

theorem tailTrace_2356055 : CollatzResearch.WordTrace tailWord_2356055 prefixEnd_2356055 268841925206418812817157 := by
  unfold tailWord_2356055
  simp only [CollatzResearch.WordTrace]
  refine ⟨85932385479422592003829619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57288256986281728002553079 85932385479422592003829619)
  ·
    refine ⟨128898578219133888005744429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85932385479422592003829619 128898578219133888005744429)
    ·
      refine ⟨48336966832175208002154161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128898578219133888005744429 48336966832175208002154161)
      ·
        refine ⟨36252725124131406001615621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48336966832175208002154161 36252725124131406001615621)
        ·
          refine ⟨6797385960774638625302929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36252725124131406001615621 6797385960774638625302929)
          ·
            refine ⟨5098039470580978968977197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6797385960774638625302929 5098039470580978968977197)
            ·
              refine ⟨1911764801467867113366449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5098039470580978968977197 1911764801467867113366449)
              ·
                refine ⟨1433823601100900335024837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1911764801467867113366449 1433823601100900335024837)
                ·
                  refine ⟨268841925206418812817157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1433823601100900335024837 268841925206418812817157)
                  ·
                    rfl

theorem cell22_2356055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 4].length) (baseStart_2356055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356055 prefixEnd_2356055 := by exact prefixLift 2356055
  have htrace : WordTrace (prefixWord ++ tailWord_2356055) baseStart_2356055 baseEnd_2356055 := by
    simpa [prefixWord, tailWord_2356055, baseEnd_2356055] using wordTrace_append hprefix tailTrace_2356055
  have hstable : (prefixWord ++ tailWord_2356055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356055).length < 2 ^ (prefixWord ++ tailWord_2356055).sum := by decide
  have hdescent : baseEnd_2356055 < baseStart_2356055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356280 : List Nat := [2, 1, 2, 1, 5, 2, 2, 2, 5]
def baseStart_2356280 : Nat := 118140960795 + 2356280 * 2 ^ 59
def prefixEnd_2356280 : Nat := 4983230072969 + 3 ^ 40 * 2356280 * 2
def baseEnd_2356280 : Nat := 268867599239143617191927

theorem tailTrace_2356280 : CollatzResearch.WordTrace tailWord_2356280 prefixEnd_2356280 268867599239143617191927 := by
  unfold tailWord_2356280
  simp only [CollatzResearch.WordTrace]
  refine ⟨42970295951803727715385147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57293727935738303620513529 42970295951803727715385147)
  ·
    refine ⟨64455443927705591573077721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42970295951803727715385147 64455443927705591573077721)
    ·
      refine ⟨48341582945779193679808291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64455443927705591573077721 48341582945779193679808291)
      ·
        refine ⟨72512374418668790519712437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48341582945779193679808291 72512374418668790519712437)
        ·
          refine ⟨6798035101750199111223041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72512374418668790519712437 6798035101750199111223041)
          ·
            refine ⟨5098526326312649333417281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6798035101750199111223041 5098526326312649333417281)
            ·
              refine ⟨3823894744734487000062961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5098526326312649333417281 3823894744734487000062961)
              ·
                refine ⟨2867921058550865250047221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3823894744734487000062961 2867921058550865250047221)
                ·
                  refine ⟨268867599239143617191927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2867921058550865250047221 268867599239143617191927)
                  ·
                    rfl

theorem cell22_2356280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 2, 5].length) (baseStart_2356280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356280 prefixEnd_2356280 := by exact prefixLift 2356280
  have htrace : WordTrace (prefixWord ++ tailWord_2356280) baseStart_2356280 baseEnd_2356280 := by
    simpa [prefixWord, tailWord_2356280, baseEnd_2356280] using wordTrace_append hprefix tailTrace_2356280
  have hstable : (prefixWord ++ tailWord_2356280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356280).length < 2 ^ (prefixWord ++ tailWord_2356280).sum := by decide
  have hdescent : baseEnd_2356280 < baseStart_2356280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356284 : List Nat := [2, 2, 2, 2, 2, 2, 4, 2, 1, 3]
def baseStart_2356284 : Nat := 118140960795 + 2356284 * 2 ^ 59
def prefixEnd_2356284 : Nat := 4983230072969 + 3 ^ 40 * 2356284 * 2
def baseEnd_2356284 : Nat := 806604166999176174475769

theorem tailTrace_2356284 : CollatzResearch.WordTrace tailWord_2356284 prefixEnd_2356284 806604166999176174475769 := by
  unfold tailWord_2356284
  simp only [CollatzResearch.WordTrace]
  refine ⟨42970368897796482056957953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57293825197061976075943937 42970368897796482056957953)
  ·
    refine ⟨32227776673347361542718465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42970368897796482056957953 32227776673347361542718465)
    ·
      refine ⟨24170832505010521157038849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32227776673347361542718465 24170832505010521157038849)
      ·
        refine ⟨18128124378757890867779137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24170832505010521157038849 18128124378757890867779137)
        ·
          refine ⟨13596093284068418150834353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18128124378757890867779137 13596093284068418150834353)
          ·
            refine ⟨10197069963051313613125765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13596093284068418150834353 10197069963051313613125765)
            ·
              refine ⟨1911950618072121302461081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10197069963051313613125765 1911950618072121302461081)
              ·
                refine ⟨1433962963554090976845811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1911950618072121302461081 1433962963554090976845811)
                ·
                  refine ⟨2150944445331136465268717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1433962963554090976845811 2150944445331136465268717)
                  ·
                    refine ⟨806604166999176174475769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2150944445331136465268717 806604166999176174475769)
                    ·
                      rfl

theorem cell22_2356284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_2356284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356284 prefixEnd_2356284 := by exact prefixLift 2356284
  have htrace : WordTrace (prefixWord ++ tailWord_2356284) baseStart_2356284 baseEnd_2356284 := by
    simpa [prefixWord, tailWord_2356284, baseEnd_2356284] using wordTrace_append hprefix tailTrace_2356284
  have hstable : (prefixWord ++ tailWord_2356284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356284).length < 2 ^ (prefixWord ++ tailWord_2356284).sum := by decide
  have hdescent : baseEnd_2356284 < baseStart_2356284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356293 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_2356293 : Nat := 118140960795 + 2356293 * 2 ^ 59
def prefixEnd_2356293 : Nat := 4983230072969 + 3 ^ 40 * 2356293 * 2
def baseEnd_2356293 : Nat := 806607247883103151000741

theorem tailTrace_2356293 : CollatzResearch.WordTrace tailWord_2356293 prefixEnd_2356293 806607247883103151000741 := by
  unfold tailWord_2356293
  simp only [CollatzResearch.WordTrace]
  refine ⟨85941066052560358650993533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57294044035040239100662355 85941066052560358650993533)
  ·
    refine ⟨32227899769710134494122575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85941066052560358650993533 32227899769710134494122575)
    ·
      refine ⟨48341849654565201741183863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32227899769710134494122575 48341849654565201741183863)
      ·
        refine ⟨72512774481847802611775795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48341849654565201741183863 72512774481847802611775795)
        ·
          refine ⟨108769161722771703917663693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72512774481847802611775795 108769161722771703917663693)
          ·
            refine ⟨40788435646039388969123885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108769161722771703917663693 40788435646039388969123885)
            ·
              refine ⟨15295663367264770863421457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40788435646039388969123885 15295663367264770863421457)
              ·
                refine ⟨11471747525448578147566093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15295663367264770863421457 11471747525448578147566093)
                ·
                  refine ⟨4301905322043216805337285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11471747525448578147566093 4301905322043216805337285)
                  ·
                    refine ⟨806607247883103151000741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4301905322043216805337285 806607247883103151000741)
                    ·
                      rfl

theorem cell22_2356293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_2356293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356293 prefixEnd_2356293 := by exact prefixLift 2356293
  have htrace : WordTrace (prefixWord ++ tailWord_2356293) baseStart_2356293 baseEnd_2356293 := by
    simpa [prefixWord, tailWord_2356293, baseEnd_2356293] using wordTrace_append hprefix tailTrace_2356293
  have hstable : (prefixWord ++ tailWord_2356293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356293).length < 2 ^ (prefixWord ++ tailWord_2356293).sum := by decide
  have hdescent : baseEnd_2356293 < baseStart_2356293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356308 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 8]
def baseStart_2356308 : Nat := 118140960795 + 2356308 * 2 ^ 59
def prefixEnd_2356308 : Nat := 4983230072969 + 3 ^ 40 * 2356308 * 2
def baseEnd_2356308 : Nat := 268870794229882703958565

theorem tailTrace_2356308 : CollatzResearch.WordTrace tailWord_2356308 prefixEnd_2356308 268870794229882703958565 := by
  unfold tailWord_2356308
  simp only [CollatzResearch.WordTrace]
  refine ⟨42970806573753008106394789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57294408765004010808526385 42970806573753008106394789)
  ·
    refine ⟨8057026232578689019949023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42970806573753008106394789 8057026232578689019949023)
    ·
      refine ⟨12085539348868033529923535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8057026232578689019949023 12085539348868033529923535)
      ·
        refine ⟨18128309023302050294885303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12085539348868033529923535 18128309023302050294885303)
        ·
          refine ⟨27192463534953075442327955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18128309023302050294885303 27192463534953075442327955)
          ·
            refine ⟨40788695302429613163491933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27192463534953075442327955 40788695302429613163491933)
            ·
              refine ⟨15295760738411104936309475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40788695302429613163491933 15295760738411104936309475)
              ·
                refine ⟨22943641107616657404464213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15295760738411104936309475 22943641107616657404464213)
                ·
                  refine ⟨268870794229882703958565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22943641107616657404464213 268870794229882703958565)
                  ·
                    rfl

theorem cell22_2356308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_2356308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356308 prefixEnd_2356308 := by exact prefixLift 2356308
  have htrace : WordTrace (prefixWord ++ tailWord_2356308) baseStart_2356308 baseEnd_2356308 := by
    simpa [prefixWord, tailWord_2356308, baseEnd_2356308] using wordTrace_append hprefix tailTrace_2356308
  have hstable : (prefixWord ++ tailWord_2356308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356308).length < 2 ^ (prefixWord ++ tailWord_2356308).sum := by decide
  have hdescent : baseEnd_2356308 < baseStart_2356308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356318 : List Nat := [4, 4, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2356318 : Nat := 118140960795 + 2356318 * 2 ^ 59
def prefixEnd_2356318 : Nat := 4983230072969 + 3 ^ 40 * 2356318 * 2
def baseEnd_2356318 : Nat := 806615805894011419125665

theorem tailTrace_2356318 : CollatzResearch.WordTrace tailWord_2356318 prefixEnd_2356318 806615805894011419125665 := by
  unfold tailWord_2356318
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742747234683723490081701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57294651918313191947102405 10742747234683723490081701)
  ·
    refine ⟨2014265106503198154390319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10742747234683723490081701 2014265106503198154390319)
    ·
      refine ⟨3021397659754797231585479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2014265106503198154390319 3021397659754797231585479)
      ·
        refine ⟨4532096489632195847378219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3021397659754797231585479 4532096489632195847378219)
        ·
          refine ⟨6798144734448293771067329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4532096489632195847378219 6798144734448293771067329)
          ·
            refine ⟨5098608550836220328300497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6798144734448293771067329 5098608550836220328300497)
            ·
              refine ⟨3823956413127165246225373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5098608550836220328300497 3823956413127165246225373)
              ·
                refine ⟨1433983654922686967334515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3823956413127165246225373 1433983654922686967334515)
                ·
                  refine ⟨2150975482384030451001773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1433983654922686967334515 2150975482384030451001773)
                  ·
                    refine ⟨806615805894011419125665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2150975482384030451001773 806615805894011419125665)
                    ·
                      rfl

theorem cell22_2356318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2356318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356318 prefixEnd_2356318 := by exact prefixLift 2356318
  have htrace : WordTrace (prefixWord ++ tailWord_2356318) baseStart_2356318 baseEnd_2356318 := by
    simpa [prefixWord, tailWord_2356318, baseEnd_2356318] using wordTrace_append hprefix tailTrace_2356318
  have hstable : (prefixWord ++ tailWord_2356318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356318).length < 2 ^ (prefixWord ++ tailWord_2356318).sum := by decide
  have hdescent : baseEnd_2356318 < baseStart_2356318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356327 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 1, 4]
def baseStart_2356327 : Nat := 118140960795 + 2356327 * 2 ^ 59
def prefixEnd_2356327 : Nat := 4983230072969 + 3 ^ 40 * 2356327 * 2
def baseEnd_2356327 : Nat := 806618886777938395650637

theorem tailTrace_2356327 : CollatzResearch.WordTrace tailWord_2356327 prefixEnd_2356327 806618886777938395650637 := by
  unfold tailWord_2356327
  simp only [CollatzResearch.WordTrace]
  refine ⟨85942306134437182457731235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57294870756291454971820823 85942306134437182457731235)
  ·
    refine ⟨128913459201655773686596853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85942306134437182457731235 128913459201655773686596853)
    ·
      refine ⟨12085636800155228783118455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128913459201655773686596853 12085636800155228783118455)
      ·
        refine ⟨18128455200232843174677683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12085636800155228783118455 18128455200232843174677683)
        ·
          refine ⟨27192682800349264762016525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18128455200232843174677683 27192682800349264762016525)
          ·
            refine ⟨10197256050130974285756197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27192682800349264762016525 10197256050130974285756197)
            ·
              refine ⟨1911985509399557678579287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10197256050130974285756197 1911985509399557678579287)
              ·
                refine ⟨2867978264099336517868931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1911985509399557678579287 2867978264099336517868931)
                ·
                  refine ⟨4301967396149004776803397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867978264099336517868931 4301967396149004776803397)
                  ·
                    refine ⟨806618886777938395650637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4301967396149004776803397 806618886777938395650637)
                    ·
                      rfl

theorem cell22_2356327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_2356327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356327 prefixEnd_2356327 := by exact prefixLift 2356327
  have htrace : WordTrace (prefixWord ++ tailWord_2356327) baseStart_2356327 baseEnd_2356327 := by
    simpa [prefixWord, tailWord_2356327, baseEnd_2356327] using wordTrace_append hprefix tailTrace_2356327
  have hstable : (prefixWord ++ tailWord_2356327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356327).length < 2 ^ (prefixWord ++ tailWord_2356327).sum := by decide
  have hdescent : baseEnd_2356327 < baseStart_2356327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356342 : List Nat := [5, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_2356342 : Nat := 118140960795 + 2356342 * 2 ^ 59
def prefixEnd_2356342 : Nat := 4983230072969 + 3 ^ 40 * 2356342 * 2
def baseEnd_2356342 : Nat := 268874673861494452175197

theorem tailTrace_2356342 : CollatzResearch.WordTrace tailWord_2356342 prefixEnd_2356342 268874673861494452175197 := by
  unfold tailWord_2356342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5371428326836427501220455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57295235486255226679684853 5371428326836427501220455)
  ·
    refine ⟨8057142490254641251830683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5371428326836427501220455 8057142490254641251830683)
    ·
      refine ⟨12085713735381961877746025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8057142490254641251830683 12085713735381961877746025)
      ·
        refine ⟨9064285301536471408309519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12085713735381961877746025 9064285301536471408309519)
        ·
          refine ⟨13596427952304707112464279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9064285301536471408309519 13596427952304707112464279)
          ·
            refine ⟨20394641928457060668696419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13596427952304707112464279 20394641928457060668696419)
            ·
              refine ⟨30591962892685591003044629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20394641928457060668696419 30591962892685591003044629)
              ·
                refine ⟨1433998260594637078267717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30591962892685591003044629 1433998260594637078267717)
                ·
                  refine ⟨268874673861494452175197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1433998260594637078267717 268874673861494452175197)
                  ·
                    rfl

theorem cell22_2356342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_2356342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356342 prefixEnd_2356342 := by exact prefixLift 2356342
  have htrace : WordTrace (prefixWord ++ tailWord_2356342) baseStart_2356342 baseEnd_2356342 := by
    simpa [prefixWord, tailWord_2356342, baseEnd_2356342] using wordTrace_append hprefix tailTrace_2356342
  have hstable : (prefixWord ++ tailWord_2356342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356342).length < 2 ^ (prefixWord ++ tailWord_2356342).sum := by decide
  have hdescent : baseEnd_2356342 < baseStart_2356342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356357 : List Nat := [1, 3, 1, 1, 6, 2, 1, 1, 1, 5]
def baseStart_2356357 : Nat := 118140960795 + 2356357 * 2 ^ 59
def prefixEnd_2356357 : Nat := 4983230072969 + 3 ^ 40 * 2356357 * 2
def baseEnd_2356357 : Nat := 806629156391028317400545

theorem tailTrace_2356357 : CollatzResearch.WordTrace tailWord_2356357 prefixEnd_2356357 806629156391028317400545 := by
  unfold tailWord_2356357
  simp only [CollatzResearch.WordTrace]
  refine ⟨85943400324328497581323325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57295600216218998387548883 85943400324328497581323325)
  ·
    refine ⟨32228775121623186592996247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85943400324328497581323325 32228775121623186592996247)
    ·
      refine ⟨48343162682434779889494371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32228775121623186592996247 48343162682434779889494371)
      ·
        refine ⟨72514744023652169834241557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48343162682434779889494371 72514744023652169834241557)
        ·
          refine ⟨3399128626108695460980073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72514744023652169834241557 3399128626108695460980073)
          ·
            refine ⟨2549346469581521595735055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3399128626108695460980073 2549346469581521595735055)
            ·
              refine ⟨3824019704372282393602583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2549346469581521595735055 3824019704372282393602583)
              ·
                refine ⟨5736029556558423590403875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3824019704372282393602583 5736029556558423590403875)
                ·
                  refine ⟨8604044334837635385605813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5736029556558423590403875 8604044334837635385605813)
                  ·
                    refine ⟨806629156391028317400545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8604044334837635385605813 806629156391028317400545)
                    ·
                      rfl

theorem cell22_2356357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_2356357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356357 prefixEnd_2356357 := by exact prefixLift 2356357
  have htrace : WordTrace (prefixWord ++ tailWord_2356357) baseStart_2356357 baseEnd_2356357 := by
    simpa [prefixWord, tailWord_2356357, baseEnd_2356357] using wordTrace_append hprefix tailTrace_2356357
  have hstable : (prefixWord ++ tailWord_2356357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356357).length < 2 ^ (prefixWord ++ tailWord_2356357).sum := by decide
  have hdescent : baseEnd_2356357 < baseStart_2356357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356370 : List Nat := [3, 2, 3, 1, 1, 3, 1, 8]
def baseStart_2356370 : Nat := 118140960795 + 2356370 * 2 ^ 59
def prefixEnd_2356370 : Nat := 4983230072969 + 3 ^ 40 * 2356370 * 2
def baseEnd_2356370 : Nat := 89625956284077846313945

theorem tailTrace_2356370 : CollatzResearch.WordTrace tailWord_2356370 prefixEnd_2356370 89625956284077846313945 := by
  unfold tailWord_2356370
  simp only [CollatzResearch.WordTrace]
  refine ⟨21485968618320350200386641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57295916315520933867697709 21485968618320350200386641)
  ·
    refine ⟨16114476463740262650289981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21485968618320350200386641 16114476463740262650289981)
    ·
      refine ⟨6042928673902598493858743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16114476463740262650289981 6042928673902598493858743)
      ·
        refine ⟨9064393010853897740788115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6042928673902598493858743 9064393010853897740788115)
        ·
          refine ⟨13596589516280846611182173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9064393010853897740788115 13596589516280846611182173)
          ·
            refine ⟨5098721068605317479193315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13596589516280846611182173 5098721068605317479193315)
            ·
              refine ⟨7648081602907976218789973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5098721068605317479193315 7648081602907976218789973)
              ·
                refine ⟨89625956284077846313945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7648081602907976218789973 89625956284077846313945)
                ·
                  rfl

theorem cell22_2356370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_2356370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356370 prefixEnd_2356370 := by exact prefixLift 2356370
  have htrace : WordTrace (prefixWord ++ tailWord_2356370) baseStart_2356370 baseEnd_2356370 := by
    simpa [prefixWord, tailWord_2356370, baseEnd_2356370] using wordTrace_append hprefix tailTrace_2356370
  have hstable : (prefixWord ++ tailWord_2356370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356370).length < 2 ^ (prefixWord ++ tailWord_2356370).sum := by decide
  have hdescent : baseEnd_2356370 < baseStart_2356370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356402 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_2356402 : Nat := 118140960795 + 2356402 * 2 ^ 59
def prefixEnd_2356402 : Nat := 4983230072969 + 3 ^ 40 * 2356402 * 2
def baseEnd_2356402 : Nat := 806644560810663200025407

theorem tailTrace_2356402 : CollatzResearch.WordTrace tailWord_2356402 prefixEnd_2356402 806644560810663200025407 := by
  unfold tailWord_2356402
  simp only [CollatzResearch.WordTrace]
  refine ⟨21486260402291367566677865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57296694406110313511140973 21486260402291367566677865)
  ·
    refine ⟨16114695301718525675008399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21486260402291367566677865 16114695301718525675008399)
    ·
      refine ⟨24172042952577788512512599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16114695301718525675008399 24172042952577788512512599)
      ·
        refine ⟨36258064428866682768768899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24172042952577788512512599 36258064428866682768768899)
        ·
          refine ⟨54387096643300024153153349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36258064428866682768768899 54387096643300024153153349)
          ·
            refine ⟨10197580620618754528716253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54387096643300024153153349 10197580620618754528716253)
            ·
              refine ⟨3824092732732032948268595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10197580620618754528716253 3824092732732032948268595)
              ·
                refine ⟨5736139099098049422402893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3824092732732032948268595 5736139099098049422402893)
                ·
                  refine ⟨2151052162161768533401085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5736139099098049422402893 2151052162161768533401085)
                  ·
                    refine ⟨806644560810663200025407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2151052162161768533401085 806644560810663200025407)
                    ·
                      rfl

theorem cell22_2356402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_2356402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356402 prefixEnd_2356402 := by exact prefixLift 2356402
  have htrace : WordTrace (prefixWord ++ tailWord_2356402) baseStart_2356402 baseEnd_2356402 := by
    simpa [prefixWord, tailWord_2356402, baseEnd_2356402] using wordTrace_append hprefix tailTrace_2356402
  have hstable : (prefixWord ++ tailWord_2356402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356402).length < 2 ^ (prefixWord ++ tailWord_2356402).sum := by decide
  have hdescent : baseEnd_2356402 < baseStart_2356402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356453 : List Nat := [1, 3, 1, 4, 3, 2, 2, 2, 1, 3]
def baseStart_2356453 : Nat := 118140960795 + 2356453 * 2 ^ 59
def prefixEnd_2356453 : Nat := 4983230072969 + 3 ^ 40 * 2356453 * 2
def baseEnd_2356453 : Nat := 806662019152916067000251

theorem tailTrace_2356453 : CollatzResearch.WordTrace tailWord_2356453 prefixEnd_2356453 806662019152916067000251 := by
  unfold tailWord_2356453
  simp only [CollatzResearch.WordTrace]
  refine ⟨85946901731980705976818013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57297934487987137317878675 85946901731980705976818013)
  ·
    refine ⟨32230088149492764741306755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85946901731980705976818013 32230088149492764741306755)
    ·
      refine ⟨48345132224239147111960133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32230088149492764741306755 48345132224239147111960133)
      ·
        refine ⟨9064712292044840083492525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48345132224239147111960133 9064712292044840083492525)
        ·
          refine ⟨3399267109516815031309697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9064712292044840083492525 3399267109516815031309697)
          ·
            refine ⟨2549450332137611273482273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3399267109516815031309697 2549450332137611273482273)
            ·
              refine ⟨1912087749103208455111705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2549450332137611273482273 1912087749103208455111705)
              ·
                refine ⟨1434065811827406341333779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1912087749103208455111705 1434065811827406341333779)
                ·
                  refine ⟨2151098717741109512000669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434065811827406341333779 2151098717741109512000669)
                  ·
                    refine ⟨806662019152916067000251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2151098717741109512000669 806662019152916067000251)
                    ·
                      rfl

theorem cell22_2356453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_2356453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356453 prefixEnd_2356453 := by exact prefixLift 2356453
  have htrace : WordTrace (prefixWord ++ tailWord_2356453) baseStart_2356453 baseEnd_2356453 := by
    simpa [prefixWord, tailWord_2356453, baseEnd_2356453] using wordTrace_append hprefix tailTrace_2356453
  have hstable : (prefixWord ++ tailWord_2356453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356453).length < 2 ^ (prefixWord ++ tailWord_2356453).sum := by decide
  have hdescent : baseEnd_2356453 < baseStart_2356453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356494 : List Nat := [4, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_2356494 : Nat := 118140960795 + 2356494 * 2 ^ 59
def prefixEnd_2356494 : Nat := 4983230072969 + 3 ^ 40 * 2356494 * 2
def baseEnd_2356494 : Nat := 268892018096935208908375

theorem tailTrace_2356494 : CollatzResearch.WordTrace tailWord_2356494 prefixEnd_2356494 268892018096935208908375 := by
  unfold tailWord_2356494
  simp only [CollatzResearch.WordTrace]
  refine ⟨10743549640604021247382567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57298931416554779986040357 10743549640604021247382567)
  ·
    refine ⟨16115324460906031871073851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10743549640604021247382567 16115324460906031871073851)
    ·
      refine ⟨24172986691359047806610777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16115324460906031871073851 24172986691359047806610777)
      ·
        refine ⟨18129740018519285854958083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24172986691359047806610777 18129740018519285854958083)
        ·
          refine ⟨27194610027778928782437125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18129740018519285854958083 27194610027778928782437125)
          ·
            refine ⟨5098989380208549146706961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27194610027778928782437125 5098989380208549146706961)
            ·
              refine ⟨3824242035156411860030221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5098989380208549146706961 3824242035156411860030221)
              ·
                refine ⟨1434090763183654447511333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3824242035156411860030221 1434090763183654447511333)
                ·
                  refine ⟨268892018096935208908375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1434090763183654447511333 268892018096935208908375)
                  ·
                    rfl

theorem cell22_2356494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_2356494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356494 prefixEnd_2356494 := by exact prefixLift 2356494
  have htrace : WordTrace (prefixWord ++ tailWord_2356494) baseStart_2356494 baseEnd_2356494 := by
    simpa [prefixWord, tailWord_2356494, baseEnd_2356494] using wordTrace_append hprefix tailTrace_2356494
  have hstable : (prefixWord ++ tailWord_2356494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356494).length < 2 ^ (prefixWord ++ tailWord_2356494).sum := by decide
  have hdescent : baseEnd_2356494 < baseStart_2356494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356509 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_2356509 : Nat := 118140960795 + 2356509 * 2 ^ 59
def prefixEnd_2356509 : Nat := 4983230072969 + 3 ^ 40 * 2356509 * 2
def baseEnd_2356509 : Nat := 806681189097350587600079

theorem tailTrace_2356509 : CollatzResearch.WordTrace tailWord_2356509 prefixEnd_2356509 806681189097350587600079 := by
  unfold tailWord_2356509
  simp only [CollatzResearch.WordTrace]
  refine ⟨85948944219777827540856581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57299296146518551693904387 85948944219777827540856581)
  ·
    refine ⟨16115427041208342663910609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85948944219777827540856581 16115427041208342663910609)
    ·
      refine ⟨12086570280906256997932957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16115427041208342663910609 12086570280906256997932957)
      ·
        refine ⟨4532463855339846374224859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12086570280906256997932957 4532463855339846374224859)
        ·
          refine ⟨6798695783009769561337289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4532463855339846374224859 6798695783009769561337289)
          ·
            refine ⟨5099021837257327171002967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6798695783009769561337289 5099021837257327171002967)
            ·
              refine ⟨7648532755885990756504451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5099021837257327171002967 7648532755885990756504451)
              ·
                refine ⟨11472799133828986134756677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7648532755885990756504451 11472799133828986134756677)
                ·
                  refine ⟨2151149837592934900266877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11472799133828986134756677 2151149837592934900266877)
                  ·
                    refine ⟨806681189097350587600079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2151149837592934900266877 806681189097350587600079)
                    ·
                      rfl

theorem cell22_2356509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_2356509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356509 prefixEnd_2356509 := by exact prefixLift 2356509
  have htrace : WordTrace (prefixWord ++ tailWord_2356509) baseStart_2356509 baseEnd_2356509 := by
    simpa [prefixWord, tailWord_2356509, baseEnd_2356509] using wordTrace_append hprefix tailTrace_2356509
  have hstable : (prefixWord ++ tailWord_2356509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356509).length < 2 ^ (prefixWord ++ tailWord_2356509).sum := by decide
  have hdescent : baseEnd_2356509 < baseStart_2356509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356584 : List Nat := [2, 1, 4, 2, 3, 1, 1, 3, 5]
def baseStart_2356584 : Nat := 118140960795 + 2356584 * 2 ^ 59
def prefixEnd_2356584 : Nat := 4983230072969 + 3 ^ 40 * 2356584 * 2
def baseEnd_2356584 : Nat := 268902287710025130658283

theorem tailTrace_2356584 : CollatzResearch.WordTrace tailWord_2356584 prefixEnd_2356584 268902287710025130658283 := by
  unfold tailWord_2356584
  simp only [CollatzResearch.WordTrace]
  refine ⟨42975839847253057674918403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57301119796337410233224537 42975839847253057674918403)
  ·
    refine ⟨64463759770879586512377605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42975839847253057674918403 64463759770879586512377605)
    ·
      refine ⟨12086954957039922471070801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64463759770879586512377605 12086954957039922471070801)
      ·
        refine ⟨9065216217779941853303101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12086954957039922471070801 9065216217779941853303101)
        ·
          refine ⟨3399456081667478194988663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9065216217779941853303101 3399456081667478194988663)
          ·
            refine ⟨5099184122501217292482995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3399456081667478194988663 5099184122501217292482995)
            ·
              refine ⟨7648776183751825938724493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5099184122501217292482995 7648776183751825938724493)
              ·
                refine ⟨2868291068906934727021685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7648776183751825938724493 2868291068906934727021685)
                ·
                  refine ⟨268902287710025130658283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2868291068906934727021685 268902287710025130658283)
                  ·
                    rfl

theorem cell22_2356584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_2356584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356584 prefixEnd_2356584 := by exact prefixLift 2356584
  have htrace : WordTrace (prefixWord ++ tailWord_2356584) baseStart_2356584 baseEnd_2356584 := by
    simpa [prefixWord, tailWord_2356584, baseEnd_2356584] using wordTrace_append hprefix tailTrace_2356584
  have hstable : (prefixWord ++ tailWord_2356584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356584).length < 2 ^ (prefixWord ++ tailWord_2356584).sum := by decide
  have hdescent : baseEnd_2356584 < baseStart_2356584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356622 : List Nat := [4, 1, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_2356622 : Nat := 118140960795 + 2356622 * 2 ^ 59
def prefixEnd_2356622 : Nat := 4983230072969 + 3 ^ 40 * 2356622 * 2
def baseEnd_2356622 : Nat := 806719871306655959524733

theorem tailTrace_2356622 : CollatzResearch.WordTrace tailWord_2356622 prefixEnd_2356622 806719871306655959524733 := by
  unfold tailWord_2356622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10744133208546055979965015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57302043778912298559813413 10744133208546055979965015)
  ·
    refine ⟨16116199812819083969947523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10744133208546055979965015 16116199812819083969947523)
    ·
      refine ⟨24174299719228625954921285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16116199812819083969947523 24174299719228625954921285)
      ·
        refine ⟨4532681197355367366547741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24174299719228625954921285 4532681197355367366547741)
        ·
          refine ⟨1699755449008262762455403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4532681197355367366547741 1699755449008262762455403)
          ·
            refine ⟨2549633173512394143683105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699755449008262762455403 2549633173512394143683105)
            ·
              refine ⟨1912224880134295607762329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2549633173512394143683105 1912224880134295607762329)
              ·
                refine ⟨1434168660100721705821747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1912224880134295607762329 1434168660100721705821747)
                ·
                  refine ⟨2151252990151082558732621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434168660100721705821747 2151252990151082558732621)
                  ·
                    refine ⟨806719871306655959524733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2151252990151082558732621 806719871306655959524733)
                    ·
                      rfl

theorem cell22_2356622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_2356622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356622 prefixEnd_2356622 := by exact prefixLift 2356622
  have htrace : WordTrace (prefixWord ++ tailWord_2356622) baseStart_2356622 baseEnd_2356622 := by
    simpa [prefixWord, tailWord_2356622, baseEnd_2356622] using wordTrace_append hprefix tailTrace_2356622
  have hstable : (prefixWord ++ tailWord_2356622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356622).length < 2 ^ (prefixWord ++ tailWord_2356622).sum := by decide
  have hdescent : baseEnd_2356622 < baseStart_2356622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356740 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_2356740 : Nat := 118140960795 + 2356740 * 2 ^ 59
def prefixEnd_2356740 : Nat := 4983230072969 + 3 ^ 40 * 2356740 * 2
def baseEnd_2356740 : Nat := 806760265118142985074371

theorem tailTrace_2356740 : CollatzResearch.WordTrace tailWord_2356740 prefixEnd_2356740 806760265118142985074371 := by
  unfold tailWord_2356740
  simp only [CollatzResearch.WordTrace]
  refine ⟨42978684740970476996257837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57304912987960635995010449 42978684740970476996257837)
  ·
    refine ⟨16117006777863928873596689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42978684740970476996257837 16117006777863928873596689)
    ·
      refine ⟨12087755083397946655197517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16117006777863928873596689 12087755083397946655197517)
      ·
        refine ⟨4532908156274229995699069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12087755083397946655197517 4532908156274229995699069)
        ·
          refine ⟨1699840558602836248387151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4532908156274229995699069 1699840558602836248387151)
          ·
            refine ⟨2549760837904254372580727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699840558602836248387151 2549760837904254372580727)
            ·
              refine ⟨3824641256856381558871091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2549760837904254372580727 3824641256856381558871091)
              ·
                refine ⟨5736961885284572338306637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3824641256856381558871091 5736961885284572338306637)
                ·
                  refine ⟨2151360706981714626864989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5736961885284572338306637 2151360706981714626864989)
                  ·
                    refine ⟨806760265118142985074371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2151360706981714626864989 806760265118142985074371)
                    ·
                      rfl

theorem cell22_2356740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_2356740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356740 prefixEnd_2356740 := by exact prefixLift 2356740
  have htrace : WordTrace (prefixWord ++ tailWord_2356740) baseStart_2356740 baseEnd_2356740 := by
    simpa [prefixWord, tailWord_2356740, baseEnd_2356740] using wordTrace_append hprefix tailTrace_2356740
  have hstable : (prefixWord ++ tailWord_2356740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356740).length < 2 ^ (prefixWord ++ tailWord_2356740).sum := by decide
  have hdescent : baseEnd_2356740 < baseStart_2356740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356792 : List Nat := [2, 1, 2, 1, 4, 12]
def baseStart_2356792 : Nat := 118140960795 + 2356792 * 2 ^ 59
def prefixEnd_2356792 : Nat := 4983230072969 + 3 ^ 40 * 2356792 * 2
def baseEnd_2356792 : Nat := 9960223034331261515731

theorem tailTrace_2356792 : CollatzResearch.WordTrace tailWord_2356792 prefixEnd_2356792 9960223034331261515731 := by
  unfold tailWord_2356792
  simp only [CollatzResearch.WordTrace]
  refine ⟨42979633038876283436704315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57306177385168377915605753 42979633038876283436704315)
  ·
    refine ⟨64469449558314425155056473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42979633038876283436704315 64469449558314425155056473)
    ·
      refine ⟨48352087168735818866292355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64469449558314425155056473 48352087168735818866292355)
      ·
        refine ⟨72528130753103728299438533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48352087168735818866292355 72528130753103728299438533)
        ·
          refine ⟨13599024516206949056144725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72528130753103728299438533 13599024516206949056144725)
          ·
            refine ⟨9960223034331261515731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13599024516206949056144725 9960223034331261515731)
            ·
              rfl

theorem cell22_2356792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 12].length) (baseStart_2356792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356792 prefixEnd_2356792 := by exact prefixLift 2356792
  have htrace : WordTrace (prefixWord ++ tailWord_2356792) baseStart_2356792 baseEnd_2356792 := by
    simpa [prefixWord, tailWord_2356792, baseEnd_2356792] using wordTrace_append hprefix tailTrace_2356792
  have hstable : (prefixWord ++ tailWord_2356792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356792).length < 2 ^ (prefixWord ++ tailWord_2356792).sum := by decide
  have hdescent : baseEnd_2356792 < baseStart_2356792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356794 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_2356794 : Nat := 118140960795 + 2356794 * 2 ^ 59
def prefixEnd_2356794 : Nat := 4983230072969 + 3 ^ 40 * 2356794 * 2
def baseEnd_2356794 : Nat := 806778750421704844224205

theorem tailTrace_2356794 : CollatzResearch.WordTrace tailWord_2356794 prefixEnd_2356794 806778750421704844224205 := by
  unfold tailWord_2356794
  simp only [CollatzResearch.WordTrace]
  refine ⟨21489834755936330303745359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57306226015830214143320957 21489834755936330303745359)
  ·
    refine ⟨32234752133904495455618039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21489834755936330303745359 32234752133904495455618039)
    ·
      refine ⟨48352128200856743183427059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32234752133904495455618039 48352128200856743183427059)
      ·
        refine ⟨72528192301285114775140589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48352128200856743183427059 72528192301285114775140589)
        ·
          refine ⟨27198072112981918040677721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72528192301285114775140589 27198072112981918040677721)
          ·
            refine ⟨20398554084736438530508291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27198072112981918040677721 20398554084736438530508291)
            ·
              refine ⟨30597831127104657795762437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20398554084736438530508291 30597831127104657795762437)
              ·
                refine ⟨5737093336332123336705457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30597831127104657795762437 5737093336332123336705457)
                ·
                  refine ⟨4302820002249092502529093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5737093336332123336705457 4302820002249092502529093)
                  ·
                    refine ⟨806778750421704844224205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4302820002249092502529093 806778750421704844224205)
                    ·
                      rfl

theorem cell22_2356794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_2356794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356794 prefixEnd_2356794 := by exact prefixLift 2356794
  have htrace : WordTrace (prefixWord ++ tailWord_2356794) baseStart_2356794 baseEnd_2356794 := by
    simpa [prefixWord, tailWord_2356794, baseEnd_2356794] using wordTrace_append hprefix tailTrace_2356794
  have hstable : (prefixWord ++ tailWord_2356794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356794).length < 2 ^ (prefixWord ++ tailWord_2356794).sum := by decide
  have hdescent : baseEnd_2356794 < baseStart_2356794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356813 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2356813 : Nat := 118140960795 + 2356813 * 2 ^ 59
def prefixEnd_2356813 : Nat := 4983230072969 + 3 ^ 40 * 2356813 * 2
def baseEnd_2356813 : Nat := 806785254509995127999147

theorem tailTrace_2356813 : CollatzResearch.WordTrace tailWord_2356813 prefixEnd_2356813 806785254509995127999147 := by
  unfold tailWord_2356813
  simp only [CollatzResearch.WordTrace]
  refine ⟨85960032010676487459923093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57306688007117658306615395 85960032010676487459923093)
  ·
    refine ⟨4029376500500460349683895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85960032010676487459923093 4029376500500460349683895)
    ·
      refine ⟨6044064750750690524525843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4029376500500460349683895 6044064750750690524525843)
      ·
        refine ⟨9066097126126035786788765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6044064750750690524525843 9066097126126035786788765)
        ·
          refine ⟨3399786422297263420045787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9066097126126035786788765 3399786422297263420045787)
          ·
            refine ⟨5099679633445895130068681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3399786422297263420045787 5099679633445895130068681)
            ·
              refine ⟨3824759725084421347551511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5099679633445895130068681 3824759725084421347551511)
              ·
                refine ⟨5737139587626632021327267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3824759725084421347551511 5737139587626632021327267)
                ·
                  refine ⟨8605709381439948031990901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5737139587626632021327267 8605709381439948031990901)
                  ·
                    refine ⟨806785254509995127999147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8605709381439948031990901 806785254509995127999147)
                    ·
                      rfl

theorem cell22_2356813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2356813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356813 prefixEnd_2356813 := by exact prefixLift 2356813
  have htrace : WordTrace (prefixWord ++ tailWord_2356813) baseStart_2356813 baseEnd_2356813 := by
    simpa [prefixWord, tailWord_2356813, baseEnd_2356813] using wordTrace_append hprefix tailTrace_2356813
  have hstable : (prefixWord ++ tailWord_2356813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356813).length < 2 ^ (prefixWord ++ tailWord_2356813).sum := by decide
  have hdescent : baseEnd_2356813 < baseStart_2356813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356828 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2356828 : Nat := 118140960795 + 2356828 * 2 ^ 59
def prefixEnd_2356828 : Nat := 4983230072969 + 3 ^ 40 * 2356828 * 2
def baseEnd_2356828 : Nat := 806790389316540088874101

theorem tailTrace_2356828 : CollatzResearch.WordTrace tailWord_2356828 prefixEnd_2356828 806790389316540088874101 := by
  unfold tailWord_2356828
  simp only [CollatzResearch.WordTrace]
  refine ⟨42980289552811072510859569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57307052737081430014479425 42980289552811072510859569)
  ·
    refine ⟨32235217164608304383144677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42980289552811072510859569 32235217164608304383144677)
    ·
      refine ⟨6044103218364057071839627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32235217164608304383144677 6044103218364057071839627)
      ·
        refine ⟨9066154827546085607759441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6044103218364057071839627 9066154827546085607759441)
        ·
          refine ⟨6799616120659564205819581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9066154827546085607759441 6799616120659564205819581)
          ·
            refine ⟨2549856045247336577182343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6799616120659564205819581 2549856045247336577182343)
            ·
              refine ⟨3824784067871004865773515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2549856045247336577182343 3824784067871004865773515)
              ·
                refine ⟨5737176101806507298660273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3824784067871004865773515 5737176101806507298660273)
                ·
                  refine ⟨4302882076354880473995205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5737176101806507298660273 4302882076354880473995205)
                  ·
                    refine ⟨806790389316540088874101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4302882076354880473995205 806790389316540088874101)
                    ·
                      rfl

theorem cell22_2356828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2356828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356828 prefixEnd_2356828 := by exact prefixLift 2356828
  have htrace : WordTrace (prefixWord ++ tailWord_2356828) baseStart_2356828 baseEnd_2356828 := by
    simpa [prefixWord, tailWord_2356828, baseEnd_2356828] using wordTrace_append hprefix tailTrace_2356828
  have hstable : (prefixWord ++ tailWord_2356828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356828).length < 2 ^ (prefixWord ++ tailWord_2356828).sum := by decide
  have hdescent : baseEnd_2356828 < baseStart_2356828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356869 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_2356869 : Nat := 118140960795 + 2356869 * 2 ^ 59
def prefixEnd_2356869 : Nat := 4983230072969 + 3 ^ 40 * 2356869 * 2
def baseEnd_2356869 : Nat := 806804424454429648598975

theorem tailTrace_2356869 : CollatzResearch.WordTrace tailWord_2356869 prefixEnd_2356869 806804424454429648598975 := by
  unfold tailWord_2356869
  simp only [CollatzResearch.WordTrace]
  refine ⟨85962074498473609023961661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57308049665649072682641107 85962074498473609023961661)
  ·
    refine ⟨32235777936927603383985623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85962074498473609023961661 32235777936927603383985623)
    ·
      refine ⟨48353666905391405075978435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32235777936927603383985623 48353666905391405075978435)
      ·
        refine ⟨72530500358087107613967653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48353666905391405075978435 72530500358087107613967653)
        ·
          refine ⟨13599468817141332677618935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72530500358087107613967653 13599468817141332677618935)
          ·
            refine ⟨20399203225711999016428403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13599468817141332677618935 20399203225711999016428403)
            ·
              refine ⟨30598804838567998524642605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20399203225711999016428403 30598804838567998524642605)
              ·
                refine ⟨11474551814462999446740977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30598804838567998524642605 11474551814462999446740977)
                ·
                  refine ⟨8605913860847249585055733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11474551814462999446740977 8605913860847249585055733)
                  ·
                    refine ⟨806804424454429648598975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8605913860847249585055733 806804424454429648598975)
                    ·
                      rfl

theorem cell22_2356869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_2356869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356869 prefixEnd_2356869 := by exact prefixLift 2356869
  have htrace : WordTrace (prefixWord ++ tailWord_2356869) baseStart_2356869 baseEnd_2356869 := by
    simpa [prefixWord, tailWord_2356869, baseEnd_2356869] using wordTrace_append hprefix tailTrace_2356869
  have hstable : (prefixWord ++ tailWord_2356869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356869).length < 2 ^ (prefixWord ++ tailWord_2356869).sum := by decide
  have hdescent : baseEnd_2356869 < baseStart_2356869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356892 : List Nat := [2, 2, 3, 2, 3, 2, 1, 3, 1, 3]
def baseStart_2356892 : Nat := 118140960795 + 2356892 * 2 ^ 59
def prefixEnd_2356892 : Nat := 4983230072969 + 3 ^ 40 * 2356892 * 2
def baseEnd_2356892 : Nat := 806812297824465255273905

theorem tailTrace_2356892 : CollatzResearch.WordTrace tailWord_2356892 prefixEnd_2356892 806812297824465255273905 := by
  unfold tailWord_2356892
  simp only [CollatzResearch.WordTrace]
  refine ⟨42981456688695141976024465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57308608918260189301365953 42981456688695141976024465)
  ·
    refine ⟨32236092516521356482018349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42981456688695141976024465 32236092516521356482018349)
    ·
      refine ⟨12088534693695508680756881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32236092516521356482018349 12088534693695508680756881)
      ·
        refine ⟨9066401020271631510567661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12088534693695508680756881 9066401020271631510567661)
        ·
          refine ⟨3399900382601861816462873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9066401020271631510567661 3399900382601861816462873)
          ·
            refine ⟨2549925286951396362347155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3399900382601861816462873 2549925286951396362347155)
            ·
              refine ⟨3824887930427094543520733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2549925286951396362347155 3824887930427094543520733)
              ·
                refine ⟨1434332973910160453820275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3824887930427094543520733 1434332973910160453820275)
                ·
                  refine ⟨2151499460865240680730413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434332973910160453820275 2151499460865240680730413)
                  ·
                    refine ⟨806812297824465255273905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2151499460865240680730413 806812297824465255273905)
                    ·
                      rfl

theorem cell22_2356892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_2356892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356892 prefixEnd_2356892 := by exact prefixLift 2356892
  have htrace : WordTrace (prefixWord ++ tailWord_2356892) baseStart_2356892 baseEnd_2356892 := by
    simpa [prefixWord, tailWord_2356892, baseEnd_2356892] using wordTrace_append hprefix tailTrace_2356892
  have hstable : (prefixWord ++ tailWord_2356892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356892).length < 2 ^ (prefixWord ++ tailWord_2356892).sum := by decide
  have hdescent : baseEnd_2356892 < baseStart_2356892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356901 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_2356901 : Nat := 118140960795 + 2356901 * 2 ^ 59
def prefixEnd_2356901 : Nat := 4983230072969 + 3 ^ 40 * 2356901 * 2
def baseEnd_2356901 : Nat := 806815378708392231798877

theorem tailTrace_2356901 : CollatzResearch.WordTrace tailWord_2356901 prefixEnd_2356901 806815378708392231798877 := by
  unfold tailWord_2356901
  simp only [CollatzResearch.WordTrace]
  refine ⟨85963241634357678489126557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57308827756238452326084371 85963241634357678489126557)
  ·
    refine ⟨32236215612884129433422459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85963241634357678489126557 32236215612884129433422459)
    ·
      refine ⟨48354323419326194150133689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32236215612884129433422459 48354323419326194150133689)
      ·
        refine ⟨36265742564494645612600267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48354323419326194150133689 36265742564494645612600267)
        ·
          refine ⟨54398613846741968418900401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36265742564494645612600267 54398613846741968418900401)
          ·
            refine ⟨40798960385056476314175301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54398613846741968418900401 40798960385056476314175301)
            ·
              refine ⟨7649805072198089308907869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40798960385056476314175301 7649805072198089308907869)
              ·
                refine ⟨2868676902074283490840451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7649805072198089308907869 2868676902074283490840451)
                ·
                  refine ⟨4303015353111425236260677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868676902074283490840451 4303015353111425236260677)
                  ·
                    refine ⟨806815378708392231798877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4303015353111425236260677 806815378708392231798877)
                    ·
                      rfl

theorem cell22_2356901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_2356901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356901 prefixEnd_2356901 := by exact prefixLift 2356901
  have htrace : WordTrace (prefixWord ++ tailWord_2356901) baseStart_2356901 baseEnd_2356901 := by
    simpa [prefixWord, tailWord_2356901, baseEnd_2356901] using wordTrace_append hprefix tailTrace_2356901
  have hstable : (prefixWord ++ tailWord_2356901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356901).length < 2 ^ (prefixWord ++ tailWord_2356901).sum := by decide
  have hdescent : baseEnd_2356901 < baseStart_2356901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356948 : List Nat := [2, 4, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2356948 : Nat := 118140960795 + 2356948 * 2 ^ 59
def prefixEnd_2356948 : Nat := 4983230072969 + 3 ^ 40 * 2356948 * 2
def baseEnd_2356948 : Nat := 806831467768899775873733

theorem tailTrace_2356948 : CollatzResearch.WordTrace tailWord_2356948 prefixEnd_2356948 806831467768899775873733 := by
  unfold tailWord_2356948
  simp only [CollatzResearch.WordTrace]
  refine ⟨42982477932593702758043749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57309970576791603677391665 42982477932593702758043749)
  ·
    refine ⟨8059214612361319267133203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42982477932593702758043749 8059214612361319267133203)
    ·
      refine ⟨12088821918541978900699805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8059214612361319267133203 12088821918541978900699805)
      ·
        refine ⟨4533308219453242087762427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12088821918541978900699805 4533308219453242087762427)
        ·
          refine ⟨6799962329179863131643641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4533308219453242087762427 6799962329179863131643641)
          ·
            refine ⟨5099971746884897348732731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6799962329179863131643641 5099971746884897348732731)
            ·
              refine ⟨7649957620327346023099097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5099971746884897348732731 7649957620327346023099097)
              ·
                refine ⟨5737468215245509517324323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7649957620327346023099097 5737468215245509517324323)
                ·
                  refine ⟨8606202322868264275986485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5737468215245509517324323 8606202322868264275986485)
                  ·
                    refine ⟨806831467768899775873733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8606202322868264275986485 806831467768899775873733)
                    ·
                      rfl

theorem cell22_2356948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2356948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356948 prefixEnd_2356948 := by exact prefixLift 2356948
  have htrace : WordTrace (prefixWord ++ tailWord_2356948) baseStart_2356948 baseEnd_2356948 := by
    simpa [prefixWord, tailWord_2356948, baseEnd_2356948] using wordTrace_append hprefix tailTrace_2356948
  have hstable : (prefixWord ++ tailWord_2356948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356948).length < 2 ^ (prefixWord ++ tailWord_2356948).sum := by decide
  have hdescent : baseEnd_2356948 < baseStart_2356948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2356961 : List Nat := [1, 2, 3, 1, 6, 9]
def baseStart_2356961 : Nat := 118140960795 + 2356961 * 2 ^ 59
def prefixEnd_2356961 : Nat := 4983230072969 + 3 ^ 40 * 2356961 * 2
def baseEnd_2356961 : Nat := 9960937258451507102453

theorem tailTrace_2356961 : CollatzResearch.WordTrace tailWord_2356961 prefixEnd_2356961 9960937258451507102453 := by
  unfold tailWord_2356961
  simp only [CollatzResearch.WordTrace]
  refine ⟨85965430014140308736310737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57310286676093539157540491 85965430014140308736310737)
  ·
    refine ⟨64474072510605231552233053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85965430014140308736310737 64474072510605231552233053)
    ·
      refine ⟨24177777191476961832087395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64474072510605231552233053 24177777191476961832087395)
      ·
        refine ⟨36266665787215442748131093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24177777191476961832087395 36266665787215442748131093)
        ·
          refine ⟨1699999958775723878818645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36266665787215442748131093 1699999958775723878818645)
          ·
            refine ⟨9960937258451507102453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1699999958775723878818645 9960937258451507102453)
            ·
              rfl

theorem cell22_2356961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 9].length) (baseStart_2356961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2356961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2356961 prefixEnd_2356961 := by exact prefixLift 2356961
  have htrace : WordTrace (prefixWord ++ tailWord_2356961) baseStart_2356961 baseEnd_2356961 := by
    simpa [prefixWord, tailWord_2356961, baseEnd_2356961] using wordTrace_append hprefix tailTrace_2356961
  have hstable : (prefixWord ++ tailWord_2356961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2356961).length < 2 ^ (prefixWord ++ tailWord_2356961).sum := by decide
  have hdescent : baseEnd_2356961 < baseStart_2356961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2356961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357066 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_2357066 : Nat := 118140960795 + 2357066 * 2 ^ 59
def prefixEnd_2357066 : Nat := 4983230072969 + 3 ^ 40 * 2357066 * 2
def baseEnd_2357066 : Nat := 806871861580386801423371

theorem tailTrace_2357066 : CollatzResearch.WordTrace tailWord_2357066 prefixEnd_2357066 806871861580386801423371 := by
  unfold tailWord_2357066
  simp only [CollatzResearch.WordTrace]
  refine ⟨21492314919689977917220763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57312839785839941112588701 21492314919689977917220763)
  ·
    refine ⟨32238472379534966875831145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21492314919689977917220763 32238472379534966875831145)
    ·
      refine ⟨24178854284651225156873359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32238472379534966875831145 24178854284651225156873359)
      ·
        refine ⟨36268281426976837735310039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24178854284651225156873359 36268281426976837735310039)
        ·
          refine ⟨54402422140465256602965059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36268281426976837735310039 54402422140465256602965059)
          ·
            refine ⟨81603633210697884904447589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54402422140465256602965059 81603633210697884904447589)
            ·
              refine ⟨15300681227005853419583923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81603633210697884904447589 15300681227005853419583923)
              ·
                refine ⟨22951021840508780129375885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15300681227005853419583923 22951021840508780129375885)
                ·
                  refine ⟨8606633190190792548515957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22951021840508780129375885 8606633190190792548515957)
                  ·
                    refine ⟨806871861580386801423371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8606633190190792548515957 806871861580386801423371)
                    ·
                      rfl

theorem cell22_2357066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_2357066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357066 prefixEnd_2357066 := by exact prefixLift 2357066
  have htrace : WordTrace (prefixWord ++ tailWord_2357066) baseStart_2357066 baseEnd_2357066 := by
    simpa [prefixWord, tailWord_2357066, baseEnd_2357066] using wordTrace_append hprefix tailTrace_2357066
  have hstable : (prefixWord ++ tailWord_2357066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357066).length < 2 ^ (prefixWord ++ tailWord_2357066).sum := by decide
  have hdescent : baseEnd_2357066 < baseStart_2357066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357100 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 2, 3]
def baseStart_2357100 : Nat := 118140960795 + 2357100 * 2 ^ 59
def prefixEnd_2357100 : Nat := 4983230072969 + 3 ^ 40 * 2357100 * 2
def baseEnd_2357100 : Nat := 806883500475222046073267

theorem tailTrace_2357100 : CollatzResearch.WordTrace tailWord_2357100 prefixEnd_2357100 806883500475222046073267 := by
  unfold tailWord_2357100
  simp only [CollatzResearch.WordTrace]
  refine ⟨42985249880318367737810377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57313666507091156983747169 42985249880318367737810377)
  ·
    refine ⟨32238937410238775803357783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42985249880318367737810377 32238937410238775803357783)
    ·
      refine ⟨48358406115358163705036675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32238937410238775803357783 48358406115358163705036675)
      ·
        refine ⟨72537609173037245557555013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48358406115358163705036675 72537609173037245557555013)
        ·
          refine ⟨13600801719944483542041565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72537609173037245557555013 13600801719944483542041565)
          ·
            refine ⟨5100300644979181328265587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13600801719944483542041565 5100300644979181328265587)
            ·
              refine ⟨7650450967468771992398381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5100300644979181328265587 7650450967468771992398381)
              ·
                refine ⟨2868919112800789497149393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7650450967468771992398381 2868919112800789497149393)
                ·
                  refine ⟨2151689334600592122862045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2868919112800789497149393 2151689334600592122862045)
                  ·
                    refine ⟨806883500475222046073267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2151689334600592122862045 806883500475222046073267)
                    ·
                      rfl

theorem cell22_2357100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_2357100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357100 prefixEnd_2357100 := by exact prefixLift 2357100
  have htrace : WordTrace (prefixWord ++ tailWord_2357100) baseStart_2357100 baseEnd_2357100 := by
    simpa [prefixWord, tailWord_2357100, baseEnd_2357100] using wordTrace_append hprefix tailTrace_2357100
  have hstable : (prefixWord ++ tailWord_2357100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357100).length < 2 ^ (prefixWord ++ tailWord_2357100).sum := by decide
  have hdescent : baseEnd_2357100 < baseStart_2357100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357134 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_2357134 : Nat := 118140960795 + 2357134 * 2 ^ 59
def prefixEnd_2357134 : Nat := 4983230072969 + 3 ^ 40 * 2357134 * 2
def baseEnd_2357134 : Nat := 806895139370057290723163

theorem tailTrace_2357134 : CollatzResearch.WordTrace tailWord_2357134 prefixEnd_2357134 806895139370057290723163 := by
  unfold tailWord_2357134
  simp only [CollatzResearch.WordTrace]
  refine ⟨10746467480314194910294807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57314493228342372854905637 10746467480314194910294807)
  ·
    refine ⟨16119701220471292365442211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10746467480314194910294807 16119701220471292365442211)
    ·
      refine ⟨24179551830706938548163317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16119701220471292365442211 24179551830706938548163317)
      ·
        refine ⟨2266832984128775488890311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24179551830706938548163317 2266832984128775488890311)
        ·
          refine ⟨3400249476193163233335467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266832984128775488890311 3400249476193163233335467)
          ·
            refine ⟨5100374214289744850003201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400249476193163233335467 5100374214289744850003201)
            ·
              refine ⟨3825280660717308637502401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5100374214289744850003201 3825280660717308637502401)
              ·
                refine ⟨2868960495537981478126801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3825280660717308637502401 2868960495537981478126801)
                ·
                  refine ⟨2151720371653486108595101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2868960495537981478126801 2151720371653486108595101)
                  ·
                    refine ⟨806895139370057290723163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2151720371653486108595101 806895139370057290723163)
                    ·
                      rfl

theorem cell22_2357134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_2357134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357134 prefixEnd_2357134 := by exact prefixLift 2357134
  have htrace : WordTrace (prefixWord ++ tailWord_2357134) baseStart_2357134 baseEnd_2357134 := by
    simpa [prefixWord, tailWord_2357134, baseEnd_2357134] using wordTrace_append hprefix tailTrace_2357134
  have hstable : (prefixWord ++ tailWord_2357134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357134).length < 2 ^ (prefixWord ++ tailWord_2357134).sum := by decide
  have hdescent : baseEnd_2357134 < baseStart_2357134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357166 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2357166 : Nat := 118140960795 + 2357166 * 2 ^ 59
def prefixEnd_2357166 : Nat := 4983230072969 + 3 ^ 40 * 2357166 * 2
def baseEnd_2357166 : Nat := 806906093624019873923065

theorem tailTrace_2357166 : CollatzResearch.WordTrace tailWord_2357166 prefixEnd_2357166 806906093624019873923065 := by
  unfold tailWord_2357166
  simp only [CollatzResearch.WordTrace]
  refine ⟨10746613372299703593440419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57315271318931752498348901 10746613372299703593440419)
  ·
    refine ⟨16119920058449555390160629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10746613372299703593440419 16119920058449555390160629)
    ·
      refine ⟨1511242505479645817827559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16119920058449555390160629 1511242505479645817827559)
      ·
        refine ⟨2266863758219468726741339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511242505479645817827559 2266863758219468726741339)
        ·
          refine ⟨3400295637329203090112009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266863758219468726741339 3400295637329203090112009)
          ·
            refine ⟨2550221727996902317584007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3400295637329203090112009 2550221727996902317584007)
            ·
              refine ⟨3825332591995353476376011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550221727996902317584007 3825332591995353476376011)
              ·
                refine ⟨5737998887993030214564017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3825332591995353476376011 5737998887993030214564017)
                ·
                  refine ⟨4303499165994772660923013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5737998887993030214564017 4303499165994772660923013)
                  ·
                    refine ⟨806906093624019873923065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4303499165994772660923013 806906093624019873923065)
                    ·
                      rfl

theorem cell22_2357166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2357166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357166 prefixEnd_2357166 := by exact prefixLift 2357166
  have htrace : WordTrace (prefixWord ++ tailWord_2357166) baseStart_2357166 baseEnd_2357166 := by
    simpa [prefixWord, tailWord_2357166, baseEnd_2357166] using wordTrace_append hprefix tailTrace_2357166
  have hstable : (prefixWord ++ tailWord_2357166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357166).length < 2 ^ (prefixWord ++ tailWord_2357166).sum := by decide
  have hdescent : baseEnd_2357166 < baseStart_2357166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357357 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_2357357 : Nat := 118140960795 + 2357357 * 2 ^ 59
def prefixEnd_2357357 : Nat := 4983230072969 + 3 ^ 40 * 2357357 * 2
def baseEnd_2357357 : Nat := 806971476827359042397479

theorem tailTrace_2357357 : CollatzResearch.WordTrace tailWord_2357357 prefixEnd_2357357 806971476827359042397479 := by
  unfold tailWord_2357357
  simp only [CollatzResearch.WordTrace]
  refine ⟨85979873320705668367726325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57319915547137112245150883 85979873320705668367726325)
  ·
    refine ⟨8060613123816156409474343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85979873320705668367726325 8060613123816156409474343)
    ·
      refine ⟨12090919685724234614211515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8060613123816156409474343 12090919685724234614211515)
      ·
        refine ⟨18136379528586351921317273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12090919685724234614211515 18136379528586351921317273)
        ·
          refine ⟨13602284646439763940987955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18136379528586351921317273 13602284646439763940987955)
          ·
            refine ⟨20403426969659645911481933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13602284646439763940987955 20403426969659645911481933)
            ·
              refine ⟨7651285113622367216805725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20403426969659645911481933 7651285113622367216805725)
              ·
                refine ⟨2869231917608387706302147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7651285113622367216805725 2869231917608387706302147)
                ·
                  refine ⟨4303847876412581559453221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869231917608387706302147 4303847876412581559453221)
                  ·
                    refine ⟨806971476827359042397479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4303847876412581559453221 806971476827359042397479)
                    ·
                      rfl

theorem cell22_2357357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_2357357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357357 prefixEnd_2357357 := by exact prefixLift 2357357
  have htrace : WordTrace (prefixWord ++ tailWord_2357357) baseStart_2357357 baseEnd_2357357 := by
    simpa [prefixWord, tailWord_2357357, baseEnd_2357357] using wordTrace_append hprefix tailTrace_2357357
  have hstable : (prefixWord ++ tailWord_2357357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357357).length < 2 ^ (prefixWord ++ tailWord_2357357).sum := by decide
  have hdescent : baseEnd_2357357 < baseStart_2357357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357372 : List Nat := [2, 2, 2, 1, 1, 4, 2, 4, 4]
def baseStart_2357372 : Nat := 118140960795 + 2357372 * 2 ^ 59
def prefixEnd_2357372 : Nat := 4983230072969 + 3 ^ 40 * 2357372 * 2
def baseEnd_2357372 : Nat := 268992203877968001090811

theorem tailTrace_2357372 : CollatzResearch.WordTrace tailWord_2357372 prefixEnd_2357372 268992203877968001090811 := by
  unfold tailWord_2357372
  simp only [CollatzResearch.WordTrace]
  refine ⟨42990210207825662964761185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57320280277100883953014913 42990210207825662964761185)
  ·
    refine ⟨32242657655869247223570889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42990210207825662964761185 32242657655869247223570889)
    ·
      refine ⟨24181993241901935417678167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32242657655869247223570889 24181993241901935417678167)
      ·
        refine ⟨36272989862852903126517251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24181993241901935417678167 36272989862852903126517251)
        ·
          refine ⟨54409484794279354689775877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36272989862852903126517251 54409484794279354689775877)
          ·
            refine ⟨10201778398927379004332977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54409484794279354689775877 10201778398927379004332977)
            ·
              refine ⟨7651333799195534253249733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10201778398927379004332977 7651333799195534253249733)
              ·
                refine ⟨1434625087349162672484325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7651333799195534253249733 1434625087349162672484325)
                ·
                  refine ⟨268992203877968001090811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1434625087349162672484325 268992203877968001090811)
                  ·
                    rfl

theorem cell22_2357372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_2357372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357372 prefixEnd_2357372 := by exact prefixLift 2357372
  have htrace : WordTrace (prefixWord ++ tailWord_2357372) baseStart_2357372 baseEnd_2357372 := by
    simpa [prefixWord, tailWord_2357372, baseEnd_2357372] using wordTrace_append hprefix tailTrace_2357372
  have hstable : (prefixWord ++ tailWord_2357372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357372).length < 2 ^ (prefixWord ++ tailWord_2357372).sum := by decide
  have hdescent : baseEnd_2357372 < baseStart_2357372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357438 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_2357438 : Nat := 118140960795 + 2357438 * 2 ^ 59
def prefixEnd_2357438 : Nat := 4983230072969 + 3 ^ 40 * 2357438 * 2
def baseEnd_2357438 : Nat := 806999204782701831122231

theorem tailTrace_2357438 : CollatzResearch.WordTrace tailWord_2357438 prefixEnd_2357438 806999204782701831122231 := by
  unfold tailWord_2357438
  simp only [CollatzResearch.WordTrace]
  refine ⟨10747853454176527400178121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57321885088941479467616645 10747853454176527400178121)
  ·
    refine ⟨8060890090632395550133591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10747853454176527400178121 8060890090632395550133591)
    ·
      refine ⟨12091335135948593325200387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8060890090632395550133591 12091335135948593325200387)
      ·
        refine ⟨18137002703922889987800581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12091335135948593325200387 18137002703922889987800581)
        ·
          refine ⟨3400688006985541872712609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18137002703922889987800581 3400688006985541872712609)
          ·
            refine ⟨2550516005239156404534457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3400688006985541872712609 2550516005239156404534457)
            ·
              refine ⟨1912887003929367303400843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2550516005239156404534457 1912887003929367303400843)
              ·
                refine ⟨2869330505894050955101265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1912887003929367303400843 2869330505894050955101265)
                ·
                  refine ⟨2151997879420538216325949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2869330505894050955101265 2151997879420538216325949)
                  ·
                    refine ⟨806999204782701831122231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2151997879420538216325949 806999204782701831122231)
                    ·
                      rfl

theorem cell22_2357438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_2357438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357438 prefixEnd_2357438 := by exact prefixLift 2357438
  have htrace : WordTrace (prefixWord ++ tailWord_2357438) baseStart_2357438 baseEnd_2357438 := by
    simpa [prefixWord, tailWord_2357438, baseEnd_2357438] using wordTrace_append hprefix tailTrace_2357438
  have hstable : (prefixWord ++ tailWord_2357438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357438).length < 2 ^ (prefixWord ++ tailWord_2357438).sum := by decide
  have hdescent : baseEnd_2357438 < baseStart_2357438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357479 : List Nat := [1, 1, 5, 3, 1, 2, 2, 2, 5]
def baseStart_2357479 : Nat := 118140960795 + 2357479 * 2 ^ 59
def prefixEnd_2357479 : Nat := 4983230072969 + 3 ^ 40 * 2357479 * 2
def baseEnd_2357479 : Nat := 269004413306863796949035

theorem tailTrace_2357479 : CollatzResearch.WordTrace tailWord_2357479 prefixEnd_2357479 269004413306863796949035 := by
  unfold tailWord_2357479
  simp only [CollatzResearch.WordTrace]
  refine ⟨85984323026263683203667491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57322882017509122135778327 85984323026263683203667491)
  ·
    refine ⟨128976484539395524805501237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85984323026263683203667491 128976484539395524805501237)
    ·
      refine ⟨12091545425568330450515741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128976484539395524805501237 12091545425568330450515741)
      ·
        refine ⟨4534329534588123918943403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12091545425568330450515741 4534329534588123918943403)
        ·
          refine ⟨6801494301882185878415105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4534329534588123918943403 6801494301882185878415105)
          ·
            refine ⟨5101120726411639408811329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6801494301882185878415105 5101120726411639408811329)
            ·
              refine ⟨3825840544808729556608497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5101120726411639408811329 3825840544808729556608497)
              ·
                refine ⟨2869380408606547167456373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3825840544808729556608497 2869380408606547167456373)
                ·
                  refine ⟨269004413306863796949035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2869380408606547167456373 269004413306863796949035)
                  ·
                    rfl

theorem cell22_2357479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 2, 5].length) (baseStart_2357479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357479 prefixEnd_2357479 := by exact prefixLift 2357479
  have htrace : WordTrace (prefixWord ++ tailWord_2357479) baseStart_2357479 baseEnd_2357479 := by
    simpa [prefixWord, tailWord_2357479, baseEnd_2357479] using wordTrace_append hprefix tailTrace_2357479
  have hstable : (prefixWord ++ tailWord_2357479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357479).length < 2 ^ (prefixWord ++ tailWord_2357479).sum := by decide
  have hdescent : baseEnd_2357479 < baseStart_2357479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357537 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 2, 4]
def baseStart_2357537 : Nat := 118140960795 + 2357537 * 2 ^ 59
def prefixEnd_2357537 : Nat := 4983230072969 + 3 ^ 40 * 2357537 * 2
def baseEnd_2357537 : Nat := 807033094505898572896927

theorem tailTrace_2357537 : CollatzResearch.WordTrace tailWord_2357537 prefixEnd_2357537 807033094505898572896927 := by
  unfold tailWord_2357537
  simp only [CollatzResearch.WordTrace]
  refine ⟨85986438460053559109278865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57324292306702372739519243 85986438460053559109278865)
  ·
    refine ⟨64489828845040169331959149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85986438460053559109278865 64489828845040169331959149)
    ·
      refine ⟨24183685816890063499484681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64489828845040169331959149 24183685816890063499484681)
      ·
        refine ⟨18137764362667547624613511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24183685816890063499484681 18137764362667547624613511)
        ·
          refine ⟨27206646544001321436920267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18137764362667547624613511 27206646544001321436920267)
          ·
            refine ⟨40809969816001982155380401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27206646544001321436920267 40809969816001982155380401)
            ·
              refine ⟨30607477362001486616535301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40809969816001982155380401 30607477362001486616535301)
              ·
                refine ⟨5738902005375278740600369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30607477362001486616535301 5738902005375278740600369)
                ·
                  refine ⟨4304176504031459055450277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5738902005375278740600369 4304176504031459055450277)
                  ·
                    refine ⟨807033094505898572896927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4304176504031459055450277 807033094505898572896927)
                    ·
                      rfl

theorem cell22_2357537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_2357537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357537 prefixEnd_2357537 := by exact prefixLift 2357537
  have htrace : WordTrace (prefixWord ++ tailWord_2357537) baseStart_2357537 baseEnd_2357537 := by
    simpa [prefixWord, tailWord_2357537, baseEnd_2357537] using wordTrace_append hprefix tailTrace_2357537
  have hstable : (prefixWord ++ tailWord_2357537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357537).length < 2 ^ (prefixWord ++ tailWord_2357537).sum := by decide
  have hdescent : baseEnd_2357537 < baseStart_2357537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357556 : List Nat := [2, 5, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_2357556 : Nat := 118140960795 + 2357556 * 2 ^ 59
def prefixEnd_2357556 : Nat := 4983230072969 + 3 ^ 40 * 2357556 * 2
def baseEnd_2357556 : Nat := 807039598594188856671869

theorem tailTrace_2357556 : CollatzResearch.WordTrace tailWord_2357556 prefixEnd_2357556 807039598594188856671869 := by
  unfold tailWord_2357556
  simp only [CollatzResearch.WordTrace]
  refine ⟨42993565723492362677110261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57324754297989816902813681 42993565723492362677110261)
  ·
    refine ⟨4030646786577409000979087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 42993565723492362677110261 4030646786577409000979087)
    ·
      refine ⟨6045970179866113501468631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4030646786577409000979087 6045970179866113501468631)
      ·
        refine ⟨9068955269799170252202947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6045970179866113501468631 9068955269799170252202947)
        ·
          refine ⟨13603432904698755378304421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9068955269799170252202947 13603432904698755378304421)
          ·
            refine ⟨2550643669631016633432079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13603432904698755378304421 2550643669631016633432079)
            ·
              refine ⟨3825965504446524950148119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550643669631016633432079 3825965504446524950148119)
              ·
                refine ⟨5738948256669787425222179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3825965504446524950148119 5738948256669787425222179)
                ·
                  refine ⟨8608422385004681137833269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5738948256669787425222179 8608422385004681137833269)
                  ·
                    refine ⟨807039598594188856671869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8608422385004681137833269 807039598594188856671869)
                    ·
                      rfl

theorem cell22_2357556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_2357556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357556 prefixEnd_2357556 := by exact prefixLift 2357556
  have htrace : WordTrace (prefixWord ++ tailWord_2357556) baseStart_2357556 baseEnd_2357556 := by
    simpa [prefixWord, tailWord_2357556, baseEnd_2357556] using wordTrace_append hprefix tailTrace_2357556
  have hstable : (prefixWord ++ tailWord_2357556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357556).length < 2 ^ (prefixWord ++ tailWord_2357556).sum := by decide
  have hdescent : baseEnd_2357556 < baseStart_2357556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357569 : List Nat := [1, 2, 5, 2, 2, 1, 1, 8]
def baseStart_2357569 : Nat := 118140960795 + 2357569 * 2 ^ 59
def prefixEnd_2357569 : Nat := 4983230072969 + 3 ^ 40 * 2357569 * 2
def baseEnd_2357569 : Nat := 89671560973317906232981

theorem tailTrace_2357569 : CollatzResearch.WordTrace tailWord_2357569 prefixEnd_2357569 89671560973317906232981 := by
  unfold tailWord_2357569
  simp only [CollatzResearch.WordTrace]
  refine ⟨85987605595937628574443761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57325070397291752382962507 85987605595937628574443761)
  ·
    refine ⟨64490704196953221430832821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85987605595937628574443761 64490704196953221430832821)
    ·
      refine ⟨6046003518464364509140577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64490704196953221430832821 6046003518464364509140577)
      ·
        refine ⟨4534502638848273381855433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6046003518464364509140577 4534502638848273381855433)
        ·
          refine ⟨3400876979136205036391575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4534502638848273381855433 3400876979136205036391575)
          ·
            refine ⟨5101315468704307554587363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400876979136205036391575 5101315468704307554587363)
            ·
              refine ⟨7651973203056461331881045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5101315468704307554587363 7651973203056461331881045)
              ·
                refine ⟨89671560973317906232981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7651973203056461331881045 89671560973317906232981)
                ·
                  rfl

theorem cell22_2357569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 8].length) (baseStart_2357569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357569 prefixEnd_2357569 := by exact prefixLift 2357569
  have htrace : WordTrace (prefixWord ++ tailWord_2357569) baseStart_2357569 baseEnd_2357569 := by
    simpa [prefixWord, tailWord_2357569, baseEnd_2357569] using wordTrace_append hprefix tailTrace_2357569
  have hstable : (prefixWord ++ tailWord_2357569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357569).length < 2 ^ (prefixWord ++ tailWord_2357569).sum := by decide
  have hdescent : baseEnd_2357569 < baseStart_2357569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357652 : List Nat := [2, 4, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2357652 : Nat := 118140960795 + 2357652 * 2 ^ 59
def prefixEnd_2357652 : Nat := 4983230072969 + 3 ^ 40 * 2357652 * 2
def baseEnd_2357652 : Nat := 807072461356076606271575

theorem tailTrace_2357652 : CollatzResearch.WordTrace tailWord_2357652 prefixEnd_2357652 807072461356076606271575 := by
  unfold tailWord_2357652
  simp only [CollatzResearch.WordTrace]
  refine ⟨42995316427318466874857605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57327088569757955833143473 42995316427318466874857605)
  ·
    refine ⟨8061621830122212539035801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42995316427318466874857605 8061621830122212539035801)
    ·
      refine ⟨6046216372591659404276851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8061621830122212539035801 6046216372591659404276851)
      ·
        refine ⟨9069324558887489106415277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6046216372591659404276851 9069324558887489106415277)
        ·
          refine ⟨3400996709582808414905729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9069324558887489106415277 3400996709582808414905729)
          ·
            refine ⟨2550747532187106311179297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3400996709582808414905729 2550747532187106311179297)
            ·
              refine ⟨1913060649140329733384473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2550747532187106311179297 1913060649140329733384473)
              ·
                refine ⟨1434795486855247300038355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913060649140329733384473 1434795486855247300038355)
                ·
                  refine ⟨2152193230282870950057533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434795486855247300038355 2152193230282870950057533)
                  ·
                    refine ⟨807072461356076606271575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2152193230282870950057533 807072461356076606271575)
                    ·
                      rfl

theorem cell22_2357652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2357652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357652 prefixEnd_2357652 := by exact prefixLift 2357652
  have htrace : WordTrace (prefixWord ++ tailWord_2357652) baseStart_2357652 baseEnd_2357652 := by
    simpa [prefixWord, tailWord_2357652, baseEnd_2357652] using wordTrace_append hprefix tailTrace_2357652
  have hstable : (prefixWord ++ tailWord_2357652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357652).length < 2 ^ (prefixWord ++ tailWord_2357652).sum := by decide
  have hdescent : baseEnd_2357652 < baseStart_2357652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357657 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_2357657 : Nat := 118140960795 + 2357657 * 2 ^ 59
def prefixEnd_2357657 : Nat := 4983230072969 + 3 ^ 40 * 2357657 * 2
def baseEnd_2357657 : Nat := 807074172958258259896559

theorem tailTrace_2357657 : CollatzResearch.WordTrace tailWord_2357657 prefixEnd_2357657 807074172958258259896559 := by
  unfold tailWord_2357657
  simp only [CollatzResearch.WordTrace]
  refine ⟨85990815219618819603647225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57327210146412546402431483 85990815219618819603647225)
  ·
    refine ⟨64493111414714114702735419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85990815219618819603647225 64493111414714114702735419)
    ·
      refine ⟨96739667122071172054103129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64493111414714114702735419 96739667122071172054103129)
      ·
        refine ⟨72554750341553379040577347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96739667122071172054103129 72554750341553379040577347)
        ·
          refine ⟨108832125512330068560866021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72554750341553379040577347 108832125512330068560866021)
          ·
            refine ⟨20406023533561887855162379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108832125512330068560866021 20406023533561887855162379)
            ·
              refine ⟨30609035300342831782743569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20406023533561887855162379 30609035300342831782743569)
              ·
                refine ⟨22956776475257123837057677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30609035300342831782743569 22956776475257123837057677)
                ·
                  refine ⟨8608791178221421438896629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22956776475257123837057677 8608791178221421438896629)
                  ·
                    refine ⟨807074172958258259896559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8608791178221421438896629 807074172958258259896559)
                    ·
                      rfl

theorem cell22_2357657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_2357657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357657 prefixEnd_2357657 := by exact prefixLift 2357657
  have htrace : WordTrace (prefixWord ++ tailWord_2357657) baseStart_2357657 baseEnd_2357657 := by
    simpa [prefixWord, tailWord_2357657, baseEnd_2357657] using wordTrace_append hprefix tailTrace_2357657
  have hstable : (prefixWord ++ tailWord_2357657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357657).length < 2 ^ (prefixWord ++ tailWord_2357657).sum := by decide
  have hdescent : baseEnd_2357657 < baseStart_2357657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357689 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 1, 6]
def baseStart_2357689 : Nat := 118140960795 + 2357689 * 2 ^ 59
def prefixEnd_2357689 : Nat := 4983230072969 + 3 ^ 40 * 2357689 * 2
def baseEnd_2357689 : Nat := 807085127212220843096461

theorem tailTrace_2357689 : CollatzResearch.WordTrace tailWord_2357689 prefixEnd_2357689 807085127212220843096461 := by
  unfold tailWord_2357689
  simp only [CollatzResearch.WordTrace]
  refine ⟨85991982355502889068812121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57327988237001926045874747 85991982355502889068812121)
  ·
    refine ⟨64493986766627166801609091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85991982355502889068812121 64493986766627166801609091)
    ·
      refine ⟨96740980149940750202413637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64493986766627166801609091 96740980149940750202413637)
      ·
        refine ⟨18138933778113890662952557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96740980149940750202413637 18138933778113890662952557)
        ·
          refine ⟨6802100166792708998607209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18138933778113890662952557 6802100166792708998607209)
          ·
            refine ⟨5101575125094531748955407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6802100166792708998607209 5101575125094531748955407)
            ·
              refine ⟨7652362687641797623433111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5101575125094531748955407 7652362687641797623433111)
              ·
                refine ⟨11478544031462696435149667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7652362687641797623433111 11478544031462696435149667)
                ·
                  refine ⟨17217816047194044652724501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11478544031462696435149667 17217816047194044652724501)
                  ·
                    refine ⟨807085127212220843096461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17217816047194044652724501 807085127212220843096461)
                    ·
                      rfl

theorem cell22_2357689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_2357689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357689 prefixEnd_2357689 := by exact prefixLift 2357689
  have htrace : WordTrace (prefixWord ++ tailWord_2357689) baseStart_2357689 baseEnd_2357689 := by
    simpa [prefixWord, tailWord_2357689, baseEnd_2357689] using wordTrace_append hprefix tailTrace_2357689
  have hstable : (prefixWord ++ tailWord_2357689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357689).length < 2 ^ (prefixWord ++ tailWord_2357689).sum := by decide
  have hdescent : baseEnd_2357689 < baseStart_2357689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357736 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 3, 3]
def baseStart_2357736 : Nat := 118140960795 + 2357736 * 2 ^ 59
def prefixEnd_2357736 : Nat := 4983230072969 + 3 ^ 40 * 2357736 * 2
def baseEnd_2357736 : Nat := 807101216272728387171317

theorem tailTrace_2357736 : CollatzResearch.WordTrace tailWord_2357736 prefixEnd_2357736 807101216272728387171317 := by
  unfold tailWord_2357736
  simp only [CollatzResearch.WordTrace]
  refine ⟨42996848293166308047886531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57329131057555077397182041 42996848293166308047886531)
  ·
    refine ⟨64495272439749462071829797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42996848293166308047886531 64495272439749462071829797)
    ·
      refine ⟨12092863582453024138468087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64495272439749462071829797 12092863582453024138468087)
      ·
        refine ⟨18139295373679536207702131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12092863582453024138468087 18139295373679536207702131)
        ·
          refine ⟨27208943060519304311553197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18139295373679536207702131 27208943060519304311553197)
          ·
            refine ⟨10203353647694739116832449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27208943060519304311553197 10203353647694739116832449)
            ·
              refine ⟨7652515235771054337624337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10203353647694739116832449 7652515235771054337624337)
              ·
                refine ⟨5739386426828290753218253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7652515235771054337624337 5739386426828290753218253)
                ·
                  refine ⟨2152269910060609032456845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5739386426828290753218253 2152269910060609032456845)
                  ·
                    refine ⟨807101216272728387171317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2152269910060609032456845 807101216272728387171317)
                    ·
                      rfl

theorem cell22_2357736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_2357736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357736 prefixEnd_2357736 := by exact prefixLift 2357736
  have htrace : WordTrace (prefixWord ++ tailWord_2357736) baseStart_2357736 baseEnd_2357736 := by
    simpa [prefixWord, tailWord_2357736, baseEnd_2357736] using wordTrace_append hprefix tailTrace_2357736
  have hstable : (prefixWord ++ tailWord_2357736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357736).length < 2 ^ (prefixWord ++ tailWord_2357736).sum := by decide
  have hdescent : baseEnd_2357736 < baseStart_2357736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357753 : List Nat := [1, 2, 1, 3, 1, 2, 5, 3, 1, 3]
def baseStart_2357753 : Nat := 118140960795 + 2357753 * 2 ^ 59
def prefixEnd_2357753 : Nat := 4983230072969 + 3 ^ 40 * 2357753 * 2
def baseEnd_2357753 : Nat := 807107035720146009496265

theorem tailTrace_2357753 : CollatzResearch.WordTrace tailWord_2357753 prefixEnd_2357753 807107035720146009496265 := by
  unfold tailWord_2357753
  simp only [CollatzResearch.WordTrace]
  refine ⟨85994316627271027999141913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57329544418180685332761275 85994316627271027999141913)
  ·
    refine ⟨64495737470453270999356435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85994316627271027999141913 64495737470453270999356435)
    ·
      refine ⟨96743606205679906499034653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64495737470453270999356435 96743606205679906499034653)
      ·
        refine ⟨36278852327129964937137995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96743606205679906499034653 36278852327129964937137995)
        ·
          refine ⟨54418278490694947405706993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36278852327129964937137995 54418278490694947405706993)
          ·
            refine ⟨40813708868021210554280245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54418278490694947405706993 40813708868021210554280245)
            ·
              refine ⟨3826285206376988489463773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40813708868021210554280245 3826285206376988489463773)
              ·
                refine ⟨1434856952391370683548915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3826285206376988489463773 1434856952391370683548915)
                ·
                  refine ⟨2152285428587056025323373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434856952391370683548915 2152285428587056025323373)
                  ·
                    refine ⟨807107035720146009496265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2152285428587056025323373 807107035720146009496265)
                    ·
                      rfl

theorem cell22_2357753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 3, 1, 3].length) (baseStart_2357753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357753 prefixEnd_2357753 := by exact prefixLift 2357753
  have htrace : WordTrace (prefixWord ++ tailWord_2357753) baseStart_2357753 baseEnd_2357753 := by
    simpa [prefixWord, tailWord_2357753, baseEnd_2357753] using wordTrace_append hprefix tailTrace_2357753
  have hstable : (prefixWord ++ tailWord_2357753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357753).length < 2 ^ (prefixWord ++ tailWord_2357753).sum := by decide
  have hdescent : baseEnd_2357753 < baseStart_2357753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357770 : List Nat := [3, 1, 2, 2, 2, 1, 5, 2, 1, 3]
def baseStart_2357770 : Nat := 118140960795 + 2357770 * 2 ^ 59
def prefixEnd_2357770 : Nat := 4983230072969 + 3 ^ 40 * 2357770 * 2
def baseEnd_2357770 : Nat := 807112855167563631821213

theorem tailTrace_2357770 : CollatzResearch.WordTrace tailWord_2357770 prefixEnd_2357770 807112855167563631821213 := by
  unfold tailWord_2357770
  simp only [CollatzResearch.WordTrace]
  refine ⟨21498734167052359975627691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57329957778806293268340509 21498734167052359975627691)
  ·
    refine ⟨32248101250578539963441537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21498734167052359975627691 32248101250578539963441537)
    ·
      refine ⟨24186075937933904972581153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32248101250578539963441537 24186075937933904972581153)
      ·
        refine ⟨18139556953450428729435865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24186075937933904972581153 18139556953450428729435865)
        ·
          refine ⟨13604667715087821547076899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18139556953450428729435865 13604667715087821547076899)
          ·
            refine ⟨20407001572631732320615349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13604667715087821547076899 20407001572631732320615349)
            ·
              refine ⟨1913156397434224905057689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20407001572631732320615349 1913156397434224905057689)
              ·
                refine ⟨1434867298075668678793267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913156397434224905057689 1434867298075668678793267)
                ·
                  refine ⟨2152300947113503018189901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1434867298075668678793267 2152300947113503018189901)
                  ·
                    refine ⟨807112855167563631821213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2152300947113503018189901 807112855167563631821213)
                    ·
                      rfl

theorem cell22_2357770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_2357770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357770 prefixEnd_2357770 := by exact prefixLift 2357770
  have htrace : WordTrace (prefixWord ++ tailWord_2357770) baseStart_2357770 baseEnd_2357770 := by
    simpa [prefixWord, tailWord_2357770, baseEnd_2357770] using wordTrace_append hprefix tailTrace_2357770
  have hstable : (prefixWord ++ tailWord_2357770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357770).length < 2 ^ (prefixWord ++ tailWord_2357770).sum := by decide
  have hdescent : baseEnd_2357770 < baseStart_2357770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357779 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 3, 4]
def baseStart_2357779 : Nat := 118140960795 + 2357779 * 2 ^ 59
def prefixEnd_2357779 : Nat := 4983230072969 + 3 ^ 40 * 2357779 * 2
def baseEnd_2357779 : Nat := 807115936051490608346185

theorem tailTrace_2357779 : CollatzResearch.WordTrace tailWord_2357779 prefixEnd_2357779 807115936051490608346185 := by
  unfold tailWord_2357779
  simp only [CollatzResearch.WordTrace]
  refine ⟨85995264925176834439588391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57330176616784556293058927 85995264925176834439588391)
  ·
    refine ⟨128992897387765251659382587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85995264925176834439588391 128992897387765251659382587)
    ·
      refine ⟨193489346081647877489073881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128992897387765251659382587 193489346081647877489073881)
      ·
        refine ⟨145117009561235908116805411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193489346081647877489073881 145117009561235908116805411)
        ·
          refine ⟨217675514341853862175208117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145117009561235908116805411 217675514341853862175208117)
          ·
            refine ⟨20407079469548799578925761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 217675514341853862175208117 20407079469548799578925761)
            ·
              refine ⟨15305309602161599684194321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20407079469548799578925761 15305309602161599684194321)
              ·
                refine ⟨11478982201621199763145741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15305309602161599684194321 11478982201621199763145741)
                ·
                  refine ⟨4304618325607949911179653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11478982201621199763145741 4304618325607949911179653)
                  ·
                    refine ⟨807115936051490608346185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4304618325607949911179653 807115936051490608346185)
                    ·
                      rfl

theorem cell22_2357779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 3, 4].length) (baseStart_2357779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357779 prefixEnd_2357779 := by exact prefixLift 2357779
  have htrace : WordTrace (prefixWord ++ tailWord_2357779) baseStart_2357779 baseEnd_2357779 := by
    simpa [prefixWord, tailWord_2357779, baseEnd_2357779] using wordTrace_append hprefix tailTrace_2357779
  have hstable : (prefixWord ++ tailWord_2357779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357779).length < 2 ^ (prefixWord ++ tailWord_2357779).sum := by decide
  have hdescent : baseEnd_2357779 < baseStart_2357779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357783 : List Nat := [1, 1, 3, 6, 1, 1, 1, 3, 5]
def baseStart_2357783 : Nat := 118140960795 + 2357783 * 2 ^ 59
def prefixEnd_2357783 : Nat := 4983230072969 + 3 ^ 40 * 2357783 * 2
def baseEnd_2357783 : Nat := 269039101777745310415391

theorem tailTrace_2357783 : CollatzResearch.WordTrace tailWord_2357783 prefixEnd_2357783 269039101777745310415391 := by
  unfold tailWord_2357783
  simp only [CollatzResearch.WordTrace]
  refine ⟨85995410817162343122734003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57330273878108228748489335 85995410817162343122734003)
  ·
    refine ⟨128993116225743514684101005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85995410817162343122734003 128993116225743514684101005)
    ·
      refine ⟨48372418584653818006537877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128993116225743514684101005 48372418584653818006537877)
      ·
        refine ⟨2267457121155647719056463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48372418584653818006537877 2267457121155647719056463)
        ·
          refine ⟨3401185681733471578584695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267457121155647719056463 3401185681733471578584695)
          ·
            refine ⟨5101778522600207367877043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3401185681733471578584695 5101778522600207367877043)
            ·
              refine ⟨7652667783900311051815565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5101778522600207367877043 7652667783900311051815565)
              ·
                refine ⟨2869750418962616644430837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7652667783900311051815565 2869750418962616644430837)
                ·
                  refine ⟨269039101777745310415391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2869750418962616644430837 269039101777745310415391)
                  ·
                    rfl

theorem cell22_2357783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 3, 5].length) (baseStart_2357783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357783 prefixEnd_2357783 := by exact prefixLift 2357783
  have htrace : WordTrace (prefixWord ++ tailWord_2357783) baseStart_2357783 baseEnd_2357783 := by
    simpa [prefixWord, tailWord_2357783, baseEnd_2357783] using wordTrace_append hprefix tailTrace_2357783
  have hstable : (prefixWord ++ tailWord_2357783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357783).length < 2 ^ (prefixWord ++ tailWord_2357783).sum := by decide
  have hdescent : baseEnd_2357783 < baseStart_2357783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357794 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 8]
def baseStart_2357794 : Nat := 118140960795 + 2357794 * 2 ^ 59
def prefixEnd_2357794 : Nat := 4983230072969 + 3 ^ 40 * 2357794 * 2
def baseEnd_2357794 : Nat := 269040356952678523073713

theorem tailTrace_2357794 : CollatzResearch.WordTrace tailWord_2357794 prefixEnd_2357794 269040356952678523073713 := by
  unfold tailWord_2357794
  simp only [CollatzResearch.WordTrace]
  refine ⟨21498953005030623000346109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57330541346748328000922957 21498953005030623000346109)
  ·
    refine ⟨8062107376886483625129791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21498953005030623000346109 8062107376886483625129791)
    ·
      refine ⟨12093161065329725437694687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8062107376886483625129791 12093161065329725437694687)
      ·
        refine ⟨18139741597994588156542031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12093161065329725437694687 18139741597994588156542031)
        ·
          refine ⟨27209612396991882234813047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18139741597994588156542031 27209612396991882234813047)
          ·
            refine ⟨40814418595487823352219571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27209612396991882234813047 40814418595487823352219571)
            ·
              refine ⟨61221627893231735028329357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40814418595487823352219571 61221627893231735028329357)
              ·
                refine ⟨22958110459961900635623509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61221627893231735028329357 22958110459961900635623509)
                ·
                  refine ⟨269040356952678523073713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22958110459961900635623509 269040356952678523073713)
                  ·
                    rfl

theorem cell22_2357794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_2357794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357794 prefixEnd_2357794 := by exact prefixLift 2357794
  have htrace : WordTrace (prefixWord ++ tailWord_2357794) baseStart_2357794 baseEnd_2357794 := by
    simpa [prefixWord, tailWord_2357794, baseEnd_2357794] using wordTrace_append hprefix tailTrace_2357794
  have hstable : (prefixWord ++ tailWord_2357794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357794).length < 2 ^ (prefixWord ++ tailWord_2357794).sum := by decide
  have hdescent : baseEnd_2357794 < baseStart_2357794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357809 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_2357809 : Nat := 118140960795 + 2357809 * 2 ^ 59
def prefixEnd_2357809 : Nat := 4983230072969 + 3 ^ 40 * 2357809 * 2
def baseEnd_2357809 : Nat := 807126205664580530096093

theorem tailTrace_2357809 : CollatzResearch.WordTrace tailWord_2357809 prefixEnd_2357809 807126205664580530096093 := by
  unfold tailWord_2357809
  simp only [CollatzResearch.WordTrace]
  refine ⟨85996359115068149563180481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57330906076712099708786987 85996359115068149563180481)
  ·
    refine ⟨64497269336301112172385361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85996359115068149563180481 64497269336301112172385361)
    ·
      refine ⟨48372952002225834129289021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64497269336301112172385361 48372952002225834129289021)
      ·
        refine ⟨18139857000834687798483383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48372952002225834129289021 18139857000834687798483383)
        ·
          refine ⟨27209785501252031697725075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18139857000834687798483383 27209785501252031697725075)
          ·
            refine ⟨40814678251878047546587613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27209785501252031697725075 40814678251878047546587613)
            ·
              refine ⟨15305504344454267829970355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40814678251878047546587613 15305504344454267829970355)
              ·
                refine ⟨22958256516681401744955533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15305504344454267829970355 22958256516681401744955533)
                ·
                  refine ⟨8609346193755525654358325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22958256516681401744955533 8609346193755525654358325)
                  ·
                    refine ⟨807126205664580530096093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8609346193755525654358325 807126205664580530096093)
                    ·
                      rfl

theorem cell22_2357809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_2357809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357809 prefixEnd_2357809 := by exact prefixLift 2357809
  have htrace : WordTrace (prefixWord ++ tailWord_2357809) baseStart_2357809 baseEnd_2357809 := by
    simpa [prefixWord, tailWord_2357809, baseEnd_2357809] using wordTrace_append hprefix tailTrace_2357809
  have hstable : (prefixWord ++ tailWord_2357809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357809).length < 2 ^ (prefixWord ++ tailWord_2357809).sum := by decide
  have hdescent : baseEnd_2357809 < baseStart_2357809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357811 : List Nat := [1, 1, 1, 2, 4, 2, 2, 5, 4]
def baseStart_2357811 : Nat := 118140960795 + 2357811 * 2 ^ 59
def prefixEnd_2357811 : Nat := 4983230072969 + 3 ^ 40 * 2357811 * 2
def baseEnd_2357811 : Nat := 269042296768484397182029

theorem tailTrace_2357811 : CollatzResearch.WordTrace tailWord_2357811 prefixEnd_2357811 269042296768484397182029 := by
  unfold tailWord_2357811
  simp only [CollatzResearch.WordTrace]
  refine ⟨85996432061060903904753287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57330954707373935936502191 85996432061060903904753287)
  ·
    refine ⟨128994648091591355857129931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85996432061060903904753287 128994648091591355857129931)
    ·
      refine ⟨193491972137387033785694897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128994648091591355857129931 193491972137387033785694897)
      ·
        refine ⟨145118979103040275339271173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193491972137387033785694897 145118979103040275339271173)
        ·
          refine ⟨27209808581820051626113345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145118979103040275339271173 27209808581820051626113345)
          ·
            refine ⟨20407356436365038719585009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27209808581820051626113345 20407356436365038719585009)
            ·
              refine ⟨15305517327273779039688757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20407356436365038719585009 15305517327273779039688757)
              ·
                refine ⟨1434892249431916784970821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15305517327273779039688757 1434892249431916784970821)
                ·
                  refine ⟨269042296768484397182029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1434892249431916784970821 269042296768484397182029)
                  ·
                    rfl

theorem cell22_2357811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 4].length) (baseStart_2357811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357811 prefixEnd_2357811 := by exact prefixLift 2357811
  have htrace : WordTrace (prefixWord ++ tailWord_2357811) baseStart_2357811 baseEnd_2357811 := by
    simpa [prefixWord, tailWord_2357811, baseEnd_2357811] using wordTrace_append hprefix tailTrace_2357811
  have hstable : (prefixWord ++ tailWord_2357811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357811).length < 2 ^ (prefixWord ++ tailWord_2357811).sum := by decide
  have hdescent : baseEnd_2357811 < baseStart_2357811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357813 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 1, 4]
def baseStart_2357813 : Nat := 118140960795 + 2357813 * 2 ^ 59
def prefixEnd_2357813 : Nat := 4983230072969 + 3 ^ 40 * 2357813 * 2
def baseEnd_2357813 : Nat := 807127574946325852996081

theorem tailTrace_2357813 : CollatzResearch.WordTrace tailWord_2357813 prefixEnd_2357813 807127574946325852996081 := by
  unfold tailWord_2357813
  simp only [CollatzResearch.WordTrace]
  refine ⟨85996505007053658246326093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57331003338035772164217395 85996505007053658246326093)
  ·
    refine ⟨32248689377645121842372285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85996505007053658246326093 32248689377645121842372285)
    ·
      refine ⟨12093258516616920690889607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32248689377645121842372285 12093258516616920690889607)
      ·
        refine ⟨18139887774925381036334411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12093258516616920690889607 18139887774925381036334411)
        ·
          refine ⟨27209831662388071554501617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18139887774925381036334411 27209831662388071554501617)
          ·
            refine ⟨20407373746791053665876213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27209831662388071554501617 20407373746791053665876213)
            ·
              refine ⟨1913191288761661281175895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20407373746791053665876213 1913191288761661281175895)
              ·
                refine ⟨2869786933142491921763843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913191288761661281175895 2869786933142491921763843)
                ·
                  refine ⟨4304680399713737882645765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2869786933142491921763843 4304680399713737882645765)
                  ·
                    refine ⟨807127574946325852996081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4304680399713737882645765 807127574946325852996081)
                    ·
                      rfl

theorem cell22_2357813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_2357813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357813 prefixEnd_2357813 := by exact prefixLift 2357813
  have htrace : WordTrace (prefixWord ++ tailWord_2357813) baseStart_2357813 baseEnd_2357813 := by
    simpa [prefixWord, tailWord_2357813, baseEnd_2357813] using wordTrace_append hprefix tailTrace_2357813
  have hstable : (prefixWord ++ tailWord_2357813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357813).length < 2 ^ (prefixWord ++ tailWord_2357813).sum := by decide
  have hdescent : baseEnd_2357813 < baseStart_2357813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357839 : List Nat := [1, 1, 2, 1, 1, 2, 7, 7]
def baseStart_2357839 : Nat := 118140960795 + 2357839 * 2 ^ 59
def prefixEnd_2357839 : Nat := 4983230072969 + 3 ^ 40 * 2357839 * 2
def baseEnd_2357839 : Nat := 89681830586407827982889

theorem tailTrace_2357839 : CollatzResearch.WordTrace tailWord_2357839 prefixEnd_2357839 89681830586407827982889 := by
  unfold tailWord_2357839
  simp only [CollatzResearch.WordTrace]
  refine ⟨85997453304959464686772571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57331635536639643124515047 85997453304959464686772571)
  ·
    refine ⟨128996179957439197030158857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85997453304959464686772571 128996179957439197030158857)
    ·
      refine ⟨96747134968079397772619143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128996179957439197030158857 96747134968079397772619143)
      ·
        refine ⟨145120702452119096658928715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96747134968079397772619143 145120702452119096658928715)
        ·
          refine ⟨217681053678178644988393073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145120702452119096658928715 217681053678178644988393073)
          ·
            refine ⟨163260790258633983741294805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217681053678178644988393073 163260790258633983741294805)
            ·
              refine ⟨3826424771686733993936597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 163260790258633983741294805 3826424771686733993936597)
              ·
                refine ⟨89681830586407827982889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3826424771686733993936597 89681830586407827982889)
                ·
                  rfl

theorem cell22_2357839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 7].length) (baseStart_2357839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357839 prefixEnd_2357839 := by exact prefixLift 2357839
  have htrace : WordTrace (prefixWord ++ tailWord_2357839) baseStart_2357839 baseEnd_2357839 := by
    simpa [prefixWord, tailWord_2357839, baseEnd_2357839] using wordTrace_append hprefix tailTrace_2357839
  have hstable : (prefixWord ++ tailWord_2357839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357839).length < 2 ^ (prefixWord ++ tailWord_2357839).sum := by decide
  have hdescent : baseEnd_2357839 < baseStart_2357839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357877 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 2, 3]
def baseStart_2357877 : Nat := 118140960795 + 2357877 * 2 ^ 59
def prefixEnd_2357877 : Nat := 4983230072969 + 3 ^ 40 * 2357877 * 2
def baseEnd_2357877 : Nat := 807149483454251019395885

theorem tailTrace_2357877 : CollatzResearch.WordTrace tailWord_2357877 prefixEnd_2357877 807149483454251019395885 := by
  unfold tailWord_2357877
  simp only [CollatzResearch.WordTrace]
  refine ⟨85998839278821797176655885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57332559519214531451103923 85998839278821797176655885)
  ·
    refine ⟨32249564729558173941245957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85998839278821797176655885 32249564729558173941245957)
    ·
      refine ⟨6046793386792157613983617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32249564729558173941245957 6046793386792157613983617)
      ·
        refine ⟨4535095040094118210487713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6046793386792157613983617 4535095040094118210487713)
        ·
          refine ⟨3401321280070588657865785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4535095040094118210487713 3401321280070588657865785)
          ·
            refine ⟨2550990960052941493399339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3401321280070588657865785 2550990960052941493399339)
            ·
              refine ⟨3826486440079412240099009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550990960052941493399339 3826486440079412240099009)
              ·
                refine ⟨2869864830059559180074257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3826486440079412240099009 2869864830059559180074257)
                ·
                  refine ⟨2152398622544669385055693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2869864830059559180074257 2152398622544669385055693)
                  ·
                    refine ⟨807149483454251019395885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2152398622544669385055693 807149483454251019395885)
                    ·
                      rfl

theorem cell22_2357877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_2357877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357877 prefixEnd_2357877 := by exact prefixLift 2357877
  have htrace : WordTrace (prefixWord ++ tailWord_2357877) baseStart_2357877 baseEnd_2357877 := by
    simpa [prefixWord, tailWord_2357877, baseEnd_2357877] using wordTrace_append hprefix tailTrace_2357877
  have hstable : (prefixWord ++ tailWord_2357877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357877).length < 2 ^ (prefixWord ++ tailWord_2357877).sum := by decide
  have hdescent : baseEnd_2357877 < baseStart_2357877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357888 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 3, 3]
def baseStart_2357888 : Nat := 118140960795 + 2357888 * 2 ^ 59
def prefixEnd_2357888 : Nat := 4983230072969 + 3 ^ 40 * 2357888 * 2
def baseEnd_2357888 : Nat := 807153248979050657370851

theorem tailTrace_2357888 : CollatzResearch.WordTrace tailWord_2357888 prefixEnd_2357888 807153248979050657370851 := by
  unfold tailWord_2357888
  simp only [CollatzResearch.WordTrace]
  refine ⟨42999620240890973027653159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57332826987854630703537545 42999620240890973027653159)
  ·
    refine ⟨64499430361336459541479739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42999620240890973027653159 64499430361336459541479739)
    ·
      refine ⟨96749145542004689312219609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64499430361336459541479739 96749145542004689312219609)
      ·
        refine ⟨72561859156503516984164707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96749145542004689312219609 72561859156503516984164707)
        ·
          refine ⟨108842788734755275476247061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72561859156503516984164707 108842788734755275476247061)
          ·
            refine ⟨5102005721941653537949081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108842788734755275476247061 5102005721941653537949081)
            ·
              refine ⟨3826504291456240153461811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5102005721941653537949081 3826504291456240153461811)
              ·
                refine ⟨5739756437184360230192717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3826504291456240153461811 5739756437184360230192717)
                ·
                  refine ⟨2152408663944135086322269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5739756437184360230192717 2152408663944135086322269)
                  ·
                    refine ⟨807153248979050657370851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2152408663944135086322269 807153248979050657370851)
                    ·
                      rfl

theorem cell22_2357888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 3, 3].length) (baseStart_2357888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357888 prefixEnd_2357888 := by exact prefixLift 2357888
  have htrace : WordTrace (prefixWord ++ tailWord_2357888) baseStart_2357888 baseEnd_2357888 := by
    simpa [prefixWord, tailWord_2357888, baseEnd_2357888] using wordTrace_append hprefix tailTrace_2357888
  have hstable : (prefixWord ++ tailWord_2357888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357888).length < 2 ^ (prefixWord ++ tailWord_2357888).sum := by decide
  have hdescent : baseEnd_2357888 < baseStart_2357888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357899 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 1, 7]
def baseStart_2357899 : Nat := 118140960795 + 2357899 * 2 ^ 59
def prefixEnd_2357899 : Nat := 4983230072969 + 3 ^ 40 * 2357899 * 2
def baseEnd_2357899 : Nat := 807157014503850295345817

theorem tailTrace_2357899 : CollatzResearch.WordTrace tailWord_2357899 prefixEnd_2357899 807157014503850295345817 := by
  unfold tailWord_2357899
  simp only [CollatzResearch.WordTrace]
  refine ⟨85999641684742094933956751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57333094456494729955971167 85999641684742094933956751)
  ·
    refine ⟨128999462527113142400935127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85999641684742094933956751 128999462527113142400935127)
    ·
      refine ⟨193499193790669713601402691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128999462527113142400935127 193499193790669713601402691)
      ·
        refine ⟨290248790686004570402104037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193499193790669713601402691 290248790686004570402104037)
        ·
          refine ⟨54421648253625856950394507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 290248790686004570402104037 54421648253625856950394507)
          ·
            refine ⟨81632472380438785425591761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54421648253625856950394507 81632472380438785425591761)
            ·
              refine ⟨61224354285329089069193821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81632472380438785425591761 61224354285329089069193821)
              ·
                refine ⟨22959132856998408400947683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61224354285329089069193821 22959132856998408400947683)
                ·
                  refine ⟨34438699285497612601421525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22959132856998408400947683 34438699285497612601421525)
                  ·
                    refine ⟨807157014503850295345817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34438699285497612601421525 807157014503850295345817)
                    ·
                      rfl

theorem cell22_2357899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 7].length) (baseStart_2357899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357899 prefixEnd_2357899 := by exact prefixLift 2357899
  have htrace : WordTrace (prefixWord ++ tailWord_2357899) baseStart_2357899 baseEnd_2357899 := by
    simpa [prefixWord, tailWord_2357899, baseEnd_2357899] using wordTrace_append hprefix tailTrace_2357899
  have hstable : (prefixWord ++ tailWord_2357899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357899).length < 2 ^ (prefixWord ++ tailWord_2357899).sum := by decide
  have hdescent : baseEnd_2357899 < baseStart_2357899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2357929 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 10]
def baseStart_2357929 : Nat := 118140960795 + 2357929 * 2 ^ 59
def prefixEnd_2357929 : Nat := 4983230072969 + 3 ^ 40 * 2357929 * 2
def baseEnd_2357929 : Nat := 269055761372313405698575

theorem tailTrace_2357929 : CollatzResearch.WordTrace tailWord_2357929 prefixEnd_2357929 269055761372313405698575 := by
  unfold tailWord_2357929
  simp only [CollatzResearch.WordTrace]
  refine ⟨86000735874633410057548841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57333823916422273371699227 86000735874633410057548841)
  ·
    refine ⟨64500551905975057543161631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86000735874633410057548841 64500551905975057543161631)
    ·
      refine ⟨96750827858962586314742447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64500551905975057543161631 96750827858962586314742447)
      ·
        refine ⟨145126241788443879472113671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96750827858962586314742447 145126241788443879472113671)
        ·
          refine ⟨217689362682665819208170507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145126241788443879472113671 217689362682665819208170507)
          ·
            refine ⟨326534044023998728812255761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217689362682665819208170507 326534044023998728812255761)
            ·
              refine ⟨244900533017999046609191821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326534044023998728812255761 244900533017999046609191821)
              ·
                refine ⟨91837699881749642478446933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244900533017999046609191821 91837699881749642478446933)
                ·
                  refine ⟨269055761372313405698575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 91837699881749642478446933 269055761372313405698575)
                  ·
                    rfl

theorem cell22_2357929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_2357929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2357929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2357929 prefixEnd_2357929 := by exact prefixLift 2357929
  have htrace : WordTrace (prefixWord ++ tailWord_2357929) baseStart_2357929 baseEnd_2357929 := by
    simpa [prefixWord, tailWord_2357929, baseEnd_2357929] using wordTrace_append hprefix tailTrace_2357929
  have hstable : (prefixWord ++ tailWord_2357929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2357929).length < 2 ^ (prefixWord ++ tailWord_2357929).sum := by decide
  have hdescent : baseEnd_2357929 < baseStart_2357929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2357929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358115 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 6]
def baseStart_2358115 : Nat := 118140960795 + 2358115 * 2 ^ 59
def prefixEnd_2358115 : Nat := 4983230072969 + 3 ^ 40 * 2358115 * 2
def baseEnd_2358115 : Nat := 269076985239365910648385

theorem tailTrace_2358115 : CollatzResearch.WordTrace tailWord_2358115 prefixEnd_2358115 269076985239365910648385 := by
  unfold tailWord_2358115
  simp only [CollatzResearch.WordTrace]
  refine ⟨86007519851959563823819799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57338346567973042549213199 86007519851959563823819799)
  ·
    refine ⟨129011279777939345735729699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86007519851959563823819799 129011279777939345735729699)
    ·
      refine ⟨193516919666909018603594549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129011279777939345735729699 193516919666909018603594549)
      ·
        refine ⟨18142211218772720494086989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193516919666909018603594549 18142211218772720494086989)
        ·
          refine ⟨6803329207039770185282621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18142211218772720494086989 6803329207039770185282621)
          ·
            refine ⟨2551248452639913819480983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6803329207039770185282621 2551248452639913819480983)
            ·
              refine ⟨3826872678959870729221475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2551248452639913819480983 3826872678959870729221475)
              ·
                refine ⟨5740309018439806093832213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3826872678959870729221475 5740309018439806093832213)
                ·
                  refine ⟨269076985239365910648385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5740309018439806093832213 269076985239365910648385)
                  ·
                    rfl

theorem cell22_2358115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 6].length) (baseStart_2358115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358115 prefixEnd_2358115 := by exact prefixLift 2358115
  have htrace : WordTrace (prefixWord ++ tailWord_2358115) baseStart_2358115 baseEnd_2358115 := by
    simpa [prefixWord, tailWord_2358115, baseEnd_2358115] using wordTrace_append hprefix tailTrace_2358115
  have hstable : (prefixWord ++ tailWord_2358115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358115).length < 2 ^ (prefixWord ++ tailWord_2358115).sum := by decide
  have hdescent : baseEnd_2358115 < baseStart_2358115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358134 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_2358134 : Nat := 118140960795 + 2358134 * 2 ^ 59
def prefixEnd_2358134 : Nat := 4983230072969 + 3 ^ 40 * 2358134 * 2
def baseEnd_2358134 : Nat := 807237459806388015720097

theorem tailTrace_2358134 : CollatzResearch.WordTrace tailWord_2358134 prefixEnd_2358134 807237459806388015720097 := by
  unfold tailWord_2358134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5375513302430670629297591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57338808559260486712507637 5375513302430670629297591)
  ·
    refine ⟨8063269953646005943946387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5375513302430670629297591 8063269953646005943946387)
    ·
      refine ⟨12094904930469008915919581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8063269953646005943946387 12094904930469008915919581)
      ·
        refine ⟨4535589348925878343469843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12094904930469008915919581 4535589348925878343469843)
        ·
          refine ⟨6803384023388817515204765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4535589348925878343469843 6803384023388817515204765)
          ·
            refine ⟨2551269008770806568201787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6803384023388817515204765 2551269008770806568201787)
            ·
              refine ⟨3826903513156209852302681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2551269008770806568201787 3826903513156209852302681)
              ·
                refine ⟨2870177634867157389227011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3826903513156209852302681 2870177634867157389227011)
                ·
                  refine ⟨4305266452300736083840517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870177634867157389227011 4305266452300736083840517)
                  ·
                    refine ⟨807237459806388015720097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4305266452300736083840517 807237459806388015720097)
                    ·
                      rfl

theorem cell22_2358134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_2358134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358134 prefixEnd_2358134 := by exact prefixLift 2358134
  have htrace : WordTrace (prefixWord ++ tailWord_2358134) baseStart_2358134 baseEnd_2358134 := by
    simpa [prefixWord, tailWord_2358134, baseEnd_2358134] using wordTrace_append hprefix tailTrace_2358134
  have hstable : (prefixWord ++ tailWord_2358134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358134).length < 2 ^ (prefixWord ++ tailWord_2358134).sum := by decide
  have hdescent : baseEnd_2358134 < baseStart_2358134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358166 : List Nat := [5, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2358166 : Nat := 118140960795 + 2358166 * 2 ^ 59
def prefixEnd_2358166 : Nat := 4983230072969 + 3 ^ 40 * 2358166 * 2
def baseEnd_2358166 : Nat := 269082804686783532973333

theorem tailTrace_2358166 : CollatzResearch.WordTrace tailWord_2358166 prefixEnd_2358166 269082804686783532973333 := by
  unfold tailWord_2358166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5375586248423424970870397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57339586649849866355950901 5375586248423424970870397)
  ·
    refine ⟨2015844843158784364076399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5375586248423424970870397 2015844843158784364076399)
    ·
      refine ⟨3023767264738176546114599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2015844843158784364076399 3023767264738176546114599)
      ·
        refine ⟨4535650897107264819171899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3023767264738176546114599 4535650897107264819171899)
        ·
          refine ⟨6803476345660897228757849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4535650897107264819171899 6803476345660897228757849)
          ·
            refine ⟨5102607259245672921568387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6803476345660897228757849 5102607259245672921568387)
            ·
              refine ⟨7653910888868509382352581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5102607259245672921568387 7653910888868509382352581)
              ·
                refine ⟨1435108291662845509191109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7653910888868509382352581 1435108291662845509191109)
                ·
                  refine ⟨269082804686783532973333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435108291662845509191109 269082804686783532973333)
                  ·
                    rfl

theorem cell22_2358166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2358166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358166 prefixEnd_2358166 := by exact prefixLift 2358166
  have htrace : WordTrace (prefixWord ++ tailWord_2358166) baseStart_2358166 baseEnd_2358166 := by
    simpa [prefixWord, tailWord_2358166, baseEnd_2358166] using wordTrace_append hprefix tailTrace_2358166
  have hstable : (prefixWord ++ tailWord_2358166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358166).length < 2 ^ (prefixWord ++ tailWord_2358166).sum := by decide
  have hdescent : baseEnd_2358166 < baseStart_2358166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358173 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_2358173 : Nat := 118140960795 + 2358173 * 2 ^ 59
def prefixEnd_2358173 : Nat := 4983230072969 + 3 ^ 40 * 2358173 * 2
def baseEnd_2358173 : Nat := 807250810303404913994977

theorem tailTrace_2358173 : CollatzResearch.WordTrace tailWord_2358173 prefixEnd_2358173 807250810303404913994977 := by
  unfold tailWord_2358173
  simp only [CollatzResearch.WordTrace]
  refine ⟨86009635285749439729431173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57339756857166293152954115 86009635285749439729431173)
  ·
    refine ⟨16126806616078019949268345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86009635285749439729431173 16126806616078019949268345)
    ·
      refine ⟨12095104962058514961951259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16126806616078019949268345 12095104962058514961951259)
      ·
        refine ⟨18142657443087772442926889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12095104962058514961951259 18142657443087772442926889)
        ·
          refine ⟨13606993082315829332195167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18142657443087772442926889 13606993082315829332195167)
          ·
            refine ⟨20410489623473743998292751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13606993082315829332195167 20410489623473743998292751)
            ·
              refine ⟨30615734435210615997439127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20410489623473743998292751 30615734435210615997439127)
              ·
                refine ⟨45923601652815923996158691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30615734435210615997439127 45923601652815923996158691)
                ·
                  refine ⟨68885402479223885994238037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45923601652815923996158691 68885402479223885994238037)
                  ·
                    refine ⟨807250810303404913994977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68885402479223885994238037 807250810303404913994977)
                    ·
                      rfl

theorem cell22_2358173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_2358173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358173 prefixEnd_2358173 := by exact prefixLift 2358173
  have htrace : WordTrace (prefixWord ++ tailWord_2358173) baseStart_2358173 baseEnd_2358173 := by
    simpa [prefixWord, tailWord_2358173, baseEnd_2358173] using wordTrace_append hprefix tailTrace_2358173
  have hstable : (prefixWord ++ tailWord_2358173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358173).length < 2 ^ (prefixWord ++ tailWord_2358173).sum := by decide
  have hdescent : baseEnd_2358173 < baseStart_2358173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358222 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_2358222 : Nat := 118140960795 + 2358222 * 2 ^ 59
def prefixEnd_2358222 : Nat := 4983230072969 + 3 ^ 40 * 2358222 * 2
def baseEnd_2358222 : Nat := 269089194668261706506609

theorem tailTrace_2358222 : CollatzResearch.WordTrace tailWord_2358222 prefixEnd_2358222 269089194668261706506609 := by
  unfold tailWord_2358222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10751427807821490137245615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57340948308381280731976613 10751427807821490137245615)
  ·
    refine ⟨16127141711732235205868423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10751427807821490137245615 16127141711732235205868423)
    ·
      refine ⟨24190712567598352808802635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16127141711732235205868423 24190712567598352808802635)
      ·
        refine ⟨36286068851397529213203953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24190712567598352808802635 36286068851397529213203953)
        ·
          refine ⟨27214551638548146909902965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36286068851397529213203953 27214551638548146909902965)
          ·
            refine ⟨2551364216113888772803403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27214551638548146909902965 2551364216113888772803403)
            ·
              refine ⟨3827046324170833159205105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2551364216113888772803403 3827046324170833159205105)
              ·
                refine ⟨2870284743128124869403829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3827046324170833159205105 2870284743128124869403829)
                ·
                  refine ⟨269089194668261706506609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2870284743128124869403829 269089194668261706506609)
                  ·
                    rfl

theorem cell22_2358222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_2358222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358222 prefixEnd_2358222 := by exact prefixLift 2358222
  have htrace : WordTrace (prefixWord ++ tailWord_2358222) baseStart_2358222 baseEnd_2358222 := by
    simpa [prefixWord, tailWord_2358222, baseEnd_2358222] using wordTrace_append hprefix tailTrace_2358222
  have hstable : (prefixWord ++ tailWord_2358222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358222).length < 2 ^ (prefixWord ++ tailWord_2358222).sum := by decide
  have hdescent : baseEnd_2358222 < baseStart_2358222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358250 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_2358250 : Nat := 118140960795 + 2358250 * 2 ^ 59
def prefixEnd_2358250 : Nat := 4983230072969 + 3 ^ 40 * 2358250 * 2
def baseEnd_2358250 : Nat := 269092389659000793273247

theorem tailTrace_2358250 : CollatzResearch.WordTrace tailWord_2358250 prefixEnd_2358250 269092389659000793273247 := by
  unfold tailWord_2358250
  simp only [CollatzResearch.WordTrace]
  refine ⟨21503110926617620469996051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57341629137646987919989469 21503110926617620469996051)
  ·
    refine ⟨32254666389926430704994077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21503110926617620469996051 32254666389926430704994077)
    ·
      refine ⟨12095499896222411514372779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32254666389926430704994077 12095499896222411514372779)
      ·
        refine ⟨18143249844333617271559169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12095499896222411514372779 18143249844333617271559169)
        ·
          refine ⟨13607437383250212953669377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18143249844333617271559169 13607437383250212953669377)
          ·
            refine ⟨10205578037437659715252033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13607437383250212953669377 10205578037437659715252033)
            ·
              refine ⟨7654183528078244786439025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10205578037437659715252033 7654183528078244786439025)
              ·
                refine ⟨5740637646058683589829269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7654183528078244786439025 5740637646058683589829269)
                ·
                  refine ⟨269092389659000793273247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5740637646058683589829269 269092389659000793273247)
                  ·
                    rfl

theorem cell22_2358250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_2358250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358250 prefixEnd_2358250 := by exact prefixLift 2358250
  have htrace : WordTrace (prefixWord ++ tailWord_2358250) baseStart_2358250 baseEnd_2358250 := by
    simpa [prefixWord, tailWord_2358250, baseEnd_2358250] using wordTrace_append hprefix tailTrace_2358250
  have hstable : (prefixWord ++ tailWord_2358250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358250).length < 2 ^ (prefixWord ++ tailWord_2358250).sum := by decide
  have hdescent : baseEnd_2358250 < baseStart_2358250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358265 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 6, 3]
def baseStart_2358265 : Nat := 118140960795 + 2358265 * 2 ^ 59
def prefixEnd_2358265 : Nat := 4983230072969 + 3 ^ 40 * 2358265 * 2
def baseEnd_2358265 : Nat := 807282303783547340694695

theorem tailTrace_2358265 : CollatzResearch.WordTrace tailWord_2358265 prefixEnd_2358265 807282303783547340694695 := by
  unfold tailWord_2358265
  simp only [CollatzResearch.WordTrace]
  refine ⟨86012990801416139441780249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57341993867610759627853499 86012990801416139441780249)
  ·
    refine ⟨64509743101062104581335187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86012990801416139441780249 64509743101062104581335187)
    ·
      refine ⟨96764614651593156872002781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64509743101062104581335187 96764614651593156872002781)
      ·
        refine ⟨36286730494347433827001043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96764614651593156872002781 36286730494347433827001043)
        ·
          refine ⟨54430095741521150740501565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36286730494347433827001043 54430095741521150740501565)
          ·
            refine ⟨20411285903070431527688087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54430095741521150740501565 20411285903070431527688087)
            ·
              refine ⟨30616928854605647291532131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20411285903070431527688087 30616928854605647291532131)
              ·
                refine ⟨45925393281908470937298197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30616928854605647291532131 45925393281908470937298197)
                ·
                  refine ⟨2152752810089459575185853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45925393281908470937298197 2152752810089459575185853)
                  ·
                    refine ⟨807282303783547340694695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2152752810089459575185853 807282303783547340694695)
                    ·
                      rfl

theorem cell22_2358265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 6, 3].length) (baseStart_2358265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358265 prefixEnd_2358265 := by exact prefixLift 2358265
  have htrace : WordTrace (prefixWord ++ tailWord_2358265) baseStart_2358265 baseEnd_2358265 := by
    simpa [prefixWord, tailWord_2358265, baseEnd_2358265] using wordTrace_append hprefix tailTrace_2358265
  have hstable : (prefixWord ++ tailWord_2358265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358265).length < 2 ^ (prefixWord ++ tailWord_2358265).sum := by decide
  have hdescent : baseEnd_2358265 < baseStart_2358265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358280 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 4, 4]
def baseStart_2358280 : Nat := 118140960795 + 2358280 * 2 ^ 59
def prefixEnd_2358280 : Nat := 4983230072969 + 3 ^ 40 * 2358280 * 2
def baseEnd_2358280 : Nat := 807287438590092301569649

theorem tailTrace_2358280 : CollatzResearch.WordTrace tailWord_2358280 prefixEnd_2358280 807287438590092301569649 := by
  unfold tailWord_2358280
  simp only [CollatzResearch.WordTrace]
  refine ⟨43006768948180898501788147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57342358597574531335717529 43006768948180898501788147)
  ·
    refine ⟨64510153422271347752682221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43006768948180898501788147 64510153422271347752682221)
    ·
      refine ⟨24191307533351755407255833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64510153422271347752682221 24191307533351755407255833)
      ·
        refine ⟨18143480650013816555441875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24191307533351755407255833 18143480650013816555441875)
        ·
          refine ⟨27215220975020724833162813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18143480650013816555441875 27215220975020724833162813)
          ·
            refine ⟨10205707865632771812436055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27215220975020724833162813 10205707865632771812436055)
            ·
              refine ⟨15308561798449157718654083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10205707865632771812436055 15308561798449157718654083)
              ·
                refine ⟨22962842697673736577981125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15308561798449157718654083 22962842697673736577981125)
                ·
                  refine ⟨4305533005813825608371461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22962842697673736577981125 4305533005813825608371461)
                  ·
                    refine ⟨807287438590092301569649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4305533005813825608371461 807287438590092301569649)
                    ·
                      rfl

theorem cell22_2358280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_2358280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358280 prefixEnd_2358280 := by exact prefixLift 2358280
  have htrace : WordTrace (prefixWord ++ tailWord_2358280) baseStart_2358280 baseEnd_2358280 := by
    simpa [prefixWord, tailWord_2358280, baseEnd_2358280] using wordTrace_append hprefix tailTrace_2358280
  have hstable : (prefixWord ++ tailWord_2358280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358280).length < 2 ^ (prefixWord ++ tailWord_2358280).sum := by decide
  have hdescent : baseEnd_2358280 < baseStart_2358280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358282 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 4, 3]
def baseStart_2358282 : Nat := 118140960795 + 2358282 * 2 ^ 59
def prefixEnd_2358282 : Nat := 4983230072969 + 3 ^ 40 * 2358282 * 2
def baseEnd_2358282 : Nat := 807288123230964963019643

theorem tailTrace_2358282 : CollatzResearch.WordTrace tailWord_2358282 prefixEnd_2358282 807288123230964963019643 := by
  unfold tailWord_2358282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21503402710588637836287275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57342407228236367563432733 21503402710588637836287275)
  ·
    refine ⟨32255104065882956754430913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21503402710588637836287275 32255104065882956754430913)
    ·
      refine ⟨24191328049412217565823185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32255104065882956754430913 24191328049412217565823185)
      ·
        refine ⟨18143496037059163174367389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24191328049412217565823185 18143496037059163174367389)
        ·
          refine ⟨6803811013897186190387771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18143496037059163174367389 6803811013897186190387771)
          ·
            refine ⟨10205716520845779285581657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6803811013897186190387771 10205716520845779285581657)
            ·
              refine ⟨7654287390634334464186243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10205716520845779285581657 7654287390634334464186243)
              ·
                refine ⟨11481431085951501696279365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7654287390634334464186243 11481431085951501696279365)
                ·
                  refine ⟨2152768328615906568052381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11481431085951501696279365 2152768328615906568052381)
                  ·
                    refine ⟨807288123230964963019643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2152768328615906568052381 807288123230964963019643)
                    ·
                      rfl

theorem cell22_2358282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_2358282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358282 prefixEnd_2358282 := by exact prefixLift 2358282
  have htrace : WordTrace (prefixWord ++ tailWord_2358282) baseStart_2358282 baseEnd_2358282 := by
    simpa [prefixWord, tailWord_2358282, baseEnd_2358282] using wordTrace_append hprefix tailTrace_2358282
  have hstable : (prefixWord ++ tailWord_2358282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358282).length < 2 ^ (prefixWord ++ tailWord_2358282).sum := by decide
  have hdescent : baseEnd_2358282 < baseStart_2358282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358284 : List Nat := [2, 2, 1, 2, 3, 3, 3, 2, 4]
def baseStart_2358284 : Nat := 118140960795 + 2358284 * 2 ^ 59
def prefixEnd_2358284 : Nat := 4983230072969 + 3 ^ 40 * 2358284 * 2
def baseEnd_2358284 : Nat := 269096269290612541489879

theorem tailTrace_2358284 : CollatzResearch.WordTrace tailWord_2358284 prefixEnd_2358284 269096269290612541489879 := by
  unfold tailWord_2358284
  simp only [CollatzResearch.WordTrace]
  refine ⟨43006841894173652843360953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57342455858898203791147937 43006841894173652843360953)
  ·
    refine ⟨32255131420630239632520715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43006841894173652843360953 32255131420630239632520715)
    ·
      refine ⟨48382697130945359448781073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32255131420630239632520715 48382697130945359448781073)
      ·
        refine ⟨36287022848209019586585805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48382697130945359448781073 36287022848209019586585805)
        ·
          refine ⟨13607633568078382344969677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36287022848209019586585805 13607633568078382344969677)
          ·
            refine ⟨5102862588029393379363629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13607633568078382344969677 5102862588029393379363629)
            ·
              refine ⟨1913573470511022517261361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5102862588029393379363629 1913573470511022517261361)
              ·
                refine ⟨1435180102883266887946021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913573470511022517261361 1435180102883266887946021)
                ·
                  refine ⟨269096269290612541489879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435180102883266887946021 269096269290612541489879)
                  ·
                    rfl

theorem cell22_2358284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 2, 4].length) (baseStart_2358284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358284 prefixEnd_2358284 := by exact prefixLift 2358284
  have htrace : WordTrace (prefixWord ++ tailWord_2358284) baseStart_2358284 baseEnd_2358284 := by
    simpa [prefixWord, tailWord_2358284, baseEnd_2358284] using wordTrace_append hprefix tailTrace_2358284
  have hstable : (prefixWord ++ tailWord_2358284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358284).length < 2 ^ (prefixWord ++ tailWord_2358284).sum := by decide
  have hdescent : baseEnd_2358284 < baseStart_2358284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358290 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 5]
def baseStart_2358290 : Nat := 118140960795 + 2358290 * 2 ^ 59
def prefixEnd_2358290 : Nat := 4983230072969 + 3 ^ 40 * 2358290 * 2
def baseEnd_2358290 : Nat := 269096953931485202939873

theorem tailTrace_2358290 : CollatzResearch.WordTrace tailWord_2358290 prefixEnd_2358290 269096953931485202939873 := by
  unfold tailWord_2358290
  simp only [CollatzResearch.WordTrace]
  refine ⟨21503475656581392177860081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57342601750883712474293549 21503475656581392177860081)
  ·
    refine ⟨16127606742436044133395061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21503475656581392177860081 16127606742436044133395061)
    ·
      refine ⟨1511963132103379137505787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16127606742436044133395061 1511963132103379137505787)
      ·
        refine ⟨2267944698155068706258681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511963132103379137505787 2267944698155068706258681)
        ·
          refine ⟨1700958523616301529694011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2267944698155068706258681 1700958523616301529694011)
          ·
            refine ⟨2551437785424452294541017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700958523616301529694011 2551437785424452294541017)
            ·
              refine ⟨1913578339068339220905763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2551437785424452294541017 1913578339068339220905763)
              ·
                refine ⟨2870367508602508831358645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913578339068339220905763 2870367508602508831358645)
                ·
                  refine ⟨269096953931485202939873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2870367508602508831358645 269096953931485202939873)
                  ·
                    rfl

theorem cell22_2358290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_2358290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358290 prefixEnd_2358290 := by exact prefixLift 2358290
  have htrace : WordTrace (prefixWord ++ tailWord_2358290) baseStart_2358290 baseEnd_2358290 := by
    simpa [prefixWord, tailWord_2358290, baseEnd_2358290] using wordTrace_append hprefix tailTrace_2358290
  have hstable : (prefixWord ++ tailWord_2358290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358290).length < 2 ^ (prefixWord ++ tailWord_2358290).sum := by decide
  have hdescent : baseEnd_2358290 < baseStart_2358290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358295 : List Nat := [1, 1, 3, 5, 1, 1, 1, 9]
def baseStart_2358295 : Nat := 118140960795 + 2358295 * 2 ^ 59
def prefixEnd_2358295 : Nat := 4983230072969 + 3 ^ 40 * 2358295 * 2
def baseEnd_2358295 : Nat := 89699174821848584716067

theorem tailTrace_2358295 : CollatzResearch.WordTrace tailWord_2358295 prefixEnd_2358295 89699174821848584716067 := by
  unfold tailWord_2358295
  simp only [CollatzResearch.WordTrace]
  refine ⟨86014084991307454565372339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57342723327538303043581559 86014084991307454565372339)
  ·
    refine ⟨129021127486961181848058509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86014084991307454565372339 129021127486961181848058509)
    ·
      refine ⟨48382922807610443193021941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129021127486961181848058509 48382922807610443193021941)
      ·
        refine ⟨4535899013213479049345807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48382922807610443193021941 4535899013213479049345807)
        ·
          refine ⟨6803848519820218574018711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4535899013213479049345807 6803848519820218574018711)
          ·
            refine ⟨10205772779730327861028067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6803848519820218574018711 10205772779730327861028067)
            ·
              refine ⟨15308659169595491791542101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10205772779730327861028067 15308659169595491791542101)
              ·
                refine ⟨89699174821848584716067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15308659169595491791542101 89699174821848584716067)
                ·
                  rfl

theorem cell22_2358295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 9].length) (baseStart_2358295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358295 prefixEnd_2358295 := by exact prefixLift 2358295
  have htrace : WordTrace (prefixWord ++ tailWord_2358295) baseStart_2358295 baseEnd_2358295 := by
    simpa [prefixWord, tailWord_2358295, baseEnd_2358295] using wordTrace_append hprefix tailTrace_2358295
  have hstable : (prefixWord ++ tailWord_2358295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358295).length < 2 ^ (prefixWord ++ tailWord_2358295).sum := by decide
  have hdescent : baseEnd_2358295 < baseStart_2358295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358314 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2358314 : Nat := 118140960795 + 2358314 * 2 ^ 59
def prefixEnd_2358314 : Nat := 4983230072969 + 3 ^ 40 * 2358314 * 2
def baseEnd_2358314 : Nat := 807299077484927546219545

theorem tailTrace_2358314 : CollatzResearch.WordTrace tailWord_2358314 prefixEnd_2358314 807299077484927546219545 := by
  unfold tailWord_2358314
  simp only [CollatzResearch.WordTrace]
  refine ⟨21503694494559655202578499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57343185318825747206875997 21503694494559655202578499)
  ·
    refine ⟨32255541741839482803867749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21503694494559655202578499 32255541741839482803867749)
    ·
      refine ⟨6047914076594903025725203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32255541741839482803867749 6047914076594903025725203)
      ·
        refine ⟨9071871114892354538587805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6047914076594903025725203 9071871114892354538587805)
        ·
          refine ⟨3401951668084632951970427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9071871114892354538587805 3401951668084632951970427)
          ·
            refine ⟨5102927502126949427955641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3401951668084632951970427 5102927502126949427955641)
            ·
              refine ⟨3827195626595212070966731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5102927502126949427955641 3827195626595212070966731)
              ·
                refine ⟨5740793439892818106450097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3827195626595212070966731 5740793439892818106450097)
                ·
                  refine ⟨4305595079919613579837573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5740793439892818106450097 4305595079919613579837573)
                  ·
                    refine ⟨807299077484927546219545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4305595079919613579837573 807299077484927546219545)
                    ·
                      rfl

theorem cell22_2358314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2358314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358314 prefixEnd_2358314 := by exact prefixLift 2358314
  have htrace : WordTrace (prefixWord ++ tailWord_2358314) baseStart_2358314 baseEnd_2358314 := by
    simpa [prefixWord, tailWord_2358314, baseEnd_2358314] using wordTrace_append hprefix tailTrace_2358314
  have hstable : (prefixWord ++ tailWord_2358314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358314).length < 2 ^ (prefixWord ++ tailWord_2358314).sum := by decide
  have hdescent : baseEnd_2358314 < baseStart_2358314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358344 : List Nat := [2, 1, 3, 1, 1, 1, 5, 4, 1, 3]
def baseStart_2358344 : Nat := 118140960795 + 2358344 * 2 ^ 59
def prefixEnd_2358344 : Nat := 4983230072969 + 3 ^ 40 * 2358344 * 2
def baseEnd_2358344 : Nat := 807309347098017467969453

theorem tailTrace_2358344 : CollatzResearch.WordTrace tailWord_2358344 prefixEnd_2358344 807309347098017467969453 := by
  unfold tailWord_2358344
  simp only [CollatzResearch.WordTrace]
  refine ⟨43007936084064967966953043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57343914778753290622604057 43007936084064967966953043)
  ·
    refine ⟨64511904126097451950429565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43007936084064967966953043 64511904126097451950429565)
    ·
      refine ⟨24191964047286544481411087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64511904126097451950429565 24191964047286544481411087)
      ·
        refine ⟨36287946070929816722116631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24191964047286544481411087 36287946070929816722116631)
        ·
          refine ⟨54431919106394725083174947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36287946070929816722116631 54431919106394725083174947)
          ·
            refine ⟨81647878659592087624762421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54431919106394725083174947 81647878659592087624762421)
            ·
              refine ⟨7654488624336758214821477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81647878659592087624762421 7654488624336758214821477)
              ·
                refine ⟨1435216617063142165279027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7654488624336758214821477 1435216617063142165279027)
                ·
                  refine ⟨2152824925594713247918541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435216617063142165279027 2152824925594713247918541)
                  ·
                    refine ⟨807309347098017467969453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2152824925594713247918541 807309347098017467969453)
                    ·
                      rfl

theorem cell22_2358344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_2358344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358344 prefixEnd_2358344 := by exact prefixLift 2358344
  have htrace : WordTrace (prefixWord ++ tailWord_2358344) baseStart_2358344 baseEnd_2358344 := by
    simpa [prefixWord, tailWord_2358344, baseEnd_2358344] using wordTrace_append hprefix tailTrace_2358344
  have hstable : (prefixWord ++ tailWord_2358344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358344).length < 2 ^ (prefixWord ++ tailWord_2358344).sum := by decide
  have hdescent : baseEnd_2358344 < baseStart_2358344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358400 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_2358400 : Nat := 118140960795 + 2358400 * 2 ^ 59
def prefixEnd_2358400 : Nat := 4983230072969 + 3 ^ 40 * 2358400 * 2
def baseEnd_2358400 : Nat := 807328517042451988569281

theorem tailTrace_2358400 : CollatzResearch.WordTrace tailWord_2358400 prefixEnd_2358400 807328517042451988569281 := by
  unfold tailWord_2358400
  simp only [CollatzResearch.WordTrace]
  refine ⟨43008957327963528748972327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57345276437284704998629769 43008957327963528748972327)
  ·
    refine ⟨64513435991945293123458491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43008957327963528748972327 64513435991945293123458491)
    ·
      refine ⟨96770153987917939685187737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64513435991945293123458491 96770153987917939685187737)
      ·
        refine ⟨72577615490938454763890803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96770153987917939685187737 72577615490938454763890803)
        ·
          refine ⟨108866423236407682145836205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72577615490938454763890803 108866423236407682145836205)
          ·
            refine ⟨40824908713652880804688577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108866423236407682145836205 40824908713652880804688577)
            ·
              refine ⟨30618681535239660603516433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40824908713652880804688577 30618681535239660603516433)
              ·
                refine ⟨22964011151429745452637325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30618681535239660603516433 22964011151429745452637325)
                ·
                  refine ⟨8611504181786154544738997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22964011151429745452637325 8611504181786154544738997)
                  ·
                    refine ⟨807328517042451988569281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8611504181786154544738997 807328517042451988569281)
                    ·
                      rfl

theorem cell22_2358400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_2358400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358400 prefixEnd_2358400 := by exact prefixLift 2358400
  have htrace : WordTrace (prefixWord ++ tailWord_2358400) baseStart_2358400 baseEnd_2358400 := by
    simpa [prefixWord, tailWord_2358400, baseEnd_2358400] using wordTrace_append hprefix tailTrace_2358400
  have hstable : (prefixWord ++ tailWord_2358400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358400).length < 2 ^ (prefixWord ++ tailWord_2358400).sum := by decide
  have hdescent : baseEnd_2358400 < baseStart_2358400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358432 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 2, 4]
def baseStart_2358432 : Nat := 118140960795 + 2358432 * 2 ^ 59
def prefixEnd_2358432 : Nat := 4983230072969 + 3 ^ 40 * 2358432 * 2
def baseEnd_2358432 : Nat := 807339471296414571769183

theorem tailTrace_2358432 : CollatzResearch.WordTrace tailWord_2358432 prefixEnd_2358432 807339471296414571769183 := by
  unfold tailWord_2358432
  simp only [CollatzResearch.WordTrace]
  refine ⟨43009540895905563481554775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57346054527874084642073033 43009540895905563481554775)
  ·
    refine ⟨64514311343858345222332163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43009540895905563481554775 64514311343858345222332163)
    ·
      refine ⟨96771467015787517833498245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64514311343858345222332163 96771467015787517833498245)
      ·
        refine ⟨18144650065460159593780921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96771467015787517833498245 18144650065460159593780921)
        ·
          refine ⟨13608487549095119695335691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18144650065460159593780921 13608487549095119695335691)
          ·
            refine ⟨20412731323642679543003537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13608487549095119695335691 20412731323642679543003537)
            ·
              refine ⟨15309548492732009657252653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20412731323642679543003537 15309548492732009657252653)
              ·
                refine ⟨5741080684774503621469745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15309548492732009657252653 5741080684774503621469745)
                ·
                  refine ⟨4305810513580877716102309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5741080684774503621469745 4305810513580877716102309)
                  ·
                    refine ⟨807339471296414571769183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4305810513580877716102309 807339471296414571769183)
                    ·
                      rfl

theorem cell22_2358432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_2358432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358432 prefixEnd_2358432 := by exact prefixLift 2358432
  have htrace : WordTrace (prefixWord ++ tailWord_2358432) baseStart_2358432 baseEnd_2358432 := by
    simpa [prefixWord, tailWord_2358432, baseEnd_2358432] using wordTrace_append hprefix tailTrace_2358432
  have hstable : (prefixWord ++ tailWord_2358432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358432).length < 2 ^ (prefixWord ++ tailWord_2358432).sum := by decide
  have hdescent : baseEnd_2358432 < baseStart_2358432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358436 : List Nat := [2, 3, 1, 2, 3, 3, 1, 3, 4]
def baseStart_2358436 : Nat := 118140960795 + 2358436 * 2 ^ 59
def prefixEnd_2358436 : Nat := 4983230072969 + 3 ^ 40 * 2358436 * 2
def baseEnd_2358436 : Nat := 269113613526053298223057

theorem tailTrace_2358436 : CollatzResearch.WordTrace tailWord_2358436 prefixEnd_2358436 269113613526053298223057 := by
  unfold tailWord_2358436
  simp only [CollatzResearch.WordTrace]
  refine ⟨43009613841898317823127581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57346151789197757097503441 43009613841898317823127581)
  ·
    refine ⟨16128605190711869183672843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43009613841898317823127581 16128605190711869183672843)
    ·
      refine ⟨24192907786067803775509265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16128605190711869183672843 24192907786067803775509265)
      ·
        refine ⟨18144680839550852831631949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24192907786067803775509265 18144680839550852831631949)
        ·
          refine ⟨6804255314831569811861981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18144680839550852831631949 6804255314831569811861981)
          ·
            refine ⟨2551595743061838679448243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6804255314831569811861981 2551595743061838679448243)
            ·
              refine ⟨3827393614592758019172365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2551595743061838679448243 3827393614592758019172365)
              ·
                refine ⟨1435272605472284257189637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3827393614592758019172365 1435272605472284257189637)
                ·
                  refine ⟨269113613526053298223057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435272605472284257189637 269113613526053298223057)
                  ·
                    rfl

theorem cell22_2358436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_2358436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358436 prefixEnd_2358436 := by exact prefixLift 2358436
  have htrace : WordTrace (prefixWord ++ tailWord_2358436) baseStart_2358436 baseEnd_2358436 := by
    simpa [prefixWord, tailWord_2358436, baseEnd_2358436] using wordTrace_append hprefix tailTrace_2358436
  have hstable : (prefixWord ++ tailWord_2358436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358436).length < 2 ^ (prefixWord ++ tailWord_2358436).sum := by decide
  have hdescent : baseEnd_2358436 < baseStart_2358436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358449 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 2, 4]
def baseStart_2358449 : Nat := 118140960795 + 2358449 * 2 ^ 59
def prefixEnd_2358449 : Nat := 4983230072969 + 3 ^ 40 * 2358449 * 2
def baseEnd_2358449 : Nat := 807345290743832194094131

theorem tailTrace_2358449 : CollatzResearch.WordTrace tailWord_2358449 prefixEnd_2358449 807345290743832194094131 := by
  unfold tailWord_2358449
  simp only [CollatzResearch.WordTrace]
  refine ⟨86019701832749538866478401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57346467888499692577652267 86019701832749538866478401)
  ·
    refine ⟨64514776374562154149858801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86019701832749538866478401 64514776374562154149858801)
    ·
      refine ⟨48386082280921615612394101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64514776374562154149858801 48386082280921615612394101)
      ·
        refine ⟨4536195213836401463661947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48386082280921615612394101 4536195213836401463661947)
        ·
          refine ⟨6804292820754602195492921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4536195213836401463661947 6804292820754602195492921)
          ·
            refine ⟨5103219615565951646619691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6804292820754602195492921 5103219615565951646619691)
            ·
              refine ⟨7654829423348927469929537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5103219615565951646619691 7654829423348927469929537)
              ·
                refine ⟨5741122067511695602447153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7654829423348927469929537 5741122067511695602447153)
                ·
                  refine ⟨4305841550633771701835365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5741122067511695602447153 4305841550633771701835365)
                  ·
                    refine ⟨807345290743832194094131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4305841550633771701835365 807345290743832194094131)
                    ·
                      rfl

theorem cell22_2358449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_2358449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358449 prefixEnd_2358449 := by exact prefixLift 2358449
  have htrace : WordTrace (prefixWord ++ tailWord_2358449) baseStart_2358449 baseEnd_2358449 := by
    simpa [prefixWord, tailWord_2358449, baseEnd_2358449] using wordTrace_append hprefix tailTrace_2358449
  have hstable : (prefixWord ++ tailWord_2358449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358449).length < 2 ^ (prefixWord ++ tailWord_2358449).sum := by decide
  have hdescent : baseEnd_2358449 < baseStart_2358449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358475 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 9]
def baseStart_2358475 : Nat := 118140960795 + 2358475 * 2 ^ 59
def prefixEnd_2358475 : Nat := 4983230072969 + 3 ^ 40 * 2358475 * 2
def baseEnd_2358475 : Nat := 269118063691725597648017

theorem tailTrace_2358475 : CollatzResearch.WordTrace tailWord_2358475 prefixEnd_2358475 269118063691725597648017 := by
  unfold tailWord_2358475
  simp only [CollatzResearch.WordTrace]
  refine ⟨86020650130655345306924879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57347100087103563537949919 86020650130655345306924879)
  ·
    refine ⟨129030975195983017960387319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86020650130655345306924879 129030975195983017960387319)
    ·
      refine ⟨193546462793974526940580979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129030975195983017960387319 193546462793974526940580979)
      ·
        refine ⟨290319694190961790410871469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193546462793974526940580979 290319694190961790410871469)
        ·
          refine ⟨108869885321610671404076801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290319694190961790410871469 108869885321610671404076801)
          ·
            refine ⟨81652413991208003553057601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108869885321610671404076801 81652413991208003553057601)
            ·
              refine ⟨61239310493406002664793201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81652413991208003553057601 61239310493406002664793201)
              ·
                refine ⟨45929482870054501998594901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61239310493406002664793201 45929482870054501998594901)
                ·
                  refine ⟨269118063691725597648017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45929482870054501998594901 269118063691725597648017)
                  ·
                    rfl

theorem cell22_2358475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 9].length) (baseStart_2358475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358475 prefixEnd_2358475 := by exact prefixLift 2358475
  have htrace : WordTrace (prefixWord ++ tailWord_2358475) baseStart_2358475 baseEnd_2358475 := by
    simpa [prefixWord, tailWord_2358475, baseEnd_2358475] using wordTrace_append hprefix tailTrace_2358475
  have hstable : (prefixWord ++ tailWord_2358475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358475).length < 2 ^ (prefixWord ++ tailWord_2358475).sum := by decide
  have hdescent : baseEnd_2358475 < baseStart_2358475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358509 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 5]
def baseStart_2358509 : Nat := 118140960795 + 2358509 * 2 ^ 59
def prefixEnd_2358509 : Nat := 4983230072969 + 3 ^ 40 * 2358509 * 2
def baseEnd_2358509 : Nat := 269121943323337345864649

theorem tailTrace_2358509 : CollatzResearch.WordTrace tailWord_2358509 prefixEnd_2358509 269121943323337345864649 := by
  unfold tailWord_2358509
  simp only [CollatzResearch.WordTrace]
  refine ⟨86021890212532169113662581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57347926808354779409108387 86021890212532169113662581)
  ·
    refine ⟨8064552207424890854405867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86021890212532169113662581 8064552207424890854405867)
    ·
      refine ⟨12096828311137336281608801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8064552207424890854405867 12096828311137336281608801)
      ·
        refine ⟨9072621233353002211206601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12096828311137336281608801 9072621233353002211206601)
        ·
          refine ⟨6804465925014751658404951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9072621233353002211206601 6804465925014751658404951)
          ·
            refine ⟨10206698887522127487607427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6804465925014751658404951 10206698887522127487607427)
            ·
              refine ⟨15310048331283191231411141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10206698887522127487607427 15310048331283191231411141)
              ·
                refine ⟨2870634062115598355889589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15310048331283191231411141 2870634062115598355889589)
                ·
                  refine ⟨269121943323337345864649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2870634062115598355889589 269121943323337345864649)
                  ·
                    rfl

theorem cell22_2358509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2358509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358509 prefixEnd_2358509 := by exact prefixLift 2358509
  have htrace : WordTrace (prefixWord ++ tailWord_2358509) baseStart_2358509 baseEnd_2358509 := by
    simpa [prefixWord, tailWord_2358509, baseEnd_2358509] using wordTrace_append hprefix tailTrace_2358509
  have hstable : (prefixWord ++ tailWord_2358509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358509).length < 2 ^ (prefixWord ++ tailWord_2358509).sum := by decide
  have hdescent : baseEnd_2358509 < baseStart_2358509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358522 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_2358522 : Nat := 118140960795 + 2358522 * 2 ^ 59
def prefixEnd_2358522 : Nat := 4983230072969 + 3 ^ 40 * 2358522 * 2
def baseEnd_2358522 : Nat := 807370280135684337018907

theorem tailTrace_2358522 : CollatzResearch.WordTrace tailWord_2358522 prefixEnd_2358522 807370280135684337018907 := by
  unfold tailWord_2358522
  simp only [CollatzResearch.WordTrace]
  refine ⟨21505591090371268083471455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57348242907656714889257213 21505591090371268083471455)
  ·
    refine ⟨32258386635556902125207183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21505591090371268083471455 32258386635556902125207183)
    ·
      refine ⟨48387579953335353187810775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32258386635556902125207183 48387579953335353187810775)
      ·
        refine ⟨72581369930003029781716163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48387579953335353187810775 72581369930003029781716163)
        ·
          refine ⟨108872054895004544672574245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72581369930003029781716163 108872054895004544672574245)
          ·
            refine ⟨20413510292813352126107671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108872054895004544672574245 20413510292813352126107671)
            ·
              refine ⟨30620265439220028189161507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20413510292813352126107671 30620265439220028189161507)
              ·
                refine ⟨45930398158830042283742261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30620265439220028189161507 45930398158830042283742261)
                ·
                  refine ⟨4305974827390316464100837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45930398158830042283742261 4305974827390316464100837)
                  ·
                    refine ⟨807370280135684337018907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4305974827390316464100837 807370280135684337018907)
                    ·
                      rfl

theorem cell22_2358522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_2358522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358522 prefixEnd_2358522 := by exact prefixLift 2358522
  have htrace : WordTrace (prefixWord ++ tailWord_2358522) baseStart_2358522 baseEnd_2358522 := by
    simpa [prefixWord, tailWord_2358522, baseEnd_2358522] using wordTrace_append hprefix tailTrace_2358522
  have hstable : (prefixWord ++ tailWord_2358522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358522).length < 2 ^ (prefixWord ++ tailWord_2358522).sum := by decide
  have hdescent : baseEnd_2358522 < baseStart_2358522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358524 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 2, 5]
def baseStart_2358524 : Nat := 118140960795 + 2358524 * 2 ^ 59
def prefixEnd_2358524 : Nat := 4983230072969 + 3 ^ 40 * 2358524 * 2
def baseEnd_2358524 : Nat := 807370964776556998468901

theorem tailTrace_2358524 : CollatzResearch.WordTrace tailWord_2358524 prefixEnd_2358524 807370964776556998468901 := by
  unfold tailWord_2358524
  simp only [CollatzResearch.WordTrace]
  refine ⟨43011218653738913337729313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57348291538318551116972417 43011218653738913337729313)
  ·
    refine ⟨32258413990304185003296985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43011218653738913337729313 32258413990304185003296985)
    ·
      refine ⟨24193810492728138752472739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32258413990304185003296985 24193810492728138752472739)
      ·
        refine ⟨36290715739092208128709109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24193810492728138752472739 36290715739092208128709109)
        ·
          refine ⟨3402254600539894512066479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36290715739092208128709109 3402254600539894512066479)
          ·
            refine ⟨5103381900809841768099719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3402254600539894512066479 5103381900809841768099719)
            ·
              refine ⟨7655072851214762652149579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5103381900809841768099719 7655072851214762652149579)
              ·
                refine ⟨11482609276822143978224369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7655072851214762652149579 11482609276822143978224369)
                ·
                  refine ⟨8611956957616607983668277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11482609276822143978224369 8611956957616607983668277)
                  ·
                    refine ⟨807370964776556998468901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8611956957616607983668277 807370964776556998468901)
                    ·
                      rfl

theorem cell22_2358524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_2358524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358524 prefixEnd_2358524 := by exact prefixLift 2358524
  have htrace : WordTrace (prefixWord ++ tailWord_2358524) baseStart_2358524 baseEnd_2358524 := by
    simpa [prefixWord, tailWord_2358524, baseEnd_2358524] using wordTrace_append hprefix tailTrace_2358524
  have hstable : (prefixWord ++ tailWord_2358524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358524).length < 2 ^ (prefixWord ++ tailWord_2358524).sum := by decide
  have hdescent : baseEnd_2358524 < baseStart_2358524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358537 : List Nat := [1, 2, 1, 1, 3, 3, 3, 2, 6]
def baseStart_2358537 : Nat := 118140960795 + 2358537 * 2 ^ 59
def prefixEnd_2358537 : Nat := 4983230072969 + 3 ^ 40 * 2358537 * 2
def baseEnd_2358537 : Nat := 269125138314076432631287

theorem tailTrace_2358537 : CollatzResearch.WordTrace tailWord_2358537 prefixEnd_2358537 269125138314076432631287 := by
  unfold tailWord_2358537
  simp only [CollatzResearch.WordTrace]
  refine ⟨86022911456430729895681865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57348607637620486597121243 86022911456430729895681865)
  ·
    refine ⟨64517183592323047421761399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86022911456430729895681865 64517183592323047421761399)
    ·
      refine ⟨96775775388484571132642099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64517183592323047421761399 96775775388484571132642099)
      ·
        refine ⟨145163663082726856698963149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96775775388484571132642099 145163663082726856698963149)
        ·
          refine ⟨54436373656022571262111181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145163663082726856698963149 54436373656022571262111181)
          ·
            refine ⟨20413640121008464223291693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54436373656022571262111181 20413640121008464223291693)
            ·
              refine ⟨7655115045378174083734385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20413640121008464223291693 7655115045378174083734385)
              ·
                refine ⟨5741336284033630562800789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7655115045378174083734385 5741336284033630562800789)
                ·
                  refine ⟨269125138314076432631287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5741336284033630562800789 269125138314076432631287)
                  ·
                    rfl

theorem cell22_2358537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_2358537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358537 prefixEnd_2358537 := by exact prefixLift 2358537
  have htrace : WordTrace (prefixWord ++ tailWord_2358537) baseStart_2358537 baseEnd_2358537 := by
    simpa [prefixWord, tailWord_2358537, baseEnd_2358537] using wordTrace_append hprefix tailTrace_2358537
  have hstable : (prefixWord ++ tailWord_2358537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358537).length < 2 ^ (prefixWord ++ tailWord_2358537).sum := by decide
  have hdescent : baseEnd_2358537 < baseStart_2358537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358556 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 1, 4]
def baseStart_2358556 : Nat := 118140960795 + 2358556 * 2 ^ 59
def prefixEnd_2358556 : Nat := 4983230072969 + 3 ^ 40 * 2358556 * 2
def baseEnd_2358556 : Nat := 807381919030519581668803

theorem tailTrace_2358556 : CollatzResearch.WordTrace tailWord_2358556 prefixEnd_2358556 807381919030519581668803 := by
  unfold tailWord_2358556
  simp only [CollatzResearch.WordTrace]
  refine ⟨43011802221680948070311761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57349069628907930760415681 43011802221680948070311761)
  ·
    refine ⟨32258851666260711052733821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43011802221680948070311761 32258851666260711052733821)
    ·
      refine ⟨12097069374847766644775183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32258851666260711052733821 12097069374847766644775183)
      ·
        refine ⟨18145604062271649967162775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12097069374847766644775183 18145604062271649967162775)
        ·
          refine ⟨27218406093407474950744163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18145604062271649967162775 27218406093407474950744163)
          ·
            refine ⟨40827609140111212426116245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27218406093407474950744163 40827609140111212426116245)
            ·
              refine ⟨1913794178442713082474199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40827609140111212426116245 1913794178442713082474199)
              ·
                refine ⟨2870691267664069623711299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913794178442713082474199 2870691267664069623711299)
                ·
                  refine ⟨4306036901496104435566949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2870691267664069623711299 4306036901496104435566949)
                  ·
                    refine ⟨807381919030519581668803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4306036901496104435566949 807381919030519581668803)
                    ·
                      rfl

theorem cell22_2358556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_2358556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358556 prefixEnd_2358556 := by exact prefixLift 2358556
  have htrace : WordTrace (prefixWord ++ tailWord_2358556) baseStart_2358556 baseEnd_2358556 := by
    simpa [prefixWord, tailWord_2358556, baseEnd_2358556] using wordTrace_append hprefix tailTrace_2358556
  have hstable : (prefixWord ++ tailWord_2358556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358556).length < 2 ^ (prefixWord ++ tailWord_2358556).sum := by decide
  have hdescent : baseEnd_2358556 < baseStart_2358556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358599 : List Nat := [1, 1, 4, 1, 2, 3, 4, 6]
def baseStart_2358599 : Nat := 118140960795 + 2358599 * 2 ^ 59
def prefixEnd_2358599 : Nat := 4983230072969 + 3 ^ 40 * 2358599 * 2
def baseEnd_2358599 : Nat := 89710737645475755871519

theorem tailTrace_2358599 : CollatzResearch.WordTrace tailWord_2358599 prefixEnd_2358599 89710737645475755871519 := by
  unfold tailWord_2358599
  simp only [CollatzResearch.WordTrace]
  refine ⟨86025172782206114484438851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57350115188137409656292567 86025172782206114484438851)
  ·
    refine ⟨129037759173309171726658277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86025172782206114484438851 129037759173309171726658277)
    ·
      refine ⟨24194579844995469698748427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129037759173309171726658277 24194579844995469698748427)
      ·
        refine ⟨36291869767493204548122641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24194579844995469698748427 36291869767493204548122641)
        ·
          refine ⟨27218902325619903411091981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36291869767493204548122641 27218902325619903411091981)
          ·
            refine ⟨10207088372107463779159493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27218902325619903411091981 10207088372107463779159493)
            ·
              refine ⟨1913829069770149458592405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10207088372107463779159493 1913829069770149458592405)
              ·
                refine ⟨89710737645475755871519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1913829069770149458592405 89710737645475755871519)
                ·
                  rfl

theorem cell22_2358599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 6].length) (baseStart_2358599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358599 prefixEnd_2358599 := by exact prefixLift 2358599
  have htrace : WordTrace (prefixWord ++ tailWord_2358599) baseStart_2358599 baseEnd_2358599 := by
    simpa [prefixWord, tailWord_2358599, baseEnd_2358599] using wordTrace_append hprefix tailTrace_2358599
  have hstable : (prefixWord ++ tailWord_2358599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358599).length < 2 ^ (prefixWord ++ tailWord_2358599).sum := by decide
  have hdescent : baseEnd_2358599 < baseStart_2358599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358755 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 2, 3]
def baseStart_2358755 : Nat := 118140960795 + 2358755 * 2 ^ 59
def prefixEnd_2358755 : Nat := 4983230072969 + 3 ^ 40 * 2358755 * 2
def baseEnd_2358755 : Nat := 807450040797349395943193

theorem tailTrace_2358755 : CollatzResearch.WordTrace tailWord_2358755 prefixEnd_2358755 807450040797349395943193 := by
  unfold tailWord_2358755
  simp only [CollatzResearch.WordTrace]
  refine ⟨86030862569640953127117719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57353908379760635418078479 86030862569640953127117719)
  ·
    refine ⟨129046293854461429690676579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86030862569640953127117719 129046293854461429690676579)
    ·
      refine ⟨193569440781692144536014869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129046293854461429690676579 193569440781692144536014869)
      ·
        refine ⟨9073567536641819275125697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 193569440781692144536014869 9073567536641819275125697)
        ·
          refine ⟨6805175652481364456344273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9073567536641819275125697 6805175652481364456344273)
          ·
            refine ⟨5103881739361023342258205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6805175652481364456344273 5103881739361023342258205)
            ·
              refine ⟨1913955652260383753346827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5103881739361023342258205 1913955652260383753346827)
              ·
                refine ⟨2870933478390575630020241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1913955652260383753346827 2870933478390575630020241)
                ·
                  refine ⟨2153200108792931722515181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2870933478390575630020241 2153200108792931722515181)
                  ·
                    refine ⟨807450040797349395943193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2153200108792931722515181 807450040797349395943193)
                    ·
                      rfl

theorem cell22_2358755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 2, 3].length) (baseStart_2358755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358755 prefixEnd_2358755 := by exact prefixLift 2358755
  have htrace : WordTrace (prefixWord ++ tailWord_2358755) baseStart_2358755 baseEnd_2358755 := by
    simpa [prefixWord, tailWord_2358755, baseEnd_2358755] using wordTrace_append hprefix tailTrace_2358755
  have hstable : (prefixWord ++ tailWord_2358755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358755).length < 2 ^ (prefixWord ++ tailWord_2358755).sum := by decide
  have hdescent : baseEnd_2358755 < baseStart_2358755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358783 : List Nat := [1, 1, 2, 2, 1, 2, 2, 7, 1, 3]
def baseStart_2358783 : Nat := 118140960795 + 2358783 * 2 ^ 59
def prefixEnd_2358783 : Nat := 4983230072969 + 3 ^ 40 * 2358783 * 2
def baseEnd_2358783 : Nat := 807459625769566656243107

theorem tailTrace_2358783 : CollatzResearch.WordTrace tailWord_2358783 prefixEnd_2358783 807459625769566656243107 := by
  unfold tailWord_2358783
  simp only [CollatzResearch.WordTrace]
  refine ⟨86031883813539513909137003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57354589209026342606091335 86031883813539513909137003)
  ·
    refine ⟨129047825720309270863705505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86031883813539513909137003 129047825720309270863705505)
    ·
      refine ⟨96785869290231953147779129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129047825720309270863705505 96785869290231953147779129)
      ·
        refine ⟨72589401967673964860834347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96785869290231953147779129 72589401967673964860834347)
        ·
          refine ⟨108884102951510947291251521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72589401967673964860834347 108884102951510947291251521)
          ·
            refine ⟨81663077213633210468438641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108884102951510947291251521 81663077213633210468438641)
            ·
              refine ⟨61247307910224907851328981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81663077213633210468438641 61247307910224907851328981)
              ·
                refine ⟨1435483779145896277765523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 61247307910224907851328981 1435483779145896277765523)
                ·
                  refine ⟨2153225668718844416648285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1435483779145896277765523 2153225668718844416648285)
                  ·
                    refine ⟨807459625769566656243107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2153225668718844416648285 807459625769566656243107)
                    ·
                      rfl

theorem cell22_2358783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 1, 3].length) (baseStart_2358783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358783 prefixEnd_2358783 := by exact prefixLift 2358783
  have htrace : WordTrace (prefixWord ++ tailWord_2358783) baseStart_2358783 baseEnd_2358783 := by
    simpa [prefixWord, tailWord_2358783, baseEnd_2358783] using wordTrace_append hprefix tailTrace_2358783
  have hstable : (prefixWord ++ tailWord_2358783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358783).length < 2 ^ (prefixWord ++ tailWord_2358783).sum := by decide
  have hdescent : baseEnd_2358783 < baseStart_2358783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358858 : List Nat := [3, 1, 2, 1, 1, 3, 3, 4, 4]
def baseStart_2358858 : Nat := 118140960795 + 2358858 * 2 ^ 59
def prefixEnd_2358858 : Nat := 4983230072969 + 3 ^ 40 * 2358858 * 2
def baseEnd_2358858 : Nat := 269161766600763820205959

theorem tailTrace_2358858 : CollatzResearch.WordTrace tailWord_2358858 prefixEnd_2358858 269161766600763820205959 := by
  unfold tailWord_2358858
  simp only [CollatzResearch.WordTrace]
  refine ⟨21508654822066950429529307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57356412858845201145411485 21508654822066950429529307)
  ·
    refine ⟨32262982233100425644293961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21508654822066950429529307 32262982233100425644293961)
    ·
      refine ⟨24197236674825319233220471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32262982233100425644293961 24197236674825319233220471)
      ·
        refine ⟨36295855012237978849830707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24197236674825319233220471 36295855012237978849830707)
        ·
          refine ⟨54443782518356968274746061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36295855012237978849830707 54443782518356968274746061)
          ·
            refine ⟨20416418444383863103029773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54443782518356968274746061 20416418444383863103029773)
            ·
              refine ⟨7656156916643948663636165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20416418444383863103029773 7656156916643948663636165)
              ·
                refine ⟨1435529421870740374431781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7656156916643948663636165 1435529421870740374431781)
                ·
                  refine ⟨269161766600763820205959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435529421870740374431781 269161766600763820205959)
                  ·
                    rfl

theorem cell22_2358858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_2358858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358858 prefixEnd_2358858 := by exact prefixLift 2358858
  have htrace : WordTrace (prefixWord ++ tailWord_2358858) baseStart_2358858 baseEnd_2358858 := by
    simpa [prefixWord, tailWord_2358858, baseEnd_2358858] using wordTrace_append hprefix tailTrace_2358858
  have hstable : (prefixWord ++ tailWord_2358858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358858).length < 2 ^ (prefixWord ++ tailWord_2358858).sum := by decide
  have hdescent : baseEnd_2358858 < baseStart_2358858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358888 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 1, 6]
def baseStart_2358888 : Nat := 118140960795 + 2358888 * 2 ^ 59
def prefixEnd_2358888 : Nat := 4983230072969 + 3 ^ 40 * 2358888 * 2
def baseEnd_2358888 : Nat := 807495569415381382367785

theorem tailTrace_2358888 : CollatzResearch.WordTrace tailWord_2358888 prefixEnd_2358888 807495569415381382367785 := by
  unfold tailWord_2358888
  simp only [CollatzResearch.WordTrace]
  refine ⟨43017856739079558420854659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57357142318772744561139545 43017856739079558420854659)
  ·
    refine ⟨64526785108619337631281989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43017856739079558420854659 64526785108619337631281989)
    ·
      refine ⟨12098772207866125805865373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64526785108619337631281989 12098772207866125805865373)
      ·
        refine ⟨4537039577949797177199515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12098772207866125805865373 4537039577949797177199515)
        ·
          refine ⟨6805559366924695765799273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4537039577949797177199515 6805559366924695765799273)
          ·
            refine ⟨5104169525193521824349455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6805559366924695765799273 5104169525193521824349455)
            ·
              refine ⟨7656254287790282736524183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5104169525193521824349455 7656254287790282736524183)
              ·
                refine ⟨11484381431685424104786275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7656254287790282736524183 11484381431685424104786275)
                ·
                  refine ⟨17226572147528136157179413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11484381431685424104786275 17226572147528136157179413)
                  ·
                    refine ⟨807495569415381382367785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17226572147528136157179413 807495569415381382367785)
                    ·
                      rfl

theorem cell22_2358888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_2358888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358888 prefixEnd_2358888 := by exact prefixLift 2358888
  have htrace : WordTrace (prefixWord ++ tailWord_2358888) baseStart_2358888 baseEnd_2358888 := by
    simpa [prefixWord, tailWord_2358888, baseEnd_2358888] using wordTrace_append hprefix tailTrace_2358888
  have hstable : (prefixWord ++ tailWord_2358888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358888).length < 2 ^ (prefixWord ++ tailWord_2358888).sum := by decide
  have hdescent : baseEnd_2358888 < baseStart_2358888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358894 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_2358894 : Nat := 118140960795 + 2358894 * 2 ^ 59
def prefixEnd_2358894 : Nat := 4983230072969 + 3 ^ 40 * 2358894 * 2
def baseEnd_2358894 : Nat := 807497623337999366717767

theorem tailTrace_2358894 : CollatzResearch.WordTrace tailWord_2358894 prefixEnd_2358894 807497623337999366717767 := by
  unfold tailWord_2358894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10754491539517172483303467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57357288210758253244285157 10754491539517172483303467)
  ·
    refine ⟨16131737309275758724955201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10754491539517172483303467 16131737309275758724955201)
    ·
      refine ⟨12098802981956819043716401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16131737309275758724955201 12098802981956819043716401)
      ·
        refine ⟨9074102236467614282787301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12098802981956819043716401 9074102236467614282787301)
        ·
          refine ⟨1701394169337677678022619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9074102236467614282787301 1701394169337677678022619)
          ·
            refine ⟨2552091254006516517033929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701394169337677678022619 2552091254006516517033929)
            ·
              refine ⟨1914068440504887387775447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552091254006516517033929 1914068440504887387775447)
              ·
                refine ⟨2871102660757331081663171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914068440504887387775447 2871102660757331081663171)
                ·
                  refine ⟨4306653991135996622494757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871102660757331081663171 4306653991135996622494757)
                  ·
                    refine ⟨807497623337999366717767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4306653991135996622494757 807497623337999366717767)
                    ·
                      rfl

theorem cell22_2358894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_2358894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358894 prefixEnd_2358894 := by exact prefixLift 2358894
  have htrace : WordTrace (prefixWord ++ tailWord_2358894) baseStart_2358894 baseEnd_2358894 := by
    simpa [prefixWord, tailWord_2358894, baseEnd_2358894] using wordTrace_append hprefix tailTrace_2358894
  have hstable : (prefixWord ++ tailWord_2358894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358894).length < 2 ^ (prefixWord ++ tailWord_2358894).sum := by decide
  have hdescent : baseEnd_2358894 < baseStart_2358894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2358991 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 5, 5]
def baseStart_2358991 : Nat := 118140960795 + 2358991 * 2 ^ 59
def prefixEnd_2358991 : Nat := 4983230072969 + 3 ^ 40 * 2358991 * 2
def baseEnd_2358991 : Nat := 807530828420323447042469

theorem tailTrace_2358991 : CollatzResearch.WordTrace tailWord_2358991 prefixEnd_2358991 807530828420323447042469 := by
  unfold tailWord_2358991
  simp only [CollatzResearch.WordTrace]
  refine ⟨86039470196785965432708827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57359646797857310288472551 86039470196785965432708827)
  ·
    refine ⟨129059205295178948149063241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86039470196785965432708827 129059205295178948149063241)
    ·
      refine ⟨96794403971384211111797431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129059205295178948149063241 96794403971384211111797431)
      ·
        refine ⟨145191605957076316667696147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96794403971384211111797431 145191605957076316667696147)
        ·
          refine ⟨217787408935614475001544221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145191605957076316667696147 217787408935614475001544221)
          ·
            refine ⟨81670278350855428125579083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217787408935614475001544221 81670278350855428125579083)
            ·
              refine ⟨122505417526283142188368625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81670278350855428125579083 122505417526283142188368625)
              ·
                refine ⟨91879063144712356641276469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122505417526283142188368625 91879063144712356641276469)
                ·
                  refine ⟨8613662169816783435119669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91879063144712356641276469 8613662169816783435119669)
                  ·
                    refine ⟨807530828420323447042469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8613662169816783435119669 807530828420323447042469)
                    ·
                      rfl

theorem cell22_2358991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_2358991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2358991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2358991 prefixEnd_2358991 := by exact prefixLift 2358991
  have htrace : WordTrace (prefixWord ++ tailWord_2358991) baseStart_2358991 baseEnd_2358991 := by
    simpa [prefixWord, tailWord_2358991, baseEnd_2358991] using wordTrace_append hprefix tailTrace_2358991
  have hstable : (prefixWord ++ tailWord_2358991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2358991).length < 2 ^ (prefixWord ++ tailWord_2358991).sum := by decide
  have hdescent : baseEnd_2358991 < baseStart_2358991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2358991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359008 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 6, 3]
def baseStart_2359008 : Nat := 118140960795 + 2359008 * 2 ^ 59
def prefixEnd_2359008 : Nat := 4983230072969 + 3 ^ 40 * 2359008 * 2
def baseEnd_2359008 : Nat := 807536647867741069367417

theorem tailTrace_2359008 : CollatzResearch.WordTrace tailWord_2359008 prefixEnd_2359008 807536647867741069367417 := by
  unfold tailWord_2359008
  simp only [CollatzResearch.WordTrace]
  refine ⟨43020045118862188668038839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57360060158482918224051785 43020045118862188668038839)
  ·
    refine ⟨64530067678293283002058259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43020045118862188668038839 64530067678293283002058259)
    ·
      refine ⟨96795101517439924503087389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64530067678293283002058259 96795101517439924503087389)
      ·
        refine ⟨36298163069039971688657771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96795101517439924503087389 36298163069039971688657771)
        ·
          refine ⟨54447244603559957532986657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36298163069039971688657771 54447244603559957532986657)
          ·
            refine ⟨40835433452669968149739993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54447244603559957532986657 40835433452669968149739993)
            ·
              refine ⟨30626575089502476112304995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40835433452669968149739993 30626575089502476112304995)
              ·
                refine ⟨45939862634253714168457493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30626575089502476112304995 45939862634253714168457493)
                ·
                  refine ⟨2153431060980642851646445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45939862634253714168457493 2153431060980642851646445)
                  ·
                    refine ⟨807536647867741069367417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2153431060980642851646445 807536647867741069367417)
                    ·
                      rfl

theorem cell22_2359008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 6, 3].length) (baseStart_2359008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359008 prefixEnd_2359008 := by exact prefixLift 2359008
  have htrace : WordTrace (prefixWord ++ tailWord_2359008) baseStart_2359008 baseEnd_2359008 := by
    simpa [prefixWord, tailWord_2359008, baseEnd_2359008] using wordTrace_append hprefix tailTrace_2359008
  have hstable : (prefixWord ++ tailWord_2359008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359008).length < 2 ^ (prefixWord ++ tailWord_2359008).sum := by decide
  have hdescent : baseEnd_2359008 < baseStart_2359008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359023 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 2, 4]
def baseStart_2359023 : Nat := 118140960795 + 2359023 * 2 ^ 59
def prefixEnd_2359023 : Nat := 4983230072969 + 3 ^ 40 * 2359023 * 2
def baseEnd_2359023 : Nat := 807541782674286030242371

theorem tailTrace_2359023 : CollatzResearch.WordTrace tailWord_2359023 prefixEnd_2359023 807541782674286030242371 := by
  unfold tailWord_2359023
  simp only [CollatzResearch.WordTrace]
  refine ⟨86040637332670034897873723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57360424888446689931915815 86040637332670034897873723)
  ·
    refine ⟨129060955999005052346810585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86040637332670034897873723 129060955999005052346810585)
    ·
      refine ⟨96795716999253789260107939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129060955999005052346810585 96795716999253789260107939)
      ·
        refine ⟨145193575498880683890161909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96795716999253789260107939 145193575498880683890161909)
        ·
          refine ⟨13611897703020064114702679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145193575498880683890161909 13611897703020064114702679)
          ·
            refine ⟨20417846554530096172054019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13611897703020064114702679 20417846554530096172054019)
            ·
              refine ⟨30626769831795144258081029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20417846554530096172054019 30626769831795144258081029)
              ·
                refine ⟨5742519343461589548390193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30626769831795144258081029 5742519343461589548390193)
                ·
                  refine ⟨4306889507596192161292645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5742519343461589548390193 4306889507596192161292645)
                  ·
                    refine ⟨807541782674286030242371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4306889507596192161292645 807541782674286030242371)
                    ·
                      rfl

theorem cell22_2359023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_2359023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359023 prefixEnd_2359023 := by exact prefixLift 2359023
  have htrace : WordTrace (prefixWord ++ tailWord_2359023) baseStart_2359023 baseEnd_2359023 := by
    simpa [prefixWord, tailWord_2359023, baseEnd_2359023] using wordTrace_append hprefix tailTrace_2359023
  have hstable : (prefixWord ++ tailWord_2359023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359023).length < 2 ^ (prefixWord ++ tailWord_2359023).sum := by decide
  have hdescent : baseEnd_2359023 < baseStart_2359023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359025 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 2, 3]
def baseStart_2359025 : Nat := 118140960795 + 2359025 * 2 ^ 59
def prefixEnd_2359025 : Nat := 4983230072969 + 3 ^ 40 * 2359025 * 2
def baseEnd_2359025 : Nat := 807542467315158691692365

theorem tailTrace_2359025 : CollatzResearch.WordTrace tailWord_2359025 prefixEnd_2359025 807542467315158691692365 := by
  unfold tailWord_2359025
  simp only [CollatzResearch.WordTrace]
  refine ⟨86040710278662789239446529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57360473519108526159631019 86040710278662789239446529)
  ·
    refine ⟨64530532708997091929584897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86040710278662789239446529 64530532708997091929584897)
    ·
      refine ⟨48397899531747818947188673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64530532708997091929584897 48397899531747818947188673)
      ·
        refine ⟨36298424648810864210391505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48397899531747818947188673 36298424648810864210391505)
        ·
          refine ⟨27223818486608148157793629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36298424648810864210391505 27223818486608148157793629)
          ·
            refine ⟨10208931932478055559172611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27223818486608148157793629 10208931932478055559172611)
            ·
              refine ⟨15313397898717083338758917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10208931932478055559172611 15313397898717083338758917)
              ·
                refine ⟨2871262106009453126017297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15313397898717083338758917 2871262106009453126017297)
                ·
                  refine ⟨2153446579507089844512973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2871262106009453126017297 2153446579507089844512973)
                  ·
                    refine ⟨807542467315158691692365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2153446579507089844512973 807542467315158691692365)
                    ·
                      rfl

theorem cell22_2359025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_2359025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359025 prefixEnd_2359025 := by exact prefixLift 2359025
  have htrace : WordTrace (prefixWord ++ tailWord_2359025) baseStart_2359025 baseEnd_2359025 := by
    simpa [prefixWord, tailWord_2359025, baseEnd_2359025] using wordTrace_append hprefix tailTrace_2359025
  have hstable : (prefixWord ++ tailWord_2359025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359025).length < 2 ^ (prefixWord ++ tailWord_2359025).sum := by decide
  have hdescent : baseEnd_2359025 < baseStart_2359025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359042 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2359042 : Nat := 118140960795 + 2359042 * 2 ^ 59
def prefixEnd_2359042 : Nat := 4983230072969 + 3 ^ 40 * 2359042 * 2
def baseEnd_2359042 : Nat := 807548286762576314017313

theorem tailTrace_2359042 : CollatzResearch.WordTrace tailWord_2359042 prefixEnd_2359042 807548286762576314017313 := by
  unfold tailWord_2359042
  simp only [CollatzResearch.WordTrace]
  refine ⟨21510332579900300285703845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57360886879734134095210253 21510332579900300285703845)
  ·
    refine ⟨4033187358731306303569471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21510332579900300285703845 4033187358731306303569471)
    ·
      refine ⟨6049781038096959455354207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4033187358731306303569471 6049781038096959455354207)
      ·
        refine ⟨9074671557145439183031311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6049781038096959455354207 9074671557145439183031311)
        ·
          refine ⟨13612007335718158774546967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9074671557145439183031311 13612007335718158774546967)
          ·
            refine ⟨20418011003577238161820451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13612007335718158774546967 20418011003577238161820451)
            ·
              refine ⟨30627016505365857242730677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20418011003577238161820451 30627016505365857242730677)
              ·
                refine ⟨2871282797378049116506001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30627016505365857242730677 2871282797378049116506001)
                ·
                  refine ⟨2153462098033536837379501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2871282797378049116506001 2153462098033536837379501)
                  ·
                    refine ⟨807548286762576314017313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2153462098033536837379501 807548286762576314017313)
                    ·
                      rfl

theorem cell22_2359042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2359042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359042 prefixEnd_2359042 := by exact prefixLift 2359042
  have htrace : WordTrace (prefixWord ++ tailWord_2359042) baseStart_2359042 baseEnd_2359042 := by
    simpa [prefixWord, tailWord_2359042, baseEnd_2359042] using wordTrace_append hprefix tailTrace_2359042
  have hstable : (prefixWord ++ tailWord_2359042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359042).length < 2 ^ (prefixWord ++ tailWord_2359042).sum := by decide
  have hdescent : baseEnd_2359042 < baseStart_2359042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359130 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_2359130 : Nat := 118140960795 + 2359130 * 2 ^ 59
def prefixEnd_2359130 : Nat := 4983230072969 + 3 ^ 40 * 2359130 * 2
def baseEnd_2359130 : Nat := 807578410960973417817043

theorem tailTrace_2359130 : CollatzResearch.WordTrace tailWord_2359130 prefixEnd_2359130 807578410960973417817043 := by
  unfold tailWord_2359130
  simp only [CollatzResearch.WordTrace]
  refine ⟨21511134985820598043004711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57363026628854928114679229 21511134985820598043004711)
  ·
    refine ⟨32266702478730897064507067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21511134985820598043004711 32266702478730897064507067)
    ·
      refine ⟨48400053718096345596760601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32266702478730897064507067 48400053718096345596760601)
      ·
        refine ⟨36300040288572259197570451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48400053718096345596760601 36300040288572259197570451)
        ·
          refine ⟨54450060432858388796355677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36300040288572259197570451 54450060432858388796355677)
          ·
            refine ⟨20418772662321895798633379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54450060432858388796355677 20418772662321895798633379)
            ·
              refine ⟨30628158993482843697950069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20418772662321895798633379 30628158993482843697950069)
              ·
                refine ⟨2871389905639016596682819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30628158993482843697950069 2871389905639016596682819)
                ·
                  refine ⟨4307084858458524895024229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871389905639016596682819 4307084858458524895024229)
                  ·
                    refine ⟨807578410960973417817043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4307084858458524895024229 807578410960973417817043)
                    ·
                      rfl

theorem cell22_2359130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_2359130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359130 prefixEnd_2359130 := by exact prefixLift 2359130
  have htrace : WordTrace (prefixWord ++ tailWord_2359130) baseStart_2359130 baseEnd_2359130 := by
    simpa [prefixWord, tailWord_2359130, baseEnd_2359130] using wordTrace_append hprefix tailTrace_2359130
  have hstable : (prefixWord ++ tailWord_2359130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359130).length < 2 ^ (prefixWord ++ tailWord_2359130).sum := by decide
  have hdescent : baseEnd_2359130 < baseStart_2359130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359145 : List Nat := [1, 2, 1, 1, 1, 3, 1, 8, 4]
def baseStart_2359145 : Nat := 118140960795 + 2359145 * 2 ^ 59
def prefixEnd_2359145 : Nat := 4983230072969 + 3 ^ 40 * 2359145 * 2
def baseEnd_2359145 : Nat := 269194515255839459563999

theorem tailTrace_2359145 : CollatzResearch.WordTrace tailWord_2359145 prefixEnd_2359145 269194515255839459563999 := by
  unfold tailWord_2359145
  simp only [CollatzResearch.WordTrace]
  refine ⟨86045087038228049733814889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57363391358818699822543259 86045087038228049733814889)
  ·
    refine ⟨64533815278671037300361167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86045087038228049733814889 64533815278671037300361167)
    ·
      refine ⟨96800722918006555950541751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64533815278671037300361167 96800722918006555950541751)
      ·
        refine ⟨145201084377009833925812627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96800722918006555950541751 145201084377009833925812627)
        ·
          refine ⟨217801626565514750888718941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145201084377009833925812627 217801626565514750888718941)
          ·
            refine ⟨81675609962068031583269603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217801626565514750888718941 81675609962068031583269603)
            ·
              refine ⟨122513414943102047374904405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81675609962068031583269603 122513414943102047374904405)
              ·
                refine ⟨1435704081364477117674661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 122513414943102047374904405 1435704081364477117674661)
                ·
                  refine ⟨269194515255839459563999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435704081364477117674661 269194515255839459563999)
                  ·
                    rfl

theorem cell22_2359145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 8, 4].length) (baseStart_2359145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359145 prefixEnd_2359145 := by exact prefixLift 2359145
  have htrace : WordTrace (prefixWord ++ tailWord_2359145) baseStart_2359145 baseEnd_2359145 := by
    simpa [prefixWord, tailWord_2359145, baseEnd_2359145] using wordTrace_append hprefix tailTrace_2359145
  have hstable : (prefixWord ++ tailWord_2359145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359145).length < 2 ^ (prefixWord ++ tailWord_2359145).sum := by decide
  have hdescent : baseEnd_2359145 < baseStart_2359145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359173 : List Nat := [1, 3, 1, 1, 3, 2, 1, 10]
def baseStart_2359173 : Nat := 118140960795 + 2359173 * 2 ^ 59
def prefixEnd_2359173 : Nat := 4983230072969 + 3 ^ 40 * 2359173 * 2
def baseEnd_2359173 : Nat := 89732570082192848776879

theorem tailTrace_2359173 : CollatzResearch.WordTrace tailWord_2359173 prefixEnd_2359173 89732570082192848776879 := by
  unfold tailWord_2359173
  simp only [CollatzResearch.WordTrace]
  refine ⟨86046108282126610515834173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57364072188084407010556115 86046108282126610515834173)
  ·
    refine ⟨32267290605797478943437815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86046108282126610515834173 32267290605797478943437815)
    ·
      refine ⟨48400935908696218415156723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32267290605797478943437815 48400935908696218415156723)
      ·
        refine ⟨72601403863044327622735085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48400935908696218415156723 72601403863044327622735085)
        ·
          refine ⟨27225526448641622858525657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72601403863044327622735085 27225526448641622858525657)
          ·
            refine ⟨20419144836481217143894243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27225526448641622858525657 20419144836481217143894243)
            ·
              refine ⟨30628717254721825715841365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20419144836481217143894243 30628717254721825715841365)
              ·
                refine ⟨89732570082192848776879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30628717254721825715841365 89732570082192848776879)
                ·
                  rfl

theorem cell22_2359173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 10].length) (baseStart_2359173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359173 prefixEnd_2359173 := by exact prefixLift 2359173
  have htrace : WordTrace (prefixWord ++ tailWord_2359173) baseStart_2359173 baseEnd_2359173 := by
    simpa [prefixWord, tailWord_2359173, baseEnd_2359173] using wordTrace_append hprefix tailTrace_2359173
  have hstable : (prefixWord ++ tailWord_2359173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359173).length < 2 ^ (prefixWord ++ tailWord_2359173).sum := by decide
  have hdescent : baseEnd_2359173 < baseStart_2359173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359194 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 2, 3]
def baseStart_2359194 : Nat := 118140960795 + 2359194 * 2 ^ 59
def prefixEnd_2359194 : Nat := 4983230072969 + 3 ^ 40 * 2359194 * 2
def baseEnd_2359194 : Nat := 807600319468898584216847

theorem tailTrace_2359194 : CollatzResearch.WordTrace tailWord_2359194 prefixEnd_2359194 807600319468898584216847 := by
  unfold tailWord_2359194
  simp only [CollatzResearch.WordTrace]
  refine ⟨21511718553762632775587159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57364582810033687401565757 21511718553762632775587159)
  ·
    refine ⟨32267577830643949163380739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21511718553762632775587159 32267577830643949163380739)
    ·
      refine ⟨48401366745965923745071109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32267577830643949163380739 48401366745965923745071109)
      ·
        refine ⟨9075256264868610702200833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48401366745965923745071109 9075256264868610702200833)
        ·
          refine ⟨6806442198651458026650625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9075256264868610702200833 6806442198651458026650625)
          ·
            refine ⟨5104831648988593519987969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6806442198651458026650625 5104831648988593519987969)
            ·
              refine ⟨3828623736741445139990977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5104831648988593519987969 3828623736741445139990977)
              ·
                refine ⟨2871467802556083854993233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828623736741445139990977 2871467802556083854993233)
                ·
                  refine ⟨2153600851917062891244925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2871467802556083854993233 2153600851917062891244925)
                  ·
                    refine ⟨807600319468898584216847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2153600851917062891244925 807600319468898584216847)
                    ·
                      rfl

theorem cell22_2359194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_2359194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359194 prefixEnd_2359194 := by exact prefixLift 2359194
  have htrace : WordTrace (prefixWord ++ tailWord_2359194) baseStart_2359194 baseEnd_2359194 := by
    simpa [prefixWord, tailWord_2359194, baseEnd_2359194] using wordTrace_append hprefix tailTrace_2359194
  have hstable : (prefixWord ++ tailWord_2359194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359194).length < 2 ^ (prefixWord ++ tailWord_2359194).sum := by decide
  have hdescent : baseEnd_2359194 < baseStart_2359194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359196 : List Nat := [2, 2, 3, 3, 1, 3, 2, 2, 4]
def baseStart_2359196 : Nat := 118140960795 + 2359196 * 2 ^ 59
def prefixEnd_2359196 : Nat := 4983230072969 + 3 ^ 40 * 2359196 * 2
def baseEnd_2359196 : Nat := 269200334703257081888947

theorem tailTrace_2359196 : CollatzResearch.WordTrace tailWord_2359196 prefixEnd_2359196 269200334703257081888947 := by
  unfold tailWord_2359196
  simp only [CollatzResearch.WordTrace]
  refine ⟨43023473580521642721960721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57364631440695523629280961 43023473580521642721960721)
  ·
    refine ⟨32267605185391232041470541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43023473580521642721960721 32267605185391232041470541)
    ·
      refine ⟨12100351944521712015551453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32267605185391232041470541 12100351944521712015551453)
      ·
        refine ⟨4537631979195642005831795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12100351944521712015551453 4537631979195642005831795)
        ·
          refine ⟨6806447968793463008747693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4537631979195642005831795 6806447968793463008747693)
          ·
            refine ⟨2552417988297548628280385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6806447968793463008747693 2552417988297548628280385)
            ·
              refine ⟨1914313491223161471210289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552417988297548628280385 1914313491223161471210289)
              ·
                refine ⟨1435735118417371103407717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1914313491223161471210289 1435735118417371103407717)
                ·
                  refine ⟨269200334703257081888947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435735118417371103407717 269200334703257081888947)
                  ·
                    rfl

theorem cell22_2359196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 2, 4].length) (baseStart_2359196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359196 prefixEnd_2359196 := by exact prefixLift 2359196
  have htrace : WordTrace (prefixWord ++ tailWord_2359196) baseStart_2359196 baseEnd_2359196 := by
    simpa [prefixWord, tailWord_2359196, baseEnd_2359196] using wordTrace_append hprefix tailTrace_2359196
  have hstable : (prefixWord ++ tailWord_2359196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359196).length < 2 ^ (prefixWord ++ tailWord_2359196).sum := by decide
  have hdescent : baseEnd_2359196 < baseStart_2359196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359205 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 7, 3]
def baseStart_2359205 : Nat := 118140960795 + 2359205 * 2 ^ 59
def prefixEnd_2359205 : Nat := 4983230072969 + 3 ^ 40 * 2359205 * 2
def baseEnd_2359205 : Nat := 807604084993698222191813

theorem tailTrace_2359205 : CollatzResearch.WordTrace tailWord_2359205 prefixEnd_2359205 807604084993698222191813 := by
  unfold tailWord_2359205
  simp only [CollatzResearch.WordTrace]
  refine ⟨86047275418010679980999069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57364850278673786653999379 86047275418010679980999069)
  ·
    refine ⟨32267728281754004992874651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86047275418010679980999069 32267728281754004992874651)
    ·
      refine ⟨48401592422631007489311977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32267728281754004992874651 48401592422631007489311977)
      ·
        refine ⟨36301194316973255616983983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48401592422631007489311977 36301194316973255616983983)
        ·
          refine ⟨54451791475459883425475975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36301194316973255616983983 54451791475459883425475975)
          ·
            refine ⟨81677687213189825138213963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54451791475459883425475975 81677687213189825138213963)
            ·
              refine ⟨122516530819784737707320945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81677687213189825138213963 122516530819784737707320945)
              ·
                refine ⟨91887398114838553280490709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122516530819784737707320945 91887398114838553280490709)
                ·
                  refine ⟨2153610893316528592511501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 91887398114838553280490709 2153610893316528592511501)
                  ·
                    refine ⟨807604084993698222191813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2153610893316528592511501 807604084993698222191813)
                    ·
                      rfl

theorem cell22_2359205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_2359205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359205 prefixEnd_2359205 := by exact prefixLift 2359205
  have htrace : WordTrace (prefixWord ++ tailWord_2359205) baseStart_2359205 baseEnd_2359205 := by
    simpa [prefixWord, tailWord_2359205, baseEnd_2359205] using wordTrace_append hprefix tailTrace_2359205
  have hstable : (prefixWord ++ tailWord_2359205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359205).length < 2 ^ (prefixWord ++ tailWord_2359205).sum := by decide
  have hdescent : baseEnd_2359205 < baseStart_2359205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359207 : List Nat := [1, 1, 6, 1, 2, 3, 1, 7]
def baseStart_2359207 : Nat := 118140960795 + 2359207 * 2 ^ 59
def prefixEnd_2359207 : Nat := 4983230072969 + 3 ^ 40 * 2359207 * 2
def baseEnd_2359207 : Nat := 89733863292730098182423

theorem tailTrace_2359207 : CollatzResearch.WordTrace tailWord_2359207 prefixEnd_2359207 89733863292730098182423 := by
  unfold tailWord_2359207
  simp only [CollatzResearch.WordTrace]
  refine ⟨86047348364003434322571875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57364898909335622881714583 86047348364003434322571875)
  ·
    refine ⟨129071022546005151483857813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86047348364003434322571875 129071022546005151483857813)
    ·
      refine ⟨6050204181843991475805835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 129071022546005151483857813 6050204181843991475805835)
      ·
        refine ⟨9075306272765987213708753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6050204181843991475805835 9075306272765987213708753)
        ·
          refine ⟨6806479704574490410281565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9075306272765987213708753 6806479704574490410281565)
          ·
            refine ⟨2552429889215433903855587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6806479704574490410281565 2552429889215433903855587)
            ·
              refine ⟨3828644833823150855783381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552429889215433903855587 3828644833823150855783381)
              ·
                refine ⟨89733863292730098182423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3828644833823150855783381 89733863292730098182423)
                ·
                  rfl

theorem cell22_2359207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 7].length) (baseStart_2359207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359207 prefixEnd_2359207 := by exact prefixLift 2359207
  have htrace : WordTrace (prefixWord ++ tailWord_2359207) baseStart_2359207 baseEnd_2359207 := by
    simpa [prefixWord, tailWord_2359207, baseEnd_2359207] using wordTrace_append hprefix tailTrace_2359207
  have hstable : (prefixWord ++ tailWord_2359207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359207).length < 2 ^ (prefixWord ++ tailWord_2359207).sum := by decide
  have hdescent : baseEnd_2359207 < baseStart_2359207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359265 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 5, 4]
def baseStart_2359265 : Nat := 118140960795 + 2359265 * 2 ^ 59
def prefixEnd_2359265 : Nat := 4983230072969 + 3 ^ 40 * 2359265 * 2
def baseEnd_2359265 : Nat := 807624624219878065691629

theorem tailTrace_2359265 : CollatzResearch.WordTrace tailWord_2359265 prefixEnd_2359265 807624624219878065691629 := by
  unfold tailWord_2359265
  simp only [CollatzResearch.WordTrace]
  refine ⟨86049463797793310228183249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57366309198528873485455499 86049463797793310228183249)
  ·
    refine ⟨64537097848344982671137437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86049463797793310228183249 64537097848344982671137437)
    ·
      refine ⟨24201411693129368501676539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64537097848344982671137437 24201411693129368501676539)
      ·
        refine ⟨36302117539694052752514809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24201411693129368501676539 36302117539694052752514809)
        ·
          refine ⟨27226588154770539564386107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36302117539694052752514809 27226588154770539564386107)
          ·
            refine ⟨40839882232155809346579161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27226588154770539564386107 40839882232155809346579161)
            ·
              refine ⟨30629911674116857009934371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40839882232155809346579161 30629911674116857009934371)
              ·
                refine ⟨45944867511175285514901557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30629911674116857009934371 45944867511175285514901557)
                ·
                  refine ⟨4307331329172683017022021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45944867511175285514901557 4307331329172683017022021)
                  ·
                    refine ⟨807624624219878065691629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4307331329172683017022021 807624624219878065691629)
                    ·
                      rfl

theorem cell22_2359265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_2359265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359265 prefixEnd_2359265 := by exact prefixLift 2359265
  have htrace : WordTrace (prefixWord ++ tailWord_2359265) baseStart_2359265 baseEnd_2359265 := by
    simpa [prefixWord, tailWord_2359265, baseEnd_2359265] using wordTrace_append hprefix tailTrace_2359265
  have hstable : (prefixWord ++ tailWord_2359265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359265).length < 2 ^ (prefixWord ++ tailWord_2359265).sum := by decide
  have hdescent : baseEnd_2359265 < baseStart_2359265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359280 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 6]
def baseStart_2359280 : Nat := 118140960795 + 2359280 * 2 ^ 59
def prefixEnd_2359280 : Nat := 4983230072969 + 3 ^ 40 * 2359280 * 2
def baseEnd_2359280 : Nat := 269209919675474342188861

theorem tailTrace_2359280 : CollatzResearch.WordTrace tailWord_2359280 prefixEnd_2359280 269209919675474342188861 := by
  unfold tailWord_2359280
  simp only [CollatzResearch.WordTrace]
  refine ⟨43025005446369483894989647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57366673928492645193319529 43025005446369483894989647)
  ·
    refine ⟨64537508169554225842484471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43025005446369483894989647 64537508169554225842484471)
    ·
      refine ⟨96806262254331338763726707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64537508169554225842484471 96806262254331338763726707)
      ·
        refine ⟨145209393381497008145590061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96806262254331338763726707 145209393381497008145590061)
        ·
          refine ⟨54453522518061378054596273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145209393381497008145590061 54453522518061378054596273)
          ·
            refine ⟨40840141888546033540947205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54453522518061378054596273 40840141888546033540947205)
            ·
              refine ⟨7657526604102381288927601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40840141888546033540947205 7657526604102381288927601)
              ·
                refine ⟨5743144953076785966695701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7657526604102381288927601 5743144953076785966695701)
                ·
                  refine ⟨269209919675474342188861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5743144953076785966695701 269209919675474342188861)
                  ·
                    rfl

theorem cell22_2359280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_2359280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359280 prefixEnd_2359280 := by exact prefixLift 2359280
  have htrace : WordTrace (prefixWord ++ tailWord_2359280) baseStart_2359280 baseEnd_2359280 := by
    simpa [prefixWord, tailWord_2359280, baseEnd_2359280] using wordTrace_append hprefix tailTrace_2359280
  have hstable : (prefixWord ++ tailWord_2359280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359280).length < 2 ^ (prefixWord ++ tailWord_2359280).sum := by decide
  have hdescent : baseEnd_2359280 < baseStart_2359280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359295 : List Nat := [1, 1, 2, 2, 1, 2, 1, 6, 1, 5]
def baseStart_2359295 : Nat := 118140960795 + 2359295 * 2 ^ 59
def prefixEnd_2359295 : Nat := 4983230072969 + 3 ^ 40 * 2359295 * 2
def baseEnd_2359295 : Nat := 807634893832967987441537

theorem tailTrace_2359295 : CollatzResearch.WordTrace tailWord_2359295 prefixEnd_2359295 807634893832967987441537 := by
  unfold tailWord_2359295
  simp only [CollatzResearch.WordTrace]
  refine ⟨86050557987684625351775339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57367038658456416901183559 86050557987684625351775339)
  ·
    refine ⟨129075836981526938027663009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86050557987684625351775339 129075836981526938027663009)
    ·
      refine ⟨96806877736145203520747257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129075836981526938027663009 96806877736145203520747257)
      ·
        refine ⟨72605158302108902640560443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96806877736145203520747257 72605158302108902640560443)
        ·
          refine ⟨108907737453163353960840665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72605158302108902640560443 108907737453163353960840665)
          ·
            refine ⟨81680803089872515470630499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108907737453163353960840665 81680803089872515470630499)
            ·
              refine ⟨122521204634808773205945749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81680803089872515470630499 122521204634808773205945749)
              ·
                refine ⟨5743181467256661244028707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122521204634808773205945749 5743181467256661244028707)
                ·
                  refine ⟨8614772200884991866043061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5743181467256661244028707 8614772200884991866043061)
                  ·
                    refine ⟨807634893832967987441537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8614772200884991866043061 807634893832967987441537)
                    ·
                      rfl

theorem cell22_2359295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_2359295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359295 prefixEnd_2359295 := by exact prefixLift 2359295
  have htrace : WordTrace (prefixWord ++ tailWord_2359295) baseStart_2359295 baseEnd_2359295 := by
    simpa [prefixWord, tailWord_2359295, baseEnd_2359295] using wordTrace_append hprefix tailTrace_2359295
  have hstable : (prefixWord ++ tailWord_2359295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359295).length < 2 ^ (prefixWord ++ tailWord_2359295).sum := by decide
  have hdescent : baseEnd_2359295 < baseStart_2359295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359342 : List Nat := [4, 1, 3, 1, 1, 2, 2, 8]
def baseStart_2359342 : Nat := 118140960795 + 2359342 * 2 ^ 59
def prefixEnd_2359342 : Nat := 4983230072969 + 3 ^ 40 * 2359342 * 2
def baseEnd_2359342 : Nat := 89738998099275059057377

theorem tailTrace_2359342 : CollatzResearch.WordTrace tailWord_2359342 prefixEnd_2359342 89738998099275059057377 := by
  unfold tailWord_2359342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10756534027314294047342035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57368181479009568252490853 10756534027314294047342035)
  ·
    refine ⟨16134801040971441071013053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10756534027314294047342035 16134801040971441071013053)
    ·
      refine ⟨6050550390364290401629895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16134801040971441071013053 6050550390364290401629895)
      ·
        refine ⟨9075825585546435602444843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6050550390364290401629895 9075825585546435602444843)
        ·
          refine ⟨13613738378319653403667265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9075825585546435602444843 13613738378319653403667265)
          ·
            refine ⟨10210303783739740052750449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13613738378319653403667265 10210303783739740052750449)
            ·
              refine ⟨7657727837804805039562837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10210303783739740052750449 7657727837804805039562837)
              ·
                refine ⟨89738998099275059057377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7657727837804805039562837 89738998099275059057377)
                ·
                  rfl

theorem cell22_2359342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_2359342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359342 prefixEnd_2359342 := by exact prefixLift 2359342
  have htrace : WordTrace (prefixWord ++ tailWord_2359342) baseStart_2359342 baseEnd_2359342 := by
    simpa [prefixWord, tailWord_2359342, baseEnd_2359342] using wordTrace_append hprefix tailTrace_2359342
  have hstable : (prefixWord ++ tailWord_2359342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359342).length < 2 ^ (prefixWord ++ tailWord_2359342).sum := by decide
  have hdescent : baseEnd_2359342 < baseStart_2359342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359479 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 2, 4]
def baseStart_2359479 : Nat := 118140960795 + 2359479 * 2 ^ 59
def prefixEnd_2359479 : Nat := 4983230072969 + 3 ^ 40 * 2359479 * 2
def baseEnd_2359479 : Nat := 807697880793252840840973

theorem tailTrace_2359479 : CollatzResearch.WordTrace tailWord_2359479 prefixEnd_2359479 807697880793252840840973 := by
  unfold tailWord_2359479
  simp only [CollatzResearch.WordTrace]
  refine ⟨86057269019018024776473491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57371512679345349850982327 86057269019018024776473491)
  ·
    refine ⟨129085903528527037164710237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86057269019018024776473491 129085903528527037164710237)
    ·
      refine ⟨48407213823197638936766339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129085903528527037164710237 48407213823197638936766339)
      ·
        refine ⟨72610820734796458405149509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48407213823197638936766339 72610820734796458405149509)
        ·
          refine ⟨13614528887774335950965533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72610820734796458405149509 13614528887774335950965533)
          ·
            refine ⟨5105448332915375981612075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13614528887774335950965533 5105448332915375981612075)
            ·
              refine ⟨7658172499373063972418113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5105448332915375981612075 7658172499373063972418113)
              ·
                refine ⟨5743629374529797979313585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7658172499373063972418113 5743629374529797979313585)
                ·
                  refine ⟨4307722030897348484485189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5743629374529797979313585 4307722030897348484485189)
                  ·
                    refine ⟨807697880793252840840973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4307722030897348484485189 807697880793252840840973)
                    ·
                      rfl

theorem cell22_2359479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_2359479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359479 prefixEnd_2359479 := by exact prefixLift 2359479
  have htrace : WordTrace (prefixWord ++ tailWord_2359479) baseStart_2359479 baseEnd_2359479 := by
    simpa [prefixWord, tailWord_2359479, baseEnd_2359479] using wordTrace_append hprefix tailTrace_2359479
  have hstable : (prefixWord ++ tailWord_2359479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359479).length < 2 ^ (prefixWord ++ tailWord_2359479).sum := by decide
  have hdescent : baseEnd_2359479 < baseStart_2359479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359539 : List Nat := [1, 1, 1, 2, 2, 4, 4, 2, 5]
def baseStart_2359539 : Nat := 118140960795 + 2359539 * 2 ^ 59
def prefixEnd_2359539 : Nat := 4983230072969 + 3 ^ 40 * 2359539 * 2
def baseEnd_2359539 : Nat := 269239473339810894780263

theorem tailTrace_2359539 : CollatzResearch.WordTrace tailWord_2359539 prefixEnd_2359539 269239473339810894780263 := by
  unfold tailWord_2359539
  simp only [CollatzResearch.WordTrace]
  refine ⟨86059457398800655023657671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57372971599200436682438447 86059457398800655023657671)
  ·
    refine ⟨129089186098200982535486507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86059457398800655023657671 129089186098200982535486507)
    ·
      refine ⟨193633779147301473803229761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129089186098200982535486507 193633779147301473803229761)
      ·
        refine ⟨145225334360476105352422321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193633779147301473803229761 145225334360476105352422321)
        ·
          refine ⟨108919000770357079014316741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145225334360476105352422321 108919000770357079014316741)
          ·
            refine ⟨20422312644441952315184389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108919000770357079014316741 20422312644441952315184389)
            ·
              refine ⟨3829183620832866059097073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20422312644441952315184389 3829183620832866059097073)
              ·
                refine ⟨2871887715624649544322805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3829183620832866059097073 2871887715624649544322805)
                ·
                  refine ⟨269239473339810894780263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2871887715624649544322805 269239473339810894780263)
                  ·
                    rfl

theorem cell22_2359539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 2, 5].length) (baseStart_2359539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359539 prefixEnd_2359539 := by exact prefixLift 2359539
  have htrace : WordTrace (prefixWord ++ tailWord_2359539) baseStart_2359539 baseEnd_2359539 := by
    simpa [prefixWord, tailWord_2359539, baseEnd_2359539] using wordTrace_append hprefix tailTrace_2359539
  have hstable : (prefixWord ++ tailWord_2359539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359539).length < 2 ^ (prefixWord ++ tailWord_2359539).sum := by decide
  have hdescent : baseEnd_2359539 < baseStart_2359539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359569 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 3, 4]
def baseStart_2359569 : Nat := 118140960795 + 2359569 * 2 ^ 59
def prefixEnd_2359569 : Nat := 4983230072969 + 3 ^ 40 * 2359569 * 2
def baseEnd_2359569 : Nat := 807728689632522606090697

theorem tailTrace_2359569 : CollatzResearch.WordTrace tailWord_2359569 prefixEnd_2359569 807728689632522606090697 := by
  unfold tailWord_2359569
  simp only [CollatzResearch.WordTrace]
  refine ⟨86060551588691970147249761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57373701059127980098166507 86060551588691970147249761)
  ·
    refine ⟨64545413691518977610437321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86060551588691970147249761 64545413691518977610437321)
    ·
      refine ⟨48409060268639233207827991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64545413691518977610437321 48409060268639233207827991)
      ·
        refine ⟨72613590402958849811741987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48409060268639233207827991 72613590402958849811741987)
        ·
          refine ⟨108920385604438274717612981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72613590402958849811741987 108920385604438274717612981)
          ·
            refine ⟨10211286150416088254776217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108920385604438274717612981 10211286150416088254776217)
            ·
              refine ⟨7658464612812066191082163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10211286150416088254776217 7658464612812066191082163)
              ·
                refine ⟨11487696919218099286623245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7658464612812066191082163 11487696919218099286623245)
                ·
                  refine ⟨4307886344706787232483717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11487696919218099286623245 4307886344706787232483717)
                  ·
                    refine ⟨807728689632522606090697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4307886344706787232483717 807728689632522606090697)
                    ·
                      rfl

theorem cell22_2359569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_2359569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359569 prefixEnd_2359569 := by exact prefixLift 2359569
  have htrace : WordTrace (prefixWord ++ tailWord_2359569) baseStart_2359569 baseEnd_2359569 := by
    simpa [prefixWord, tailWord_2359569, baseEnd_2359569] using wordTrace_append hprefix tailTrace_2359569
  have hstable : (prefixWord ++ tailWord_2359569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359569).length < 2 ^ (prefixWord ++ tailWord_2359569).sum := by decide
  have hdescent : baseEnd_2359569 < baseStart_2359569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359601 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 6]
def baseStart_2359601 : Nat := 118140960795 + 2359601 * 2 ^ 59
def prefixEnd_2359601 : Nat := 4983230072969 + 3 ^ 40 * 2359601 * 2
def baseEnd_2359601 : Nat := 269246547962161729763533

theorem tailTrace_2359601 : CollatzResearch.WordTrace tailWord_2359601 prefixEnd_2359601 269246547962161729763533 := by
  unfold tailWord_2359601
  simp only [CollatzResearch.WordTrace]
  refine ⟨86061718724576039612414657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57374479149717359741609771 86061718724576039612414657)
  ·
    refine ⟨64546289043432029709310993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86061718724576039612414657 64546289043432029709310993)
    ·
      refine ⟨48409716782574022281983245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64546289043432029709310993 48409716782574022281983245)
      ·
        refine ⟨18153643793465258355743717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48409716782574022281983245 18153643793465258355743717)
        ·
          refine ⟨3403808211274735941701947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18153643793465258355743717 3403808211274735941701947)
          ·
            refine ⟨5105712316912103912552921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3403808211274735941701947 5105712316912103912552921)
            ·
              refine ⟨3829284237684077934414691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5105712316912103912552921 3829284237684077934414691)
              ·
                refine ⟨5743926356526116901622037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3829284237684077934414691 5743926356526116901622037)
                ·
                  refine ⟨269246547962161729763533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5743926356526116901622037 269246547962161729763533)
                  ·
                    rfl

theorem cell22_2359601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_2359601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359601 prefixEnd_2359601 := by exact prefixLift 2359601
  have htrace : WordTrace (prefixWord ++ tailWord_2359601) baseStart_2359601 baseEnd_2359601 := by
    simpa [prefixWord, tailWord_2359601, baseEnd_2359601] using wordTrace_append hprefix tailTrace_2359601
  have hstable : (prefixWord ++ tailWord_2359601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359601).length < 2 ^ (prefixWord ++ tailWord_2359601).sum := by decide
  have hdescent : baseEnd_2359601 < baseStart_2359601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359620 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2359620 : Nat := 118140960795 + 2359620 * 2 ^ 59
def prefixEnd_2359620 : Nat := 4983230072969 + 3 ^ 40 * 2359620 * 2
def baseEnd_2359620 : Nat := 807746147974775473065541

theorem tailTrace_2359620 : CollatzResearch.WordTrace tailWord_2359620 prefixEnd_2359620 807746147974775473065541 := by
  unfold tailWord_2359620
  simp only [CollatzResearch.WordTrace]
  refine ⟨43031205855753602928678157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57374941141004803904904209 43031205855753602928678157)
  ·
    refine ⟨16136702195907601098254309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43031205855753602928678157 16136702195907601098254309)
    ·
      refine ⟨3025631661732675205922683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16136702195907601098254309 3025631661732675205922683)
      ·
        refine ⟨4538447492599012808884025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3025631661732675205922683 4538447492599012808884025)
        ·
          refine ⟨3403835619449259606663019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4538447492599012808884025 3403835619449259606663019)
          ·
            refine ⟨5105753429173889409994529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3403835619449259606663019 5105753429173889409994529)
            ·
              refine ⟨3829315071880417057495897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5105753429173889409994529 3829315071880417057495897)
              ·
                refine ⟨2871986303910312793121923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3829315071880417057495897 2871986303910312793121923)
                ·
                  refine ⟨4307979455865469189682885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871986303910312793121923 4307979455865469189682885)
                  ·
                    refine ⟨807746147974775473065541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4307979455865469189682885 807746147974775473065541)
                    ·
                      rfl

theorem cell22_2359620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2359620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359620 prefixEnd_2359620 := by exact prefixLift 2359620
  have htrace : WordTrace (prefixWord ++ tailWord_2359620) baseStart_2359620 baseEnd_2359620 := by
    simpa [prefixWord, tailWord_2359620, baseEnd_2359620] using wordTrace_append hprefix tailTrace_2359620
  have hstable : (prefixWord ++ tailWord_2359620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359620).length < 2 ^ (prefixWord ++ tailWord_2359620).sum := by decide
  have hdescent : baseEnd_2359620 < baseStart_2359620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359712 : List Nat := [2, 1, 1, 4, 1, 5, 2, 2, 1, 3]
def baseStart_2359712 : Nat := 118140960795 + 2359712 * 2 ^ 59
def prefixEnd_2359712 : Nat := 4983230072969 + 3 ^ 40 * 2359712 * 2
def baseEnd_2359712 : Nat := 807777641454917899765259

theorem tailTrace_2359712 : CollatzResearch.WordTrace tailWord_2359712 prefixEnd_2359712 807777641454917899765259 := by
  unfold tailWord_2359712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43032883613586952784852695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57377178151449270379803593 43032883613586952784852695)
  ·
    refine ⟨64549325420380429177279043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43032883613586952784852695 64549325420380429177279043)
    ·
      refine ⟨96823988130570643765918565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64549325420380429177279043 96823988130570643765918565)
      ·
        refine ⟨18154497774481995706109731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96823988130570643765918565 18154497774481995706109731)
        ·
          refine ⟨27231746661722993559164597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18154497774481995706109731 27231746661722993559164597)
          ·
            refine ⟨2552976249536530646171681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27231746661722993559164597 2552976249536530646171681)
            ·
              refine ⟨1914732187152397984628761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552976249536530646171681 1914732187152397984628761)
              ·
                refine ⟨1436049140364298488471571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1914732187152397984628761 1436049140364298488471571)
                ·
                  refine ⟨2154073710546447732707357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436049140364298488471571 2154073710546447732707357)
                  ·
                    refine ⟨807777641454917899765259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2154073710546447732707357 807777641454917899765259)
                    ·
                      rfl

theorem cell22_2359712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 1, 3].length) (baseStart_2359712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359712 prefixEnd_2359712 := by exact prefixLift 2359712
  have htrace : WordTrace (prefixWord ++ tailWord_2359712) baseStart_2359712 baseEnd_2359712 := by
    simpa [prefixWord, tailWord_2359712, baseEnd_2359712] using wordTrace_append hprefix tailTrace_2359712
  have hstable : (prefixWord ++ tailWord_2359712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359712).length < 2 ^ (prefixWord ++ tailWord_2359712).sum := by decide
  have hdescent : baseEnd_2359712 < baseStart_2359712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359751 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 1, 5]
def baseStart_2359751 : Nat := 118140960795 + 2359751 * 2 ^ 59
def prefixEnd_2359751 : Nat := 4983230072969 + 3 ^ 40 * 2359751 * 2
def baseEnd_2359751 : Nat := 807790991951934798040139

theorem tailTrace_2359751 : CollatzResearch.WordTrace tailWord_2359751 prefixEnd_2359751 807790991951934798040139 := by
  unfold tailWord_2359751
  simp only [CollatzResearch.WordTrace]
  refine ⟨86067189674032615230375107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57378126449355076820250071 86067189674032615230375107)
  ·
    refine ⟨129100784511048922845562661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86067189674032615230375107 129100784511048922845562661)
    ·
      refine ⟨24206397095821673033542999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129100784511048922845562661 24206397095821673033542999)
      ·
        refine ⟨36309595643732509550314499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24206397095821673033542999 36309595643732509550314499)
        ·
          refine ⟨54464393465598764325471749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36309595643732509550314499 54464393465598764325471749)
          ·
            refine ⟨10212073774799768311025953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54464393465598764325471749 10212073774799768311025953)
            ·
              refine ⟨7659055331099826233269465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10212073774799768311025953 7659055331099826233269465)
              ·
                refine ⟨5744291498324869674952099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7659055331099826233269465 5744291498324869674952099)
                ·
                  refine ⟨8616437247487304512428149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5744291498324869674952099 8616437247487304512428149)
                  ·
                    refine ⟨807790991951934798040139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8616437247487304512428149 807790991951934798040139)
                    ·
                      rfl

theorem cell22_2359751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_2359751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359751 prefixEnd_2359751 := by exact prefixLift 2359751
  have htrace : WordTrace (prefixWord ++ tailWord_2359751) baseStart_2359751 baseEnd_2359751 := by
    simpa [prefixWord, tailWord_2359751, baseEnd_2359751] using wordTrace_append hprefix tailTrace_2359751
  have hstable : (prefixWord ++ tailWord_2359751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359751).length < 2 ^ (prefixWord ++ tailWord_2359751).sum := by decide
  have hdescent : baseEnd_2359751 < baseStart_2359751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359841 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_2359841 : Nat := 118140960795 + 2359841 * 2 ^ 59
def prefixEnd_2359841 : Nat := 4983230072969 + 3 ^ 40 * 2359841 * 2
def baseEnd_2359841 : Nat := 807821800791204563289863

theorem tailTrace_2359841 : CollatzResearch.WordTrace tailWord_2359841 prefixEnd_2359841 807821800791204563289863 := by
  unfold tailWord_2359841
  simp only [CollatzResearch.WordTrace]
  refine ⟨86070472243706560601151377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57380314829137707067434251 86070472243706560601151377)
  ·
    refine ⟨64552854182779920450863533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86070472243706560601151377 64552854182779920450863533)
    ·
      refine ⟨24207320318542470169073825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64552854182779920450863533 24207320318542470169073825)
      ·
        refine ⟨18155490238906852626805369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24207320318542470169073825 18155490238906852626805369)
        ·
          refine ⟨13616617679180139470104027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18155490238906852626805369 13616617679180139470104027)
          ·
            refine ⟨20424926518770209205156041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13616617679180139470104027 20424926518770209205156041)
            ·
              refine ⟨15318694889077656903867031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20424926518770209205156041 15318694889077656903867031)
              ·
                refine ⟨22978042333616485355800547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15318694889077656903867031 22978042333616485355800547)
                ·
                  refine ⟨34467063500424728033700821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22978042333616485355800547 34467063500424728033700821)
                  ·
                    refine ⟨807821800791204563289863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34467063500424728033700821 807821800791204563289863)
                    ·
                      rfl

theorem cell22_2359841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_2359841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359841 prefixEnd_2359841 := by exact prefixLift 2359841
  have htrace : WordTrace (prefixWord ++ tailWord_2359841) baseStart_2359841 baseEnd_2359841 := by
    simpa [prefixWord, tailWord_2359841, baseEnd_2359841] using wordTrace_append hprefix tailTrace_2359841
  have hstable : (prefixWord ++ tailWord_2359841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359841).length < 2 ^ (prefixWord ++ tailWord_2359841).sum := by decide
  have hdescent : baseEnd_2359841 < baseStart_2359841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359843 : List Nat := [1, 1, 1, 4, 4, 2, 1, 3, 5]
def baseStart_2359843 : Nat := 118140960795 + 2359843 * 2 ^ 59
def prefixEnd_2359843 : Nat := 4983230072969 + 3 ^ 40 * 2359843 * 2
def baseEnd_2359843 : Nat := 269274161810692408246619

theorem tailTrace_2359843 : CollatzResearch.WordTrace tailWord_2359843 prefixEnd_2359843 269274161810692408246619 := by
  unfold tailWord_2359843
  simp only [CollatzResearch.WordTrace]
  refine ⟨86070545189699314942724183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57380363459799543295149455 86070545189699314942724183)
  ·
    refine ⟨129105817784548972414086275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86070545189699314942724183 129105817784548972414086275)
    ·
      refine ⟨193658726676823458621129413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129105817784548972414086275 193658726676823458621129413)
      ·
        refine ⟨36311011251904398491461765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193658726676823458621129413 36311011251904398491461765)
        ·
          refine ⟨6808314609732074717149081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36311011251904398491461765 6808314609732074717149081)
          ·
            refine ⟨5106235957299056037861811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6808314609732074717149081 5106235957299056037861811)
            ·
              refine ⟨7659353935948584056792717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5106235957299056037861811 7659353935948584056792717)
              ·
                refine ⟨2872257725980719021297269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7659353935948584056792717 2872257725980719021297269)
                ·
                  refine ⟨269274161810692408246619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2872257725980719021297269 269274161810692408246619)
                  ·
                    rfl

theorem cell22_2359843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 3, 5].length) (baseStart_2359843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359843 prefixEnd_2359843 := by exact prefixLift 2359843
  have htrace : WordTrace (prefixWord ++ tailWord_2359843) baseStart_2359843 baseEnd_2359843 := by
    simpa [prefixWord, tailWord_2359843, baseEnd_2359843] using wordTrace_append hprefix tailTrace_2359843
  have hstable : (prefixWord ++ tailWord_2359843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359843).length < 2 ^ (prefixWord ++ tailWord_2359843).sum := by decide
  have hdescent : baseEnd_2359843 < baseStart_2359843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359916 : List Nat := [2, 2, 1, 1, 3, 1, 2, 10]
def baseStart_2359916 : Nat := 118140960795 + 2359916 * 2 ^ 59
def prefixEnd_2359916 : Nat := 4983230072969 + 3 ^ 40 * 2359916 * 2
def baseEnd_2359916 : Nat := 89760830535992151962737

theorem tailTrace_2359916 : CollatzResearch.WordTrace tailWord_2359916 prefixEnd_2359916 89760830535992151962737 := by
  unfold tailWord_2359916
  simp only [CollatzResearch.WordTrace]
  refine ⟨43036603859217424205065801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57382138478956565606754401 43036603859217424205065801)
  ·
    refine ⟨32277452894413068153799351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43036603859217424205065801 32277452894413068153799351)
    ·
      refine ⟨48416179341619602230699027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32277452894413068153799351 48416179341619602230699027)
      ·
        refine ⟨72624269012429403346048541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48416179341619602230699027 72624269012429403346048541)
        ·
          refine ⟨27234100879661026254768203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72624269012429403346048541 27234100879661026254768203)
          ·
            refine ⟨40851151319491539382152305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27234100879661026254768203 40851151319491539382152305)
            ·
              refine ⟨30638363489618654536614229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40851151319491539382152305 30638363489618654536614229)
              ·
                refine ⟨89760830535992151962737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30638363489618654536614229 89760830535992151962737)
                ·
                  rfl

theorem cell22_2359916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 10].length) (baseStart_2359916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359916 prefixEnd_2359916 := by exact prefixLift 2359916
  have htrace : WordTrace (prefixWord ++ tailWord_2359916) baseStart_2359916 baseEnd_2359916 := by
    simpa [prefixWord, tailWord_2359916, baseEnd_2359916] using wordTrace_append hprefix tailTrace_2359916
  have hstable : (prefixWord ++ tailWord_2359916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359916).length < 2 ^ (prefixWord ++ tailWord_2359916).sum := by decide
  have hdescent : baseEnd_2359916 < baseStart_2359916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359922 : List Nat := [3, 2, 1, 2, 4, 1, 2, 3, 4]
def baseStart_2359922 : Nat := 118140960795 + 2359922 * 2 ^ 59
def prefixEnd_2359922 : Nat := 4983230072969 + 3 ^ 40 * 2359922 * 2
def baseEnd_2359922 : Nat := 269283176248849117338205

theorem tailTrace_2359922 : CollatzResearch.WordTrace tailWord_2359922 prefixEnd_2359922 269283176248849117338205 := by
  unfold tailWord_2359922
  simp only [CollatzResearch.WordTrace]
  refine ⟨21518356639103277858712505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57382284370942074289900013 21518356639103277858712505)
  ·
    refine ⟨16138767479327458394034379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21518356639103277858712505 16138767479327458394034379)
    ·
      refine ⟨24208151218991187591051569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16138767479327458394034379 24208151218991187591051569)
      ·
        refine ⟨18156113414243390693288677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24208151218991187591051569 18156113414243390693288677)
        ·
          refine ⟨3404271265170635754991627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18156113414243390693288677 3404271265170635754991627)
          ·
            refine ⟨5106406897755953632487441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3404271265170635754991627 5106406897755953632487441)
            ·
              refine ⟨3829805173316965224365581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5106406897755953632487441 3829805173316965224365581)
              ·
                refine ⟨1436176939993861959137093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3829805173316965224365581 1436176939993861959137093)
                ·
                  refine ⟨269283176248849117338205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1436176939993861959137093 269283176248849117338205)
                  ·
                    rfl

theorem cell22_2359922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_2359922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359922 prefixEnd_2359922 := by exact prefixLift 2359922
  have htrace : WordTrace (prefixWord ++ tailWord_2359922) baseStart_2359922 baseEnd_2359922 := by
    simpa [prefixWord, tailWord_2359922, baseEnd_2359922] using wordTrace_append hprefix tailTrace_2359922
  have hstable : (prefixWord ++ tailWord_2359922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359922).length < 2 ^ (prefixWord ++ tailWord_2359922).sum := by decide
  have hdescent : baseEnd_2359922 < baseStart_2359922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359933 : List Nat := [1, 4, 1, 1, 5, 1, 9]
def baseStart_2359933 : Nat := 118140960795 + 2359933 * 2 ^ 59
def prefixEnd_2359933 : Nat := 4983230072969 + 3 ^ 40 * 2359933 * 2
def baseEnd_2359933 : Nat := 29920492380420258888503

theorem tailTrace_2359933 : CollatzResearch.WordTrace tailWord_2359933 prefixEnd_2359933 29920492380420258888503 := by
  unfold tailWord_2359933
  simp only [CollatzResearch.WordTrace]
  refine ⟨86073827759373260313500453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57382551839582173542333635 86073827759373260313500453)
  ·
    refine ⟨16138842704882486308781335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86073827759373260313500453 16138842704882486308781335)
    ·
      refine ⟨24208264057323729463172003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16138842704882486308781335 24208264057323729463172003)
      ·
        refine ⟨36312396085985594194758005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24208264057323729463172003 36312396085985594194758005)
        ·
          refine ⟨3404287133061149455758563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36312396085985594194758005 3404287133061149455758563)
          ·
            refine ⟨5106430699591724183637845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3404287133061149455758563 5106430699591724183637845)
            ·
              refine ⟨29920492380420258888503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5106430699591724183637845 29920492380420258888503)
              ·
                rfl

theorem cell22_2359933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 9].length) (baseStart_2359933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359933 prefixEnd_2359933 := by exact prefixLift 2359933
  have htrace : WordTrace (prefixWord ++ tailWord_2359933) baseStart_2359933 baseEnd_2359933 := by
    simpa [prefixWord, tailWord_2359933, baseEnd_2359933] using wordTrace_append hprefix tailTrace_2359933
  have hstable : (prefixWord ++ tailWord_2359933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359933).length < 2 ^ (prefixWord ++ tailWord_2359933).sum := by decide
  have hdescent : baseEnd_2359933 < baseStart_2359933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359954 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 2, 3]
def baseStart_2359954 : Nat := 118140960795 + 2359954 * 2 ^ 59
def prefixEnd_2359954 : Nat := 4983230072969 + 3 ^ 40 * 2359954 * 2
def baseEnd_2359954 : Nat := 807860483000509935214517

theorem tailTrace_2359954 : CollatzResearch.WordTrace tailWord_2359954 prefixEnd_2359954 807860483000509935214517 := by
  unfold tailWord_2359954
  simp only [CollatzResearch.WordTrace]
  refine ⟨21518648423074295225003729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57383062461531453933343277 21518648423074295225003729)
  ·
    refine ⟨16138986317305721418752797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21518648423074295225003729 16138986317305721418752797)
    ·
      refine ⟨6052119868989645532032299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16138986317305721418752797 6052119868989645532032299)
      ·
        refine ⟨9078179803484468298048449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6052119868989645532032299 9078179803484468298048449)
        ·
          refine ⟨6808634852613351223536337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9078179803484468298048449 6808634852613351223536337)
          ·
            refine ⟨5106476139460013417652253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6808634852613351223536337 5106476139460013417652253)
            ·
              refine ⟨1914928552297505031619595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5106476139460013417652253 1914928552297505031619595)
              ·
                refine ⟨2872392828446257547429393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914928552297505031619595 2872392828446257547429393)
                ·
                  refine ⟨2154294621334693160572045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2872392828446257547429393 2154294621334693160572045)
                  ·
                    refine ⟨807860483000509935214517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2154294621334693160572045 807860483000509935214517)
                    ·
                      rfl

theorem cell22_2359954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_2359954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359954 prefixEnd_2359954 := by exact prefixLift 2359954
  have htrace : WordTrace (prefixWord ++ tailWord_2359954) baseStart_2359954 baseEnd_2359954 := by
    simpa [prefixWord, tailWord_2359954, baseEnd_2359954] using wordTrace_append hprefix tailTrace_2359954
  have hstable : (prefixWord ++ tailWord_2359954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359954).length < 2 ^ (prefixWord ++ tailWord_2359954).sum := by decide
  have hdescent : baseEnd_2359954 < baseStart_2359954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359965 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_2359965 : Nat := 118140960795 + 2359965 * 2 ^ 59
def prefixEnd_2359965 : Nat := 4983230072969 + 3 ^ 40 * 2359965 * 2
def baseEnd_2359965 : Nat := 807864248525309573189483

theorem tailTrace_2359965 : CollatzResearch.WordTrace tailWord_2359965 prefixEnd_2359965 807864248525309573189483 := by
  unfold tailWord_2359965
  simp only [CollatzResearch.WordTrace]
  refine ⟨86074994895257329778665349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57383329930171553185776899 86074994895257329778665349)
  ·
    refine ⟨16139061542860749333499753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86074994895257329778665349 16139061542860749333499753)
    ·
      refine ⟨12104296157145562000124815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16139061542860749333499753 12104296157145562000124815)
      ·
        refine ⟨18156444235718343000187223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12104296157145562000124815 18156444235718343000187223)
        ·
          refine ⟨27234666353577514500280835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18156444235718343000187223 27234666353577514500280835)
          ·
            refine ⟨40851999530366271750421253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27234666353577514500280835 40851999530366271750421253)
            ·
              refine ⟨7659749911943675953203985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40851999530366271750421253 7659749911943675953203985)
              ·
                refine ⟨5744812433957756964902989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7659749911943675953203985 5744812433957756964902989)
                ·
                  refine ⟨2154304662734158861838621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5744812433957756964902989 2154304662734158861838621)
                  ·
                    refine ⟨807864248525309573189483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2154304662734158861838621 807864248525309573189483)
                    ·
                      rfl

theorem cell22_2359965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_2359965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359965 prefixEnd_2359965 := by exact prefixLift 2359965
  have htrace : WordTrace (prefixWord ++ tailWord_2359965) baseStart_2359965 baseEnd_2359965 := by
    simpa [prefixWord, tailWord_2359965, baseEnd_2359965] using wordTrace_append hprefix tailTrace_2359965
  have hstable : (prefixWord ++ tailWord_2359965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359965).length < 2 ^ (prefixWord ++ tailWord_2359965).sum := by decide
  have hdescent : baseEnd_2359965 < baseStart_2359965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359999 : List Nat := [1, 1, 2, 2, 2, 5, 3, 2, 1, 3]
def baseStart_2359999 : Nat := 118140960795 + 2359999 * 2 ^ 59
def prefixEnd_2359999 : Nat := 4983230072969 + 3 ^ 40 * 2359999 * 2
def baseEnd_2359999 : Nat := 807875887420144817839379

theorem tailTrace_2359999 : CollatzResearch.WordTrace tailWord_2359999 prefixEnd_2359999 807875887420144817839379 := by
  unfold tailWord_2359999
  simp only [CollatzResearch.WordTrace]
  refine ⟨86076234977134153585403051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57384156651422769056935367 86076234977134153585403051)
  ·
    refine ⟨129114352465701230378104577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86076234977134153585403051 129114352465701230378104577)
    ·
      refine ⟨96835764349275922783578433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129114352465701230378104577 96835764349275922783578433)
      ·
        refine ⟨72626823261956942087683825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96835764349275922783578433 72626823261956942087683825)
        ·
          refine ⟨54470117446467706565762869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72626823261956942087683825 54470117446467706565762869)
          ·
            refine ⟨5106573510606347490540269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54470117446467706565762869 5106573510606347490540269)
            ·
              refine ⟨1914965066477380308952601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5106573510606347490540269 1914965066477380308952601)
              ·
                refine ⟨1436223799858035231714451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1914965066477380308952601 1436223799858035231714451)
                ·
                  refine ⟨2154335699787052847571677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436223799858035231714451 2154335699787052847571677)
                  ·
                    refine ⟨807875887420144817839379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2154335699787052847571677 807875887420144817839379)
                    ·
                      rfl

theorem cell22_2359999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 1, 3].length) (baseStart_2359999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2359999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2359999 prefixEnd_2359999 := by exact prefixLift 2359999
  have htrace : WordTrace (prefixWord ++ tailWord_2359999) baseStart_2359999 baseEnd_2359999 := by
    simpa [prefixWord, tailWord_2359999, baseEnd_2359999] using wordTrace_append hprefix tailTrace_2359999
  have hstable : (prefixWord ++ tailWord_2359999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359999).length < 2 ^ (prefixWord ++ tailWord_2359999).sum := by decide
  have hdescent : baseEnd_2359999 < baseStart_2359999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360012 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 5]
def baseStart_2360012 : Nat := 118140960795 + 2360012 * 2 ^ 59
def prefixEnd_2360012 : Nat := 4983230072969 + 3 ^ 40 * 2360012 * 2
def baseEnd_2360012 : Nat := 269293445861939039088113

theorem tailTrace_2360012 : CollatzResearch.WordTrace tailWord_2360012 prefixEnd_2360012 269293445861939039088113 := by
  unfold tailWord_2360012
  simp only [CollatzResearch.WordTrace]
  refine ⟨43038354563043528402813145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57384472750724704537084193 43038354563043528402813145)
  ·
    refine ⟨32278765922282646302109859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43038354563043528402813145 32278765922282646302109859)
    ·
      refine ⟨48418148883423969453164789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32278765922282646302109859 48418148883423969453164789)
      ·
        refine ⟨4539201457820997136234199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48418148883423969453164789 4539201457820997136234199)
        ·
          refine ⟨6808802186731495704351299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539201457820997136234199 6808802186731495704351299)
          ·
            refine ⟨10213203280097243556526949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808802186731495704351299 10213203280097243556526949)
            ·
              refine ⟨1914975615018233166848803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10213203280097243556526949 1914975615018233166848803)
              ·
                refine ⟨2872463422527349750273205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914975615018233166848803 2872463422527349750273205)
                ·
                  refine ⟨269293445861939039088113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2872463422527349750273205 269293445861939039088113)
                  ·
                    rfl

theorem cell22_2360012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 5].length) (baseStart_2360012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360012 prefixEnd_2360012 := by exact prefixLift 2360012
  have htrace : WordTrace (prefixWord ++ tailWord_2360012) baseStart_2360012 baseEnd_2360012 := by
    simpa [prefixWord, tailWord_2360012, baseEnd_2360012] using wordTrace_append hprefix tailTrace_2360012
  have hstable : (prefixWord ++ tailWord_2360012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360012).length < 2 ^ (prefixWord ++ tailWord_2360012).sum := by decide
  have hdescent : baseEnd_2360012 < baseStart_2360012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360072 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 2, 3]
def baseStart_2360072 : Nat := 118140960795 + 2360072 * 2 ^ 59
def prefixEnd_2360072 : Nat := 4983230072969 + 3 ^ 40 * 2360072 * 2
def baseEnd_2360072 : Nat := 807900876811996960764155

theorem tailTrace_2360072 : CollatzResearch.WordTrace tailWord_2360072 prefixEnd_2360072 807900876811996960764155 := by
  unfold tailWord_2360072
  simp only [CollatzResearch.WordTrace]
  refine ⟨43039448752934843526405235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57385931670579791368540313 43039448752934843526405235)
  ·
    refine ⟨64559173129402265289607853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43039448752934843526405235 64559173129402265289607853)
    ·
      refine ⟨24209689923525849483602945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64559173129402265289607853 24209689923525849483602945)
      ·
        refine ⟨18157267442644387112702209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24209689923525849483602945 18157267442644387112702209)
        ·
          refine ⟨13617950581983290334526657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18157267442644387112702209 13617950581983290334526657)
          ·
            refine ⟨10213462936487467750894993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13617950581983290334526657 10213462936487467750894993)
            ·
              refine ⟨7660097202365600813171245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10213462936487467750894993 7660097202365600813171245)
              ·
                refine ⟨2872536450887100304939217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7660097202365600813171245 2872536450887100304939217)
                ·
                  refine ⟨2154402338165325228704413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2872536450887100304939217 2154402338165325228704413)
                  ·
                    refine ⟨807900876811996960764155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2154402338165325228704413 807900876811996960764155)
                    ·
                      rfl

theorem cell22_2360072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_2360072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360072 prefixEnd_2360072 := by exact prefixLift 2360072
  have htrace : WordTrace (prefixWord ++ tailWord_2360072) baseStart_2360072 baseEnd_2360072 := by
    simpa [prefixWord, tailWord_2360072, baseEnd_2360072] using wordTrace_append hprefix tailTrace_2360072
  have hstable : (prefixWord ++ tailWord_2360072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360072).length < 2 ^ (prefixWord ++ tailWord_2360072).sum := by decide
  have hdescent : baseEnd_2360072 < baseStart_2360072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360085 : List Nat := [1, 3, 2, 1, 2, 2, 5, 6]
def baseStart_2360085 : Nat := 118140960795 + 2360085 * 2 ^ 59
def prefixEnd_2360085 : Nat := 4983230072969 + 3 ^ 40 * 2360085 * 2
def baseEnd_2360085 : Nat := 89767258553074362243235

theorem tailTrace_2360085 : CollatzResearch.WordTrace tailWord_2360085 prefixEnd_2360085 89767258553074362243235 := by
  unfold tailWord_2360085
  simp only [CollatzResearch.WordTrace]
  refine ⟨86079371654822590273033709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57386247769881726848689139 86079371654822590273033709)
  ·
    refine ⟨32279764370558471352387641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86079371654822590273033709 32279764370558471352387641)
    ·
      refine ⟨24209823277918853514290731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32279764370558471352387641 24209823277918853514290731)
      ·
        refine ⟨36314734916878280271436097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24209823277918853514290731 36314734916878280271436097)
        ·
          refine ⟨27236051187658710203577073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36314734916878280271436097 27236051187658710203577073)
          ·
            refine ⟨20427038390744032652682805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27236051187658710203577073 20427038390744032652682805)
            ·
              refine ⟨1915034849132253061189013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20427038390744032652682805 1915034849132253061189013)
              ·
                refine ⟨89767258553074362243235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1915034849132253061189013 89767258553074362243235)
                ·
                  rfl

theorem cell22_2360085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 6].length) (baseStart_2360085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360085 prefixEnd_2360085 := by exact prefixLift 2360085
  have htrace : WordTrace (prefixWord ++ tailWord_2360085) baseStart_2360085 baseEnd_2360085 := by
    simpa [prefixWord, tailWord_2360085, baseEnd_2360085] using wordTrace_append hprefix tailTrace_2360085
  have hstable : (prefixWord ++ tailWord_2360085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360085).length < 2 ^ (prefixWord ++ tailWord_2360085).sum := by decide
  have hdescent : baseEnd_2360085 < baseStart_2360085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360093 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_2360093 : Nat := 118140960795 + 2360093 * 2 ^ 59
def prefixEnd_2360093 : Nat := 4983230072969 + 3 ^ 40 * 2360093 * 2
def baseEnd_2360093 : Nat := 807908065541159905989091

theorem tailTrace_2360093 : CollatzResearch.WordTrace tailWord_2360093 prefixEnd_2360093 807908065541159905989091 := by
  unfold tailWord_2360093
  simp only [CollatzResearch.WordTrace]
  refine ⟨86079663438793607639324933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57386442292529071759549955 86079663438793607639324933)
  ·
    refine ⟨16139936894773801432373425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86079663438793607639324933 16139936894773801432373425)
    ·
      refine ⟨12104952671080351074280069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16139936894773801432373425 12104952671080351074280069)
      ·
        refine ⟨2269678625827565826427513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12104952671080351074280069 2269678625827565826427513)
        ·
          refine ⟨1702258969370674369820635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2269678625827565826427513 1702258969370674369820635)
          ·
            refine ⟨2553388454056011554730953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1702258969370674369820635 2553388454056011554730953)
            ·
              refine ⟨1915041340542008666048215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2553388454056011554730953 1915041340542008666048215)
              ·
                refine ⟨2872562010813012999072323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1915041340542008666048215 2872562010813012999072323)
                ·
                  refine ⟨4308843016219519498608485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2872562010813012999072323 4308843016219519498608485)
                  ·
                    refine ⟨807908065541159905989091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4308843016219519498608485 807908065541159905989091)
                    ·
                      rfl

theorem cell22_2360093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_2360093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360093 prefixEnd_2360093 := by exact prefixLift 2360093
  have htrace : WordTrace (prefixWord ++ tailWord_2360093) baseStart_2360093 baseEnd_2360093 := by
    simpa [prefixWord, tailWord_2360093, baseEnd_2360093] using wordTrace_append hprefix tailTrace_2360093
  have hstable : (prefixWord ++ tailWord_2360093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360093).length < 2 ^ (prefixWord ++ tailWord_2360093).sum := by decide
  have hdescent : baseEnd_2360093 < baseStart_2360093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360117 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 3, 3]
def baseStart_2360117 : Nat := 118140960795 + 2360117 * 2 ^ 59
def prefixEnd_2360117 : Nat := 4983230072969 + 3 ^ 40 * 2360117 * 2
def baseEnd_2360117 : Nat := 807916281231631843389017

theorem tailTrace_2360117 : CollatzResearch.WordTrace tailWord_2360117 prefixEnd_2360117 807916281231631843389017 := by
  unfold tailWord_2360117
  simp only [CollatzResearch.WordTrace]
  refine ⟨86080538790706659738198605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57387025860471106492132403 86080538790706659738198605)
  ·
    refine ⟨32280202046514997401824477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86080538790706659738198605 32280202046514997401824477)
    ·
      refine ⟨12105075767443124025684179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32280202046514997401824477 12105075767443124025684179)
      ·
        refine ⟨18157613651164686038526269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12105075767443124025684179 18157613651164686038526269)
        ·
          refine ⟨6809105119186757264447351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18157613651164686038526269 6809105119186757264447351)
          ·
            refine ⟨10213657678780135896671027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809105119186757264447351 10213657678780135896671027)
            ·
              refine ⟨15320486518170203845006541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10213657678780135896671027 15320486518170203845006541)
              ·
                refine ⟨5745182444313826441877453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15320486518170203845006541 5745182444313826441877453)
                ·
                  refine ⟨2154443416617684915704045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5745182444313826441877453 2154443416617684915704045)
                  ·
                    refine ⟨807916281231631843389017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2154443416617684915704045 807916281231631843389017)
                    ·
                      rfl

theorem cell22_2360117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_2360117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360117 prefixEnd_2360117 := by exact prefixLift 2360117
  have htrace : WordTrace (prefixWord ++ tailWord_2360117) baseStart_2360117 baseEnd_2360117 := by
    simpa [prefixWord, tailWord_2360117, baseEnd_2360117] using wordTrace_append hprefix tailTrace_2360117
  have hstable : (prefixWord ++ tailWord_2360117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360117).length < 2 ^ (prefixWord ++ tailWord_2360117).sum := by decide
  have hdescent : baseEnd_2360117 < baseStart_2360117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360143 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 4, 8]
def baseStart_2360143 : Nat := 118140960795 + 2360143 * 2 ^ 59
def prefixEnd_2360143 : Nat := 4983230072969 + 3 ^ 40 * 2360143 * 2
def baseEnd_2360143 : Nat := 807925181562976442238937

theorem tailTrace_2360143 : CollatzResearch.WordTrace tailWord_2360143 prefixEnd_2360143 807925181562976442238937 := by
  unfold tailWord_2360143
  simp only [CollatzResearch.WordTrace]
  refine ⟨86081487088612466178645083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57387658059074977452430055 86081487088612466178645083)
  ·
    refine ⟨129122230632918699267967625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86081487088612466178645083 129122230632918699267967625)
    ·
      refine ⟨96841672974689024450975719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129122230632918699267967625 96841672974689024450975719)
      ·
        refine ⟨145262509462033536676463579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96841672974689024450975719 145262509462033536676463579)
        ·
          refine ⟨217893764193050305014695369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145262509462033536676463579 217893764193050305014695369)
          ·
            refine ⟨163420323144787728761021527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217893764193050305014695369 163420323144787728761021527)
            ·
              refine ⟨245130484717181593141532291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163420323144787728761021527 245130484717181593141532291)
              ·
                refine ⟨367695727075772389712298437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245130484717181593141532291 367695727075772389712298437)
                ·
                  refine ⟨68942948826707323071055957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 367695727075772389712298437 68942948826707323071055957)
                  ·
                    refine ⟨807925181562976442238937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68942948826707323071055957 807925181562976442238937)
                    ·
                      rfl

theorem cell22_2360143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_2360143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360143 prefixEnd_2360143 := by exact prefixLift 2360143
  have htrace : WordTrace (prefixWord ++ tailWord_2360143) baseStart_2360143 baseEnd_2360143 := by
    simpa [prefixWord, tailWord_2360143, baseEnd_2360143] using wordTrace_append hprefix tailTrace_2360143
  have hstable : (prefixWord ++ tailWord_2360143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360143).length < 2 ^ (prefixWord ++ tailWord_2360143).sum := by decide
  have hdescent : baseEnd_2360143 < baseStart_2360143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360151 : List Nat := [1, 1, 3, 2, 4, 3, 1, 3, 1, 3]
def baseStart_2360151 : Nat := 118140960795 + 2360151 * 2 ^ 59
def prefixEnd_2360151 : Nat := 4983230072969 + 3 ^ 40 * 2360151 * 2
def baseEnd_2360151 : Nat := 807927920126467088038913

theorem tailTrace_2360151 : CollatzResearch.WordTrace tailWord_2360151 prefixEnd_2360151 807927920126467088038913 := by
  unfold tailWord_2360151
  simp only [CollatzResearch.WordTrace]
  refine ⟨86081778872583483544936307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57387852581722322363290871 86081778872583483544936307)
  ·
    refine ⟨129122668308875225317404461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86081778872583483544936307 129122668308875225317404461)
    ·
      refine ⟨48421000615828209494026673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129122668308875225317404461 48421000615828209494026673)
      ·
        refine ⟨36315750461871157120520005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48421000615828209494026673 36315750461871157120520005)
        ·
          refine ⟨6809203211600841960097501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36315750461871157120520005 6809203211600841960097501)
          ·
            refine ⟨2553451204350315735036563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6809203211600841960097501 2553451204350315735036563)
            ·
              refine ⟨3830176806525473602554845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553451204350315735036563 3830176806525473602554845)
              ·
                refine ⟨1436316302447052600958067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3830176806525473602554845 1436316302447052600958067)
                ·
                  refine ⟨2154474453670578901437101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436316302447052600958067 2154474453670578901437101)
                  ·
                    refine ⟨807927920126467088038913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2154474453670578901437101 807927920126467088038913)
                    ·
                      rfl

theorem cell22_2360151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_2360151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360151 prefixEnd_2360151 := by exact prefixLift 2360151
  have htrace : WordTrace (prefixWord ++ tailWord_2360151) baseStart_2360151 baseEnd_2360151 := by
    simpa [prefixWord, tailWord_2360151, baseEnd_2360151] using wordTrace_append hprefix tailTrace_2360151
  have hstable : (prefixWord ++ tailWord_2360151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360151).length < 2 ^ (prefixWord ++ tailWord_2360151).sum := by decide
  have hdescent : baseEnd_2360151 < baseStart_2360151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360220 : List Nat := [2, 2, 3, 3, 12]
def baseStart_2360220 : Nat := 118140960795 + 2360220 * 2 ^ 59
def prefixEnd_2360220 : Nat := 4983230072969 + 3 ^ 40 * 2360220 * 2
def baseEnd_2360220 : Nat := 3324903457763678634007

theorem tailTrace_2360220 : CollatzResearch.WordTrace tailWord_2360220 prefixEnd_2360220 3324903457763678634007 := by
  unfold tailWord_2360220
  simp only [CollatzResearch.WordTrace]
  refine ⟨43042147754666754164599057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57389530339555672219465409 43042147754666754164599057)
  ·
    refine ⟨32281610816000065623449293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43042147754666754164599057 32281610816000065623449293)
    ·
      refine ⟨12105604056000024608793485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32281610816000065623449293 12105604056000024608793485)
      ·
        refine ⟨4539601521000009228297557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12105604056000024608793485 4539601521000009228297557)
        ·
          refine ⟨3324903457763678634007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4539601521000009228297557 3324903457763678634007)
          ·
            rfl

theorem cell22_2360220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 12].length) (baseStart_2360220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360220 prefixEnd_2360220 := by exact prefixLift 2360220
  have htrace : WordTrace (prefixWord ++ tailWord_2360220) baseStart_2360220 baseEnd_2360220 := by
    simpa [prefixWord, tailWord_2360220, baseEnd_2360220] using wordTrace_append hprefix tailTrace_2360220
  have hstable : (prefixWord ++ tailWord_2360220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360220).length < 2 ^ (prefixWord ++ tailWord_2360220).sum := by decide
  have hdescent : baseEnd_2360220 < baseStart_2360220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360226 : List Nat := [3, 3, 1, 2, 2, 1, 4, 2, 4]
def baseStart_2360226 : Nat := 118140960795 + 2360226 * 2 ^ 59
def prefixEnd_2360226 : Nat := 4983230072969 + 3 ^ 40 * 2360226 * 2
def baseEnd_2360226 : Nat := 269317864719730630804561

theorem tailTrace_2360226 : CollatzResearch.WordTrace tailWord_2360226 prefixEnd_2360226 269317864719730630804561 := by
  unfold tailWord_2360226
  simp only [CollatzResearch.WordTrace]
  refine ⟨21521128586827942838479133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57389676231541180902611021 21521128586827942838479133)
  ·
    refine ⟨8070423220060478564429675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21521128586827942838479133 8070423220060478564429675)
    ·
      refine ⟨12105634830090717846644513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8070423220060478564429675 12105634830090717846644513)
      ·
        refine ⟨9079226122568038384983385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12105634830090717846644513 9079226122568038384983385)
        ·
          refine ⟨6809419591926028788737539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9079226122568038384983385 6809419591926028788737539)
          ·
            refine ⟨10214129387889043183106309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809419591926028788737539 10214129387889043183106309)
            ·
              refine ⟨1915149260229195596832433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10214129387889043183106309 1915149260229195596832433)
              ·
                refine ⟨1436361945171896697624325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1915149260229195596832433 1436361945171896697624325)
                ·
                  refine ⟨269317864719730630804561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1436361945171896697624325 269317864719730630804561)
                  ·
                    rfl

theorem cell22_2360226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_2360226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360226 prefixEnd_2360226 := by exact prefixLift 2360226
  have htrace : WordTrace (prefixWord ++ tailWord_2360226) baseStart_2360226 baseEnd_2360226 := by
    simpa [prefixWord, tailWord_2360226, baseEnd_2360226] using wordTrace_append hprefix tailTrace_2360226
  have hstable : (prefixWord ++ tailWord_2360226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360226).length < 2 ^ (prefixWord ++ tailWord_2360226).sum := by decide
  have hdescent : baseEnd_2360226 < baseStart_2360226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360250 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_2360250 : Nat := 118140960795 + 2360250 * 2 ^ 59
def prefixEnd_2360250 : Nat := 4983230072969 + 3 ^ 40 * 2360250 * 2
def baseEnd_2360250 : Nat := 807961809849663829813609

theorem tailTrace_2360250 : CollatzResearch.WordTrace tailWord_2360250 prefixEnd_2360250 807961809849663829813609 := by
  unfold tailWord_2360250
  simp only [CollatzResearch.WordTrace]
  refine ⟨21521347424806205863197551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57390259799483215635193469 21521347424806205863197551)
  ·
    refine ⟨32282021137209308794796327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21521347424806205863197551 32282021137209308794796327)
    ·
      refine ⟨48423031705813963192194491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32282021137209308794796327 48423031705813963192194491)
      ·
        refine ⟨72634547558720944788291737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48423031705813963192194491 72634547558720944788291737)
        ·
          refine ⟨54475910669040708591218803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72634547558720944788291737 54475910669040708591218803)
          ·
            refine ⟨81713866003561062886828205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54475910669040708591218803 81713866003561062886828205)
            ·
              refine ⟨30642699751335398582560577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81713866003561062886828205 30642699751335398582560577)
              ·
                refine ⟨22982024813501548936920433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30642699751335398582560577 22982024813501548936920433)
                ·
                  refine ⟨17236518610126161702690325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22982024813501548936920433 17236518610126161702690325)
                  ·
                    refine ⟨807961809849663829813609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17236518610126161702690325 807961809849663829813609)
                    ·
                      rfl

theorem cell22_2360250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_2360250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360250 prefixEnd_2360250 := by exact prefixLift 2360250
  have htrace : WordTrace (prefixWord ++ tailWord_2360250) baseStart_2360250 baseEnd_2360250 := by
    simpa [prefixWord, tailWord_2360250, baseEnd_2360250] using wordTrace_append hprefix tailTrace_2360250
  have hstable : (prefixWord ++ tailWord_2360250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360250).length < 2 ^ (prefixWord ++ tailWord_2360250).sum := by decide
  have hdescent : baseEnd_2360250 < baseStart_2360250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360282 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 7]
def baseStart_2360282 : Nat := 118140960795 + 2360282 * 2 ^ 59
def prefixEnd_2360282 : Nat := 4983230072969 + 3 ^ 40 * 2360282 * 2
def baseEnd_2360282 : Nat := 269324254701208804337837

theorem tailTrace_2360282 : CollatzResearch.WordTrace tailWord_2360282 prefixEnd_2360282 269324254701208804337837 := by
  unfold tailWord_2360282
  simp only [CollatzResearch.WordTrace]
  refine ⟨21521639208777223229488775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57391037890072595278636733 21521639208777223229488775)
  ·
    refine ⟨32282458813165834844233163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21521639208777223229488775 32282458813165834844233163)
    ·
      refine ⟨48423688219748752266349745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32282458813165834844233163 48423688219748752266349745)
      ·
        refine ⟨36317766164811564199762309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48423688219748752266349745 36317766164811564199762309)
        ·
          refine ⟨6809581155902168287455433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36317766164811564199762309 6809581155902168287455433)
          ·
            refine ⟨5107185866926626215591575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6809581155902168287455433 5107185866926626215591575)
            ·
              refine ⟨7660778800389939323387363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5107185866926626215591575 7660778800389939323387363)
              ·
                refine ⟨11491168200584908985081045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7660778800389939323387363 11491168200584908985081045)
                ·
                  refine ⟨269324254701208804337837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11491168200584908985081045 269324254701208804337837)
                  ·
                    rfl

theorem cell22_2360282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_2360282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360282 prefixEnd_2360282 := by exact prefixLift 2360282
  have htrace : WordTrace (prefixWord ++ tailWord_2360282) baseStart_2360282 baseEnd_2360282 := by
    simpa [prefixWord, tailWord_2360282, baseEnd_2360282] using wordTrace_append hprefix tailTrace_2360282
  have hstable : (prefixWord ++ tailWord_2360282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360282).length < 2 ^ (prefixWord ++ tailWord_2360282).sum := by decide
  have hdescent : baseEnd_2360282 < baseStart_2360282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360344 : List Nat := [2, 1, 2, 3, 2, 4, 1, 1, 6]
def baseStart_2360344 : Nat := 118140960795 + 2360344 * 2 ^ 59
def prefixEnd_2360344 : Nat := 4983230072969 + 3 ^ 40 * 2360344 * 2
def baseEnd_2360344 : Nat := 269331329323559639321107

theorem tailTrace_2360344 : CollatzResearch.WordTrace tailWord_2360344 prefixEnd_2360344 269331329323559639321107 := by
  unfold tailWord_2360344
  simp only [CollatzResearch.WordTrace]
  refine ⟨43044409080442138753356043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57392545440589518337808057 43044409080442138753356043)
  ·
    refine ⟨64566613620663208130034065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43044409080442138753356043 64566613620663208130034065)
    ·
      refine ⟨48424960215497406097525549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64566613620663208130034065 48424960215497406097525549)
      ·
        refine ⟨18159360080811527286572081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48424960215497406097525549 18159360080811527286572081)
        ·
          refine ⟨13619520060608645464929061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18159360080811527286572081 13619520060608645464929061)
          ·
            refine ⟨2553660011364121024674199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13619520060608645464929061 2553660011364121024674199)
            ·
              refine ⟨3830490017046181537011299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553660011364121024674199 3830490017046181537011299)
              ·
                refine ⟨5745735025569272305516949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830490017046181537011299 5745735025569272305516949)
                ·
                  refine ⟨269331329323559639321107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5745735025569272305516949 269331329323559639321107)
                  ·
                    rfl

theorem cell22_2360344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 6].length) (baseStart_2360344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360344 prefixEnd_2360344 := by exact prefixLift 2360344
  have htrace : WordTrace (prefixWord ++ tailWord_2360344) baseStart_2360344 baseEnd_2360344 := by
    simpa [prefixWord, tailWord_2360344, baseEnd_2360344] using wordTrace_append hprefix tailTrace_2360344
  have hstable : (prefixWord ++ tailWord_2360344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360344).length < 2 ^ (prefixWord ++ tailWord_2360344).sum := by decide
  have hdescent : baseEnd_2360344 < baseStart_2360344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360357 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_2360357 : Nat := 118140960795 + 2360357 * 2 ^ 59
def prefixEnd_2360357 : Nat := 4983230072969 + 3 ^ 40 * 2360357 * 2
def baseEnd_2360357 : Nat := 807998438136351217388281

theorem tailTrace_2360357 : CollatzResearch.WordTrace tailWord_2360357 prefixEnd_2360357 807998438136351217388281 := by
  unfold tailWord_2360357
  simp only [CollatzResearch.WordTrace]
  refine ⟨86089292309837180726935325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57392861539891453817956883 86089292309837180726935325)
  ·
    refine ⟨32283484616188942772600747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86089292309837180726935325 32283484616188942772600747)
    ·
      refine ⟨48425226924283414158901121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32283484616188942772600747 48425226924283414158901121)
      ·
        refine ⟨36318920193212560619175841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48425226924283414158901121 36318920193212560619175841)
        ·
          refine ⟨27239190144909420464381881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36318920193212560619175841 27239190144909420464381881)
          ·
            refine ⟨20429392608682065348286411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27239190144909420464381881 20429392608682065348286411)
            ·
              refine ⟨30644088913023098022429617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20429392608682065348286411 30644088913023098022429617)
              ·
                refine ⟨22983066684767323516822213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30644088913023098022429617 22983066684767323516822213)
                ·
                  refine ⟨4309325003393873159404165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22983066684767323516822213 4309325003393873159404165)
                  ·
                    refine ⟨807998438136351217388281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4309325003393873159404165 807998438136351217388281)
                    ·
                      rfl

theorem cell22_2360357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_2360357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360357 prefixEnd_2360357 := by exact prefixLift 2360357
  have htrace : WordTrace (prefixWord ++ tailWord_2360357) baseStart_2360357 baseEnd_2360357 := by
    simpa [prefixWord, tailWord_2360357, baseEnd_2360357] using wordTrace_append hprefix tailTrace_2360357
  have hstable : (prefixWord ++ tailWord_2360357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360357).length < 2 ^ (prefixWord ++ tailWord_2360357).sum := by decide
  have hdescent : baseEnd_2360357 < baseStart_2360357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360432 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_2360432 : Nat := 118140960795 + 2360432 * 2 ^ 59
def prefixEnd_2360432 : Nat := 4983230072969 + 3 ^ 40 * 2360432 * 2
def baseEnd_2360432 : Nat := 808024112169076021763051

theorem tailTrace_2360432 : CollatzResearch.WordTrace tailWord_2360432 prefixEnd_2360432 808024112169076021763051 := by
  unfold tailWord_2360432
  simp only [CollatzResearch.WordTrace]
  refine ⟨43046013892282734267957775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57394685189710312357277033 43046013892282734267957775)
  ·
    refine ⟨64569020838424101401936663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43046013892282734267957775 64569020838424101401936663)
    ·
      refine ⟨96853531257636152102904995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64569020838424101401936663 96853531257636152102904995)
      ·
        refine ⟨145280296886454228154357493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96853531257636152102904995 145280296886454228154357493)
        ·
          refine ⟨13620027833105083889471015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145280296886454228154357493 13620027833105083889471015)
          ·
            refine ⟨20430041749657625834206523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13620027833105083889471015 20430041749657625834206523)
            ·
              refine ⟨30645062624486438751309785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20430041749657625834206523 30645062624486438751309785)
              ·
                refine ⟨22983796968364829063482339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30645062624486438751309785 22983796968364829063482339)
                ·
                  refine ⟨34475695452547243595223509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22983796968364829063482339 34475695452547243595223509)
                  ·
                    refine ⟨808024112169076021763051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34475695452547243595223509 808024112169076021763051)
                    ·
                      rfl

theorem cell22_2360432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_2360432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360432 prefixEnd_2360432 := by exact prefixLift 2360432
  have htrace : WordTrace (prefixWord ++ tailWord_2360432) baseStart_2360432 baseEnd_2360432 := by
    simpa [prefixWord, tailWord_2360432, baseEnd_2360432] using wordTrace_append hprefix tailTrace_2360432
  have hstable : (prefixWord ++ tailWord_2360432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360432).length < 2 ^ (prefixWord ++ tailWord_2360432).sum := by decide
  have hdescent : baseEnd_2360432 < baseStart_2360432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360449 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 2, 5]
def baseStart_2360449 : Nat := 118140960795 + 2360449 * 2 ^ 59
def prefixEnd_2360449 : Nat := 4983230072969 + 3 ^ 40 * 2360449 * 2
def baseEnd_2360449 : Nat := 808029931616493644087999

theorem tailTrace_2360449 : CollatzResearch.WordTrace tailWord_2360449 prefixEnd_2360449 808029931616493644087999 := by
  unfold tailWord_2360449
  simp only [CollatzResearch.WordTrace]
  refine ⟨86092647825503880439284401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57395098550335920292856267 86092647825503880439284401)
  ·
    refine ⟨64569485869127910329463301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86092647825503880439284401 64569485869127910329463301)
    ·
      refine ⟨12106778600461483186774369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64569485869127910329463301 12106778600461483186774369)
      ·
        refine ⟨9080083950346112390080777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12106778600461483186774369 9080083950346112390080777)
        ·
          refine ⟨6810062962759584292560583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9080083950346112390080777 6810062962759584292560583)
          ·
            refine ⟨10215094444139376438840875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6810062962759584292560583 10215094444139376438840875)
            ·
              refine ⟨15322641666209064658261313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10215094444139376438840875 15322641666209064658261313)
              ·
                refine ⟨11491981249656798493695985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15322641666209064658261313 11491981249656798493695985)
                ·
                  refine ⟨8618985937242598870271989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11491981249656798493695985 8618985937242598870271989)
                  ·
                    refine ⟨808029931616493644087999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8618985937242598870271989 808029931616493644087999)
                    ·
                      rfl

theorem cell22_2360449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_2360449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360449 prefixEnd_2360449 := by exact prefixLift 2360449
  have htrace : WordTrace (prefixWord ++ tailWord_2360449) baseStart_2360449 baseEnd_2360449 := by
    simpa [prefixWord, tailWord_2360449, baseEnd_2360449] using wordTrace_append hprefix tailTrace_2360449
  have hstable : (prefixWord ++ tailWord_2360449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360449).length < 2 ^ (prefixWord ++ tailWord_2360449).sum := by decide
  have hdescent : baseEnd_2360449 < baseStart_2360449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360481 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 1, 4]
def baseStart_2360481 : Nat := 118140960795 + 2360481 * 2 ^ 59
def prefixEnd_2360481 : Nat := 4983230072969 + 3 ^ 40 * 2360481 * 2
def baseEnd_2360481 : Nat := 808040885870456227287901

theorem tailTrace_2360481 : CollatzResearch.WordTrace tailWord_2360481 prefixEnd_2360481 808040885870456227287901 := by
  unfold tailWord_2360481
  simp only [CollatzResearch.WordTrace]
  refine ⟨86093814961387949904449297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57395876640925299936299531 86093814961387949904449297)
  ·
    refine ⟨64570361221040962428336973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86093814961387949904449297 64570361221040962428336973)
    ·
      refine ⟨24213885457890360910626365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64570361221040962428336973 24213885457890360910626365)
      ·
        refine ⟨9080207046708885341484887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24213885457890360910626365 9080207046708885341484887)
        ·
          refine ⟨13620310570063328012227331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9080207046708885341484887 13620310570063328012227331)
          ·
            refine ⟨20430465855094992018340997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13620310570063328012227331 20430465855094992018340997)
            ·
              refine ⟨3830712347830311003438937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20430465855094992018340997 3830712347830311003438937)
              ·
                refine ⟨2873034260872733252579203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3830712347830311003438937 2873034260872733252579203)
                ·
                  refine ⟨4309551391309099878868805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2873034260872733252579203 4309551391309099878868805)
                  ·
                    refine ⟨808040885870456227287901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4309551391309099878868805 808040885870456227287901)
                    ·
                      rfl

theorem cell22_2360481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_2360481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360481 prefixEnd_2360481 := by exact prefixLift 2360481
  have htrace : WordTrace (prefixWord ++ tailWord_2360481) baseStart_2360481 baseEnd_2360481 := by
    simpa [prefixWord, tailWord_2360481, baseEnd_2360481] using wordTrace_append hprefix tailTrace_2360481
  have hstable : (prefixWord ++ tailWord_2360481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360481).length < 2 ^ (prefixWord ++ tailWord_2360481).sum := by decide
  have hdescent : baseEnd_2360481 < baseStart_2360481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360509 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_2360509 : Nat := 118140960795 + 2360509 * 2 ^ 59
def prefixEnd_2360509 : Nat := 4983230072969 + 3 ^ 40 * 2360509 * 2
def baseEnd_2360509 : Nat := 808050470842673487587815

theorem tailTrace_2360509 : CollatzResearch.WordTrace tailWord_2360509 prefixEnd_2360509 808050470842673487587815 := by
  unfold tailWord_2360509
  simp only [CollatzResearch.WordTrace]
  refine ⟨86094836205286510686468581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57396557470191007124312387 86094836205286510686468581)
  ·
    refine ⟨16142781788491220753712859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86094836205286510686468581 16142781788491220753712859)
    ·
      refine ⟨24214172682736831130569289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16142781788491220753712859 24214172682736831130569289)
      ·
        refine ⟨18160629512052623347926967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24214172682736831130569289 18160629512052623347926967)
        ·
          refine ⟨27240944268078935021890451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18160629512052623347926967 27240944268078935021890451)
          ·
            refine ⟨40861416402118402532835677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27240944268078935021890451 40861416402118402532835677)
            ·
              refine ⟨15323031150794400949813379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40861416402118402532835677 15323031150794400949813379)
              ·
                refine ⟨22984546726191601424720069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15323031150794400949813379 22984546726191601424720069)
                ·
                  refine ⟨4309602511160925267135013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22984546726191601424720069 4309602511160925267135013)
                  ·
                    refine ⟨808050470842673487587815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4309602511160925267135013 808050470842673487587815)
                    ·
                      rfl

theorem cell22_2360509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_2360509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360509 prefixEnd_2360509 := by exact prefixLift 2360509
  have htrace : WordTrace (prefixWord ++ tailWord_2360509) baseStart_2360509 baseEnd_2360509 := by
    simpa [prefixWord, tailWord_2360509, baseEnd_2360509] using wordTrace_append hprefix tailTrace_2360509
  have hstable : (prefixWord ++ tailWord_2360509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360509).length < 2 ^ (prefixWord ++ tailWord_2360509).sum := by decide
  have hdescent : baseEnd_2360509 < baseStart_2360509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360513 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 6]
def baseStart_2360513 : Nat := 118140960795 + 2360513 * 2 ^ 59
def prefixEnd_2360513 : Nat := 4983230072969 + 3 ^ 40 * 2360513 * 2
def baseEnd_2360513 : Nat := 269350613374806270162601

theorem tailTrace_2360513 : CollatzResearch.WordTrace tailWord_2360513 prefixEnd_2360513 269350613374806270162601 := by
  unfold tailWord_2360513
  simp only [CollatzResearch.WordTrace]
  refine ⟨86094982097272019369614193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57396654731514679579742795 86094982097272019369614193)
  ·
    refine ⟨64571236572954014527210645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86094982097272019369614193 64571236572954014527210645)
    ·
      refine ⟨3026776714357219430962999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64571236572954014527210645 3026776714357219430962999)
      ·
        refine ⟨4540165071535829146444499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3026776714357219430962999 4540165071535829146444499)
        ·
          refine ⟨6810247607303743719666749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4540165071535829146444499 6810247607303743719666749)
          ·
            refine ⟨2553842852738903894875031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6810247607303743719666749 2553842852738903894875031)
            ·
              refine ⟨3830764279108355842312547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553842852738903894875031 3830764279108355842312547)
              ·
                refine ⟨5746146418662533763468821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830764279108355842312547 5746146418662533763468821)
                ·
                  refine ⟨269350613374806270162601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5746146418662533763468821 269350613374806270162601)
                  ·
                    rfl

theorem cell22_2360513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 6].length) (baseStart_2360513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360513 prefixEnd_2360513 := by exact prefixLift 2360513
  have htrace : WordTrace (prefixWord ++ tailWord_2360513) baseStart_2360513 baseEnd_2360513 := by
    simpa [prefixWord, tailWord_2360513, baseEnd_2360513] using wordTrace_append hprefix tailTrace_2360513
  have hstable : (prefixWord ++ tailWord_2360513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360513).length < 2 ^ (prefixWord ++ tailWord_2360513).sum := by decide
  have hdescent : baseEnd_2360513 < baseStart_2360513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360532 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_2360532 : Nat := 118140960795 + 2360532 * 2 ^ 59
def prefixEnd_2360532 : Nat := 4983230072969 + 3 ^ 40 * 2360532 * 2
def baseEnd_2360532 : Nat := 808058344212709094262745

theorem tailTrace_2360532 : CollatzResearch.WordTrace tailWord_2360532 prefixEnd_2360532 808058344212709094262745 := by
  unfold tailWord_2360532
  simp only [CollatzResearch.WordTrace]
  refine ⟨43047837542101592807277925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57397116722802123743037233 43047837542101592807277925)
  ·
    refine ⟨8071469539144048651364611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43047837542101592807277925 8071469539144048651364611)
    ·
      refine ⟨12107204308716072977046917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8071469539144048651364611 12107204308716072977046917)
      ·
        refine ⟨2270100807884263683196297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12107204308716072977046917 2270100807884263683196297)
        ·
          refine ⟨1702575605913197762397223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2270100807884263683196297 1702575605913197762397223)
          ·
            refine ⟨2553863408869796643595835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1702575605913197762397223 2553863408869796643595835)
            ·
              refine ⟨3830795113304694965393753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553863408869796643595835 3830795113304694965393753)
              ·
                refine ⟨2873096334978521224045315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3830795113304694965393753 2873096334978521224045315)
                ·
                  refine ⟨4309644502467781836067973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2873096334978521224045315 4309644502467781836067973)
                  ·
                    refine ⟨808058344212709094262745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4309644502467781836067973 808058344212709094262745)
                    ·
                      rfl

theorem cell22_2360532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_2360532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360532 prefixEnd_2360532 := by exact prefixLift 2360532
  have htrace : WordTrace (prefixWord ++ tailWord_2360532) baseStart_2360532 baseEnd_2360532 := by
    simpa [prefixWord, tailWord_2360532, baseEnd_2360532] using wordTrace_append hprefix tailTrace_2360532
  have hstable : (prefixWord ++ tailWord_2360532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360532).length < 2 ^ (prefixWord ++ tailWord_2360532).sum := by decide
  have hdescent : baseEnd_2360532 < baseStart_2360532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360659 : List Nat := [1, 1, 1, 2, 1, 1, 7, 8]
def baseStart_2360659 : Nat := 118140960795 + 2360659 * 2 ^ 59
def prefixEnd_2360659 : Nat := 4983230072969 + 3 ^ 40 * 2360659 * 2
def baseEnd_2360659 : Nat := 89789090989791455148595

theorem tailTrace_2360659 : CollatzResearch.WordTrace tailWord_2360659 prefixEnd_2360659 89789090989791455148595 := by
  unfold tailWord_2360659
  simp only [CollatzResearch.WordTrace]
  refine ⟨86100307154743086304429031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57400204769828724202952687 86100307154743086304429031)
  ·
    refine ⟨129150460732114629456643547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86100307154743086304429031 129150460732114629456643547)
    ·
      refine ⟨193725691098171944184965321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129150460732114629456643547 193725691098171944184965321)
      ·
        refine ⟨145294268323628958138723991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193725691098171944184965321 145294268323628958138723991)
        ·
          refine ⟨217941402485443437208085987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145294268323628958138723991 217941402485443437208085987)
          ·
            refine ⟨326912103728165155812128981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217941402485443437208085987 326912103728165155812128981)
            ·
              refine ⟨7662002431128870839346773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 326912103728165155812128981 7662002431128870839346773)
              ·
                refine ⟨89789090989791455148595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7662002431128870839346773 89789090989791455148595)
                ·
                  rfl

theorem cell22_2360659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 8].length) (baseStart_2360659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360659 prefixEnd_2360659 := by exact prefixLift 2360659
  have htrace : WordTrace (prefixWord ++ tailWord_2360659) baseStart_2360659 baseEnd_2360659 := by
    simpa [prefixWord, tailWord_2360659, baseEnd_2360659] using wordTrace_append hprefix tailTrace_2360659
  have hstable : (prefixWord ++ tailWord_2360659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360659).length < 2 ^ (prefixWord ++ tailWord_2360659).sum := by decide
  have hdescent : baseEnd_2360659 < baseStart_2360659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360661 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_2360661 : Nat := 118140960795 + 2360661 * 2 ^ 59
def prefixEnd_2360661 : Nat := 4983230072969 + 3 ^ 40 * 2360661 * 2
def baseEnd_2360661 : Nat := 808102503548995757787349

theorem tailTrace_2360661 : CollatzResearch.WordTrace tailWord_2360661 prefixEnd_2360661 808102503548995757787349 := by
  unfold tailWord_2360661
  simp only [CollatzResearch.WordTrace]
  refine ⟨86100380100735840646001837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57400253400490560430667891 86100380100735840646001837)
  ·
    refine ⟨32287642537775940242250689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86100380100735840646001837 32287642537775940242250689)
    ·
      refine ⟨24215731903331955181688017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32287642537775940242250689 24215731903331955181688017)
      ·
        refine ⟨18161798927498966386266013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24215731903331955181688017 18161798927498966386266013)
        ·
          refine ⟨6810674597812112394849755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18161798927498966386266013 6810674597812112394849755)
          ·
            refine ⟨10216011896718168592274633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6810674597812112394849755 10216011896718168592274633)
            ·
              refine ⟨7662008922538626444205975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10216011896718168592274633 7662008922538626444205975)
              ·
                refine ⟨11493013383807939666308963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7662008922538626444205975 11493013383807939666308963)
                ·
                  refine ⟨17239520075711909499463445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11493013383807939666308963 17239520075711909499463445)
                  ·
                    refine ⟨808102503548995757787349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17239520075711909499463445 808102503548995757787349)
                    ·
                      rfl

theorem cell22_2360661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_2360661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360661 prefixEnd_2360661 := by exact prefixLift 2360661
  have htrace : WordTrace (prefixWord ++ tailWord_2360661) baseStart_2360661 baseEnd_2360661 := by
    simpa [prefixWord, tailWord_2360661, baseEnd_2360661] using wordTrace_append hprefix tailTrace_2360661
  have hstable : (prefixWord ++ tailWord_2360661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360661).length < 2 ^ (prefixWord ++ tailWord_2360661).sum := by decide
  have hdescent : baseEnd_2360661 < baseStart_2360661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360676 : List Nat := [2, 3, 1, 1, 3, 4, 8]
def baseStart_2360676 : Nat := 118140960795 + 2360676 * 2 ^ 59
def prefixEnd_2360676 : Nat := 4983230072969 + 3 ^ 40 * 2360676 * 2
def baseEnd_2360676 : Nat := 29929912531686693283789

theorem tailTrace_2360676 : CollatzResearch.WordTrace tailWord_2360676 prefixEnd_2360676 29929912531686693283789 := by
  unfold tailWord_2360676
  simp only [CollatzResearch.WordTrace]
  refine ⟨43050463597840749103898941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57400618130454332138531921 43050463597840749103898941)
  ·
    refine ⟨16143923849190280913962103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43050463597840749103898941 16143923849190280913962103)
    ·
      refine ⟨24215885773785421370943155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16143923849190280913962103 24215885773785421370943155)
      ·
        refine ⟨36323828660678132056414733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24215885773785421370943155 36323828660678132056414733)
        ·
          refine ⟨13621435747754299521155525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36323828660678132056414733 13621435747754299521155525)
          ·
            refine ⟨2554019202703931160216661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13621435747754299521155525 2554019202703931160216661)
            ·
              refine ⟨29929912531686693283789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2554019202703931160216661 29929912531686693283789)
              ·
                rfl

theorem cell22_2360676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 8].length) (baseStart_2360676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360676 prefixEnd_2360676 := by exact prefixLift 2360676
  have htrace : WordTrace (prefixWord ++ tailWord_2360676) baseStart_2360676 baseEnd_2360676 := by
    simpa [prefixWord, tailWord_2360676, baseEnd_2360676] using wordTrace_append hprefix tailTrace_2360676
  have hstable : (prefixWord ++ tailWord_2360676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360676).length < 2 ^ (prefixWord ++ tailWord_2360676).sum := by decide
  have hdescent : baseEnd_2360676 < baseStart_2360676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360682 : List Nat := [3, 1, 3, 3, 2, 1, 3, 2, 4]
def baseStart_2360682 : Nat := 118140960795 + 2360682 * 2 ^ 59
def prefixEnd_2360682 : Nat := 4983230072969 + 3 ^ 40 * 2360682 * 2
def baseEnd_2360682 : Nat := 269369897426052901004095

theorem tailTrace_2360682 : CollatzResearch.WordTrace tailWord_2360682 prefixEnd_2360682 269369897426052901004095 := by
  unfold tailWord_2360682
  simp only [CollatzResearch.WordTrace]
  refine ⟨21525286508414940308129075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57400764022439840821677533 21525286508414940308129075)
  ·
    refine ⟨32287929762622410462193613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21525286508414940308129075 32287929762622410462193613)
    ·
      refine ⟨12107973660983403923322605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32287929762622410462193613 12107973660983403923322605)
      ·
        refine ⟨4540490122868776471245977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12107973660983403923322605 4540490122868776471245977)
        ·
          refine ⟨3405367592151582353434483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4540490122868776471245977 3405367592151582353434483)
          ·
            refine ⟨5108051388227373530151725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405367592151582353434483 5108051388227373530151725)
            ·
              refine ⟨1915519270585265073806897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5108051388227373530151725 1915519270585265073806897)
              ·
                refine ⟨1436639452938948805355173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1915519270585265073806897 1436639452938948805355173)
                ·
                  refine ⟨269369897426052901004095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1436639452938948805355173 269369897426052901004095)
                  ·
                    rfl

theorem cell22_2360682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_2360682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360682 prefixEnd_2360682 := by exact prefixLift 2360682
  have htrace : WordTrace (prefixWord ++ tailWord_2360682) baseStart_2360682 baseEnd_2360682 := by
    simpa [prefixWord, tailWord_2360682, baseEnd_2360682] using wordTrace_append hprefix tailTrace_2360682
  have hstable : (prefixWord ++ tailWord_2360682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360682).length < 2 ^ (prefixWord ++ tailWord_2360682).sum := by decide
  have hdescent : baseEnd_2360682 < baseStart_2360682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360693 : List Nat := [1, 3, 4, 1, 3, 1, 2, 7]
def baseStart_2360693 : Nat := 118140960795 + 2360693 * 2 ^ 59
def prefixEnd_2360693 : Nat := 4983230072969 + 3 ^ 40 * 2360693 * 2
def baseEnd_2360693 : Nat := 89790384200328704554139

theorem tailTrace_2360693 : CollatzResearch.WordTrace tailWord_2360693 prefixEnd_2360693 89790384200328704554139 := by
  unfold tailWord_2360693
  simp only [CollatzResearch.WordTrace]
  refine ⟨86101547236619910111166733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57401031491079940074111155 86101547236619910111166733)
  ·
    refine ⟨32288080213732466291687525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86101547236619910111166733 32288080213732466291687525)
    ·
      refine ⟨6054015040074837429691411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32288080213732466291687525 6054015040074837429691411)
      ·
        refine ⟨9081022560112256144537117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6054015040074837429691411 9081022560112256144537117)
        ·
          refine ⟨3405383460042096054201419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9081022560112256144537117 3405383460042096054201419)
          ·
            refine ⟨5108075190063144081302129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405383460042096054201419 5108075190063144081302129)
            ·
              refine ⟨3831056392547358060976597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5108075190063144081302129 3831056392547358060976597)
              ·
                refine ⟨89790384200328704554139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3831056392547358060976597 89790384200328704554139)
                ·
                  rfl

theorem cell22_2360693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 7].length) (baseStart_2360693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360693 prefixEnd_2360693 := by exact prefixLift 2360693
  have htrace : WordTrace (prefixWord ++ tailWord_2360693) baseStart_2360693 baseEnd_2360693 := by
    simpa [prefixWord, tailWord_2360693, baseEnd_2360693] using wordTrace_append hprefix tailTrace_2360693
  have hstable : (prefixWord ++ tailWord_2360693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360693).length < 2 ^ (prefixWord ++ tailWord_2360693).sum := by decide
  have hdescent : baseEnd_2360693 < baseStart_2360693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360736 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_2360736 : Nat := 118140960795 + 2360736 * 2 ^ 59
def prefixEnd_2360736 : Nat := 4983230072969 + 3 ^ 40 * 2360736 * 2
def baseEnd_2360736 : Nat := 808128177581720562162119

theorem tailTrace_2360736 : CollatzResearch.WordTrace tailWord_2360736 prefixEnd_2360736 808128177581720562162119 := by
  unfold tailWord_2360736
  simp only [CollatzResearch.WordTrace]
  refine ⟨43051557787732064227491031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57402077050309418969988041 43051557787732064227491031)
  ·
    refine ⟨64577336681598096341236547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43051557787732064227491031 64577336681598096341236547)
    ·
      refine ⟨96866005022397144511854821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64577336681598096341236547 96866005022397144511854821)
      ·
        refine ⟨18162375941699464595972779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96866005022397144511854821 18162375941699464595972779)
        ·
          refine ⟨27243563912549196893959169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18162375941699464595972779 27243563912549196893959169)
          ·
            refine ⟨20432672934411897670469377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27243563912549196893959169 20432672934411897670469377)
            ·
              refine ⟨15324504700808923252852033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20432672934411897670469377 15324504700808923252852033)
              ·
                refine ⟨11493378525606692439639025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15324504700808923252852033 11493378525606692439639025)
                ·
                  refine ⟨8620033894205019329729269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11493378525606692439639025 8620033894205019329729269)
                  ·
                    refine ⟨808128177581720562162119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8620033894205019329729269 808128177581720562162119)
                    ·
                      rfl

theorem cell22_2360736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_2360736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360736 prefixEnd_2360736 := by exact prefixLift 2360736
  have htrace : WordTrace (prefixWord ++ tailWord_2360736) baseStart_2360736 baseEnd_2360736 := by
    simpa [prefixWord, tailWord_2360736, baseEnd_2360736] using wordTrace_append hprefix tailTrace_2360736
  have hstable : (prefixWord ++ tailWord_2360736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360736).length < 2 ^ (prefixWord ++ tailWord_2360736).sum := by decide
  have hdescent : baseEnd_2360736 < baseStart_2360736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360738 : List Nat := [3, 3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_2360738 : Nat := 118140960795 + 2360738 * 2 ^ 59
def prefixEnd_2360738 : Nat := 4983230072969 + 3 ^ 40 * 2360738 * 2
def baseEnd_2360738 : Nat := 269376287407531074537371

theorem tailTrace_2360738 : CollatzResearch.WordTrace tailWord_2360738 prefixEnd_2360738 269376287407531074537371 := by
  unfold tailWord_2360738
  simp only [CollatzResearch.WordTrace]
  refine ⟨21525797130364220699138717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57402125680971255197703245 21525797130364220699138717)
  ·
    refine ⟨8072173923886582762177019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21525797130364220699138717 8072173923886582762177019)
    ·
      refine ⟨12108260885829874143265529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8072173923886582762177019 12108260885829874143265529)
      ·
        refine ⟨9081195664372405607449147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12108260885829874143265529 9081195664372405607449147)
        ·
          refine ⟨13621793496558608411173721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9081195664372405607449147 13621793496558608411173721)
          ·
            refine ⟨10216345122418956308380291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13621793496558608411173721 10216345122418956308380291)
            ·
              refine ⟨15324517683628434462570437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10216345122418956308380291 15324517683628434462570437)
              ·
                refine ⟨2873347065680331461731957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15324517683628434462570437 2873347065680331461731957)
                ·
                  refine ⟨269376287407531074537371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2873347065680331461731957 269376287407531074537371)
                  ·
                    rfl

theorem cell22_2360738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_2360738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360738 prefixEnd_2360738 := by exact prefixLift 2360738
  have htrace : WordTrace (prefixWord ++ tailWord_2360738) baseStart_2360738 baseEnd_2360738 := by
    simpa [prefixWord, tailWord_2360738, baseEnd_2360738] using wordTrace_append hprefix tailTrace_2360738
  have hstable : (prefixWord ++ tailWord_2360738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360738).length < 2 ^ (prefixWord ++ tailWord_2360738).sum := by decide
  have hdescent : baseEnd_2360738 < baseStart_2360738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360783 : List Nat := [1, 1, 2, 1, 1, 4, 3, 5, 4]
def baseStart_2360783 : Nat := 118140960795 + 2360783 * 2 ^ 59
def prefixEnd_2360783 : Nat := 4983230072969 + 3 ^ 40 * 2360783 * 2
def baseEnd_2360783 : Nat := 269381422214076035412325

theorem tailTrace_2360783 : CollatzResearch.WordTrace tailWord_2360783 prefixEnd_2360783 269381422214076035412325 := by
  unfold tailWord_2360783
  simp only [CollatzResearch.WordTrace]
  refine ⟨86104829806293855481943003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57403219870862570321295335 86104829806293855481943003)
  ·
    refine ⟨129157244709440783222914505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86104829806293855481943003 129157244709440783222914505)
    ·
      refine ⟨96867933532080587417185879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129157244709440783222914505 96867933532080587417185879)
      ·
        refine ⟨145301900298120881125778819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96867933532080587417185879 145301900298120881125778819)
        ·
          refine ⟨217952850447181321688668229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145301900298120881125778819 217952850447181321688668229)
          ·
            refine ⟨40866159458846497816625293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217952850447181321688668229 40866159458846497816625293)
            ·
              refine ⟨15324809797067436681234485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40866159458846497816625293 15324809797067436681234485)
              ·
                refine ⟨1436700918475072188865733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15324809797067436681234485 1436700918475072188865733)
                ·
                  refine ⟨269381422214076035412325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1436700918475072188865733 269381422214076035412325)
                  ·
                    rfl

theorem cell22_2360783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 5, 4].length) (baseStart_2360783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360783 prefixEnd_2360783 := by exact prefixLift 2360783
  have htrace : WordTrace (prefixWord ++ tailWord_2360783) baseStart_2360783 baseEnd_2360783 := by
    simpa [prefixWord, tailWord_2360783, baseEnd_2360783] using wordTrace_append hprefix tailTrace_2360783
  have hstable : (prefixWord ++ tailWord_2360783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360783).length < 2 ^ (prefixWord ++ tailWord_2360783).sum := by decide
  have hdescent : baseEnd_2360783 < baseStart_2360783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360826 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_2360826 : Nat := 118140960795 + 2360826 * 2 ^ 59
def prefixEnd_2360826 : Nat := 4983230072969 + 3 ^ 40 * 2360826 * 2
def baseEnd_2360826 : Nat := 808158986420990327411843

theorem tailTrace_2360826 : CollatzResearch.WordTrace tailWord_2360826 prefixEnd_2360826 808158986420990327411843 := by
  unfold tailWord_2360826
  simp only [CollatzResearch.WordTrace]
  refine ⟨21526599536284518456439583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57404265430092049217172221 21526599536284518456439583)
  ·
    refine ⟨32289899304426777684659375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21526599536284518456439583 32289899304426777684659375)
    ·
      refine ⟨48434848956640166526989063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32289899304426777684659375 48434848956640166526989063)
      ·
        refine ⟨72652273434960249790483595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48434848956640166526989063 72652273434960249790483595)
        ·
          refine ⟨108978410152440374685725393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72652273434960249790483595 108978410152440374685725393)
          ·
            refine ⟨81733807614330281014294045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108978410152440374685725393 81733807614330281014294045)
            ·
              refine ⟨30650177855373855380360267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81733807614330281014294045 30650177855373855380360267)
              ·
                refine ⟨45975266783060783070540401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30650177855373855380360267 45975266783060783070540401)
                ·
                  refine ⟨34481450087295587302905301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45975266783060783070540401 34481450087295587302905301)
                  ·
                    refine ⟨808158986420990327411843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34481450087295587302905301 808158986420990327411843)
                    ·
                      rfl

theorem cell22_2360826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_2360826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360826 prefixEnd_2360826 := by exact prefixLift 2360826
  have htrace : WordTrace (prefixWord ++ tailWord_2360826) baseStart_2360826 baseEnd_2360826 := by
    simpa [prefixWord, tailWord_2360826, baseEnd_2360826] using wordTrace_append hprefix tailTrace_2360826
  have hstable : (prefixWord ++ tailWord_2360826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360826).length < 2 ^ (prefixWord ++ tailWord_2360826).sum := by decide
  have hdescent : baseEnd_2360826 < baseStart_2360826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360828 : List Nat := [2, 2, 2, 1, 2, 1, 6, 6]
def baseStart_2360828 : Nat := 118140960795 + 2360828 * 2 ^ 59
def prefixEnd_2360828 : Nat := 4983230072969 + 3 ^ 40 * 2360828 * 2
def baseEnd_2360828 : Nat := 89795519006873665429093

theorem tailTrace_2360828 : CollatzResearch.WordTrace tailWord_2360828 prefixEnd_2360828 89795519006873665429093 := by
  unfold tailWord_2360828
  simp only [CollatzResearch.WordTrace]
  refine ⟨43053235545565414083665569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57404314060753885444887425 43053235545565414083665569)
  ·
    refine ⟨32289926659174060562749177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43053235545565414083665569 32289926659174060562749177)
    ·
      refine ⟨24217444994380545422061883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32289926659174060562749177 24217444994380545422061883)
      ·
        refine ⟨36326167491570818133092825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24217444994380545422061883 36326167491570818133092825)
        ·
          refine ⟨27244625618678113599819619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36326167491570818133092825 27244625618678113599819619)
          ·
            refine ⟨40866938428017170399729429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27244625618678113599819619 40866938428017170399729429)
            ·
              refine ⟨1915637738813304862487317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40866938428017170399729429 1915637738813304862487317)
              ·
                refine ⟨89795519006873665429093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1915637738813304862487317 89795519006873665429093)
                ·
                  rfl

theorem cell22_2360828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 6].length) (baseStart_2360828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360828 prefixEnd_2360828 := by exact prefixLift 2360828
  have htrace : WordTrace (prefixWord ++ tailWord_2360828) baseStart_2360828 baseEnd_2360828 := by
    simpa [prefixWord, tailWord_2360828, baseEnd_2360828] using wordTrace_append hprefix tailTrace_2360828
  have hstable : (prefixWord ++ tailWord_2360828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360828).length < 2 ^ (prefixWord ++ tailWord_2360828).sum := by decide
  have hdescent : baseEnd_2360828 < baseStart_2360828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360834 : List Nat := [3, 4, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2360834 : Nat := 118140960795 + 2360834 * 2 ^ 59
def prefixEnd_2360834 : Nat := 4983230072969 + 3 ^ 40 * 2360834 * 2
def baseEnd_2360834 : Nat := 269387241661493657737273

theorem tailTrace_2360834 : CollatzResearch.WordTrace tailWord_2360834 prefixEnd_2360834 269387241661493657737273 := by
  unfold tailWord_2360834
  simp only [CollatzResearch.WordTrace]
  refine ⟨21526672482277272798012389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57404459952739394128033037 21526672482277272798012389)
  ·
    refine ⟨4036251090426988649627323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21526672482277272798012389 4036251090426988649627323)
    ·
      refine ⟨6054376635640482974440985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4036251090426988649627323 6054376635640482974440985)
      ·
        refine ⟨4540782476730362230830739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6054376635640482974440985 4540782476730362230830739)
        ·
          refine ⟨6811173715095543346246109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4540782476730362230830739 6811173715095543346246109)
          ·
            refine ⟨2554190143160828754842291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6811173715095543346246109 2554190143160828754842291)
            ·
              refine ⟨3831285214741243132263437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554190143160828754842291 3831285214741243132263437)
              ·
                refine ⟨1436731955527966174598789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3831285214741243132263437 1436731955527966174598789)
                ·
                  refine ⟨269387241661493657737273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1436731955527966174598789 269387241661493657737273)
                  ·
                    rfl

theorem cell22_2360834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2360834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360834 prefixEnd_2360834 := by exact prefixLift 2360834
  have htrace : WordTrace (prefixWord ++ tailWord_2360834) baseStart_2360834 baseEnd_2360834 := by
    simpa [prefixWord, tailWord_2360834, baseEnd_2360834] using wordTrace_append hprefix tailTrace_2360834
  have hstable : (prefixWord ++ tailWord_2360834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360834).length < 2 ^ (prefixWord ++ tailWord_2360834).sum := by decide
  have hdescent : baseEnd_2360834 < baseStart_2360834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360967 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 2, 3]
def baseStart_2360967 : Nat := 118140960795 + 2360967 * 2 ^ 59
def prefixEnd_2360967 : Nat := 4983230072969 + 3 ^ 40 * 2360967 * 2
def baseEnd_2360967 : Nat := 808207253602512959636411

theorem tailTrace_2360967 : CollatzResearch.WordTrace tailWord_2360967 prefixEnd_2360967 808207253602512959636411 := by
  unfold tailWord_2360967
  simp only [CollatzResearch.WordTrace]
  refine ⟨86111540837627254906641155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57407693891751503271094103 86111540837627254906641155)
  ·
    refine ⟨129167311256440882359961733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86111540837627254906641155 129167311256440882359961733)
    ·
      refine ⟨24218870860582665442492825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129167311256440882359961733 24218870860582665442492825)
      ·
        refine ⟨18164153145436999081869619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24218870860582665442492825 18164153145436999081869619)
        ·
          refine ⟨27246229718155498622804429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18164153145436999081869619 27246229718155498622804429)
          ·
            refine ⟨10217336144308311983551661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27246229718155498622804429 10217336144308311983551661)
            ·
              refine ⟨3831501054115616993831873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10217336144308311983551661 3831501054115616993831873)
              ·
                refine ⟨2873625790586712745373905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3831501054115616993831873 2873625790586712745373905)
                ·
                  refine ⟨2155219342940034559030429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2873625790586712745373905 2155219342940034559030429)
                  ·
                    refine ⟨808207253602512959636411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2155219342940034559030429 808207253602512959636411)
                    ·
                      rfl

theorem cell22_2360967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_2360967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360967 prefixEnd_2360967 := by exact prefixLift 2360967
  have htrace : WordTrace (prefixWord ++ tailWord_2360967) baseStart_2360967 baseEnd_2360967 := by
    simpa [prefixWord, tailWord_2360967, baseEnd_2360967] using wordTrace_append hprefix tailTrace_2360967
  have hstable : (prefixWord ++ tailWord_2360967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360967).length < 2 ^ (prefixWord ++ tailWord_2360967).sum := by decide
  have hdescent : baseEnd_2360967 < baseStart_2360967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360984 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 2, 3]
def baseStart_2360984 : Nat := 118140960795 + 2360984 * 2 ^ 59
def prefixEnd_2360984 : Nat := 4983230072969 + 3 ^ 40 * 2360984 * 2
def baseEnd_2360984 : Nat := 808213073049930581961359

theorem tailTrace_2360984 : CollatzResearch.WordTrace tailWord_2360984 prefixEnd_2360984 808213073049930581961359 := by
  unfold tailWord_2360984
  simp only [CollatzResearch.WordTrace]
  refine ⟨43056080439282833405005003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57408107252377111206673337 43056080439282833405005003)
  ·
    refine ⟨64584120658924250107507505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43056080439282833405005003 64584120658924250107507505)
    ·
      refine ⟨48438090494193187580630629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64584120658924250107507505 48438090494193187580630629)
      ·
        refine ⟨9082141967661222671368243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48438090494193187580630629 9082141967661222671368243)
        ·
          refine ⟨13623212951491834007052365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9082141967661222671368243 13623212951491834007052365)
          ·
            refine ⟨5108704856809437752644637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13623212951491834007052365 5108704856809437752644637)
            ·
              refine ⟨1915764321303539157241739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5108704856809437752644637 1915764321303539157241739)
              ·
                refine ⟨2873646481955308735862609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1915764321303539157241739 2873646481955308735862609)
                ·
                  refine ⟨2155234861466481551896957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2873646481955308735862609 2155234861466481551896957)
                  ·
                    refine ⟨808213073049930581961359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2155234861466481551896957 808213073049930581961359)
                    ·
                      rfl

theorem cell22_2360984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_2360984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360984 prefixEnd_2360984 := by exact prefixLift 2360984
  have htrace : WordTrace (prefixWord ++ tailWord_2360984) baseStart_2360984 baseEnd_2360984 := by
    simpa [prefixWord, tailWord_2360984, baseEnd_2360984] using wordTrace_append hprefix tailTrace_2360984
  have hstable : (prefixWord ++ tailWord_2360984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360984).length < 2 ^ (prefixWord ++ tailWord_2360984).sum := by decide
  have hdescent : baseEnd_2360984 < baseStart_2360984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360995 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 3, 3]
def baseStart_2360995 : Nat := 118140960795 + 2360995 * 2 ^ 59
def prefixEnd_2360995 : Nat := 4983230072969 + 3 ^ 40 * 2360995 * 2
def baseEnd_2360995 : Nat := 808216838574730219936325

theorem tailTrace_2360995 : CollatzResearch.WordTrace tailWord_2360995 prefixEnd_2360995 808216838574730219936325 := by
  unfold tailWord_2360995
  simp only [CollatzResearch.WordTrace]
  refine ⟨86112562081525815688660439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57408374721017210459106959 86112562081525815688660439)
  ·
    refine ⟨129168843122288723532990659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86112562081525815688660439 129168843122288723532990659)
    ·
      refine ⟨193753264683433085299485989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129168843122288723532990659 193753264683433085299485989)
      ·
        refine ⟨36328737128143703493653623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193753264683433085299485989 36328737128143703493653623)
        ·
          refine ⟨54493105692215555240480435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36328737128143703493653623 54493105692215555240480435)
          ·
            refine ⟨81739658538323332860720653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54493105692215555240480435 81739658538323332860720653)
            ·
              refine ⟨30652371951871249822770245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81739658538323332860720653 30652371951871249822770245)
              ·
                refine ⟨5747319740975859341769421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30652371951871249822770245 5747319740975859341769421)
                ·
                  refine ⟨2155244902865947253163533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5747319740975859341769421 2155244902865947253163533)
                  ·
                    refine ⟨808216838574730219936325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2155244902865947253163533 808216838574730219936325)
                    ·
                      rfl

theorem cell22_2360995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 3].length) (baseStart_2360995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2360995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2360995 prefixEnd_2360995 := by exact prefixLift 2360995
  have htrace : WordTrace (prefixWord ++ tailWord_2360995) baseStart_2360995 baseEnd_2360995 := by
    simpa [prefixWord, tailWord_2360995, baseEnd_2360995] using wordTrace_append hprefix tailTrace_2360995
  have hstable : (prefixWord ++ tailWord_2360995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360995).length < 2 ^ (prefixWord ++ tailWord_2360995).sum := by decide
  have hdescent : baseEnd_2360995 < baseStart_2360995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361008 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 7]
def baseStart_2361008 : Nat := 118140960795 + 2361008 * 2 ^ 59
def prefixEnd_2361008 : Nat := 4983230072969 + 3 ^ 40 * 2361008 * 2
def baseEnd_2361008 : Nat := 269407096246800839787095

theorem tailTrace_2361008 : CollatzResearch.WordTrace tailWord_2361008 prefixEnd_2361008 269407096246800839787095 := by
  unfold tailWord_2361008
  simp only [CollatzResearch.WordTrace]
  refine ⟨43056518115239359454441839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57408690820319145939255785 43056518115239359454441839)
  ·
    refine ⟨64584777172859039181662759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43056518115239359454441839 64584777172859039181662759)
    ·
      refine ⟨96877165759288558772494139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64584777172859039181662759 96877165759288558772494139)
      ·
        refine ⟨145315748638932838158741209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96877165759288558772494139 145315748638932838158741209)
        ·
          refine ⟨108986811479199628619055907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145315748638932838158741209 108986811479199628619055907)
          ·
            refine ⟨163480217218799442928583861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108986811479199628619055907 163480217218799442928583861)
            ·
              refine ⟨15326270364262447774554737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163480217218799442928583861 15326270364262447774554737)
              ·
                refine ⟨11494702773196835830916053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15326270364262447774554737 11494702773196835830916053)
                ·
                  refine ⟨269407096246800839787095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11494702773196835830916053 269407096246800839787095)
                  ·
                    rfl

theorem cell22_2361008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_2361008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361008 prefixEnd_2361008 := by exact prefixLift 2361008
  have htrace : WordTrace (prefixWord ++ tailWord_2361008) baseStart_2361008 baseEnd_2361008 := by
    simpa [prefixWord, tailWord_2361008, baseEnd_2361008] using wordTrace_append hprefix tailTrace_2361008
  have hstable : (prefixWord ++ tailWord_2361008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361008).length < 2 ^ (prefixWord ++ tailWord_2361008).sum := by decide
  have hdescent : baseEnd_2361008 < baseStart_2361008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361042 : List Nat := [3, 2, 2, 2, 2, 2, 1, 3, 5]
def baseStart_2361042 : Nat := 118140960795 + 2361042 * 2 ^ 59
def prefixEnd_2361042 : Nat := 4983230072969 + 3 ^ 40 * 2361042 * 2
def baseEnd_2361042 : Nat := 269410975878412588003727

theorem tailTrace_2361042 : CollatzResearch.WordTrace tailWord_2361042 prefixEnd_2361042 269410975878412588003727 := by
  unfold tailWord_2361042
  simp only [CollatzResearch.WordTrace]
  refine ⟨21528569078088885678905345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57409517541570361810414253 21528569078088885678905345)
  ·
    refine ⟨16146426808566664259179009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21528569078088885678905345 16146426808566664259179009)
    ·
      refine ⟨12109820106424998194384257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16146426808566664259179009 12109820106424998194384257)
      ·
        refine ⟨9082365079818748645788193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12109820106424998194384257 9082365079818748645788193)
        ·
          refine ⟨6811773809864061484341145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9082365079818748645788193 6811773809864061484341145)
          ·
            refine ⟨5108830357398046113255859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6811773809864061484341145 5108830357398046113255859)
            ·
              refine ⟨7663245536097069169883789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5108830357398046113255859 7663245536097069169883789)
              ·
                refine ⟨2873717076036400938706421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7663245536097069169883789 2873717076036400938706421)
                ·
                  refine ⟨269410975878412588003727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2873717076036400938706421 269410975878412588003727)
                  ·
                    rfl

theorem cell22_2361042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_2361042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361042 prefixEnd_2361042 := by exact prefixLift 2361042
  have htrace : WordTrace (prefixWord ++ tailWord_2361042) baseStart_2361042 baseEnd_2361042 := by
    simpa [prefixWord, tailWord_2361042, baseEnd_2361042] using wordTrace_append hprefix tailTrace_2361042
  have hstable : (prefixWord ++ tailWord_2361042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361042).length < 2 ^ (prefixWord ++ tailWord_2361042).sum := by decide
  have hdescent : baseEnd_2361042 < baseStart_2361042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361055 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 3, 4]
def baseStart_2361055 : Nat := 118140960795 + 2361055 * 2 ^ 59
def prefixEnd_2361055 : Nat := 4983230072969 + 3 ^ 40 * 2361055 * 2
def baseEnd_2361055 : Nat := 808237377800910063436141

theorem tailTrace_2361055 : CollatzResearch.WordTrace tailWord_2361055 prefixEnd_2361055 808237377800910063436141 := by
  unfold tailWord_2361055
  simp only [CollatzResearch.WordTrace]
  refine ⟨86114750461308445935844619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57409833640872297290563079 86114750461308445935844619)
  ·
    refine ⟨129172125691962668903766929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86114750461308445935844619 129172125691962668903766929)
    ·
      refine ⟨96879094268972001677825197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129172125691962668903766929 96879094268972001677825197)
      ·
        refine ⟨36329660350864500629184449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96879094268972001677825197 36329660350864500629184449)
        ·
          refine ⟨27247245263148375471888337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36329660350864500629184449 27247245263148375471888337)
          ·
            refine ⟨20435433947361281603916253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27247245263148375471888337 20435433947361281603916253)
            ·
              refine ⟨7663287730260480601468595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20435433947361281603916253 7663287730260480601468595)
              ·
                refine ⟨11494931595390720902202893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7663287730260480601468595 11494931595390720902202893)
                ·
                  refine ⟨4310599348271520338326085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11494931595390720902202893 4310599348271520338326085)
                  ·
                    refine ⟨808237377800910063436141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4310599348271520338326085 808237377800910063436141)
                    ·
                      rfl

theorem cell22_2361055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_2361055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361055 prefixEnd_2361055 := by exact prefixLift 2361055
  have htrace : WordTrace (prefixWord ++ tailWord_2361055) baseStart_2361055 baseEnd_2361055 := by
    simpa [prefixWord, tailWord_2361055, baseEnd_2361055] using wordTrace_append hprefix tailTrace_2361055
  have hstable : (prefixWord ++ tailWord_2361055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361055).length < 2 ^ (prefixWord ++ tailWord_2361055).sum := by decide
  have hdescent : baseEnd_2361055 < baseStart_2361055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361076 : List Nat := [2, 6, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2361076 : Nat := 118140960795 + 2361076 * 2 ^ 59
def prefixEnd_2361076 : Nat := 4983230072969 + 3 ^ 40 * 2361076 * 2
def baseEnd_2361076 : Nat := 269414855510024336220359

theorem tailTrace_2361076 : CollatzResearch.WordTrace tailWord_2361076 prefixEnd_2361076 269414855510024336220359 := by
  unfold tailWord_2361076
  simp only [CollatzResearch.WordTrace]
  refine ⟨43057758197116183261179541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57410344262821577681572721 43057758197116183261179541)
  ·
    refine ⟨2018332415489821090367791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43057758197116183261179541 2018332415489821090367791)
    ·
      refine ⟨3027498623234731635551687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2018332415489821090367791 3027498623234731635551687)
      ·
        refine ⟨4541247934852097453327531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3027498623234731635551687 4541247934852097453327531)
        ·
          refine ⟨6811871902278146179991297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4541247934852097453327531 6811871902278146179991297)
          ·
            refine ⟨5108903926708609634993473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6811871902278146179991297 5108903926708609634993473)
            ·
              refine ⟨3831677945031457226245105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5108903926708609634993473 3831677945031457226245105)
              ·
                refine ⟨2873758458773592919683829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3831677945031457226245105 2873758458773592919683829)
                ·
                  refine ⟨269414855510024336220359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2873758458773592919683829 269414855510024336220359)
                  ·
                    rfl

theorem cell22_2361076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2361076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361076 prefixEnd_2361076 := by exact prefixLift 2361076
  have htrace : WordTrace (prefixWord ++ tailWord_2361076) baseStart_2361076 baseEnd_2361076 := by
    simpa [prefixWord, tailWord_2361076, baseEnd_2361076] using wordTrace_append hprefix tailTrace_2361076
  have hstable : (prefixWord ++ tailWord_2361076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361076).length < 2 ^ (prefixWord ++ tailWord_2361076).sum := by decide
  have hdescent : baseEnd_2361076 < baseStart_2361076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361100 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_2361100 : Nat := 118140960795 + 2361100 * 2 ^ 59
def prefixEnd_2361100 : Nat := 4983230072969 + 3 ^ 40 * 2361100 * 2
def baseEnd_2361100 : Nat := 808252782220544946061003

theorem tailTrace_2361100 : CollatzResearch.WordTrace tailWord_2361100 prefixEnd_2361100 808252782220544946061003 := by
  unfold tailWord_2361100
  simp only [CollatzResearch.WordTrace]
  refine ⟨43058195873072709310616377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57410927830763612414155169 43058195873072709310616377)
  ·
    refine ⟨32293646904804531982962283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43058195873072709310616377 32293646904804531982962283)
    ·
      refine ⟨48440470357206797974443425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32293646904804531982962283 48440470357206797974443425)
      ·
        refine ⟨36330352767905098480832569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48440470357206797974443425 36330352767905098480832569)
        ·
          refine ⟨27247764575928823860624427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36330352767905098480832569 27247764575928823860624427)
          ·
            refine ⟨40871646863893235790936641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27247764575928823860624427 40871646863893235790936641)
            ·
              refine ⟨30653735147919926843202481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40871646863893235790936641 30653735147919926843202481)
              ·
                refine ⟨22990301360939945132401861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30653735147919926843202481 22990301360939945132401861)
                ·
                  refine ⟨4310681505176239712325349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22990301360939945132401861 4310681505176239712325349)
                  ·
                    refine ⟨808252782220544946061003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4310681505176239712325349 808252782220544946061003)
                    ·
                      rfl

theorem cell22_2361100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_2361100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361100 prefixEnd_2361100 := by exact prefixLift 2361100
  have htrace : WordTrace (prefixWord ++ tailWord_2361100) baseStart_2361100 baseEnd_2361100 := by
    simpa [prefixWord, tailWord_2361100, baseEnd_2361100] using wordTrace_append hprefix tailTrace_2361100
  have hstable : (prefixWord ++ tailWord_2361100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361100).length < 2 ^ (prefixWord ++ tailWord_2361100).sum := by decide
  have hdescent : baseEnd_2361100 < baseStart_2361100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361224 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 3, 4]
def baseStart_2361224 : Nat := 118140960795 + 2361224 * 2 ^ 59
def prefixEnd_2361224 : Nat := 4983230072969 + 3 ^ 40 * 2361224 * 2
def baseEnd_2361224 : Nat := 808295229954649955960623

theorem tailTrace_2361224 : CollatzResearch.WordTrace tailWord_2361224 prefixEnd_2361224 808295229954649955960623 := by
  unfold tailWord_2361224
  simp only [CollatzResearch.WordTrace]
  refine ⟨43060457198848093899373363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57413942931797458532497817 43060457198848093899373363)
  ·
    refine ⟨64590685798272140849060045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43060457198848093899373363 64590685798272140849060045)
    ·
      refine ⟨24221507174352052818397517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64590685798272140849060045 24221507174352052818397517)
      ·
        refine ⟨9083065190382019806899069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24221507174352052818397517 9083065190382019806899069)
        ·
          refine ⟨3406149446393257427587151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9083065190382019806899069 3406149446393257427587151)
          ·
            refine ⟨5109224169589886141380727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406149446393257427587151 5109224169589886141380727)
            ·
              refine ⟨7663836254384829212071091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5109224169589886141380727 7663836254384829212071091)
              ·
                refine ⟨11495754381577243818106637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7663836254384829212071091 11495754381577243818106637)
                ·
                  refine ⟨4310907893091466431789989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11495754381577243818106637 4310907893091466431789989)
                  ·
                    refine ⟨808295229954649955960623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4310907893091466431789989 808295229954649955960623)
                    ·
                      rfl

theorem cell22_2361224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_2361224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361224 prefixEnd_2361224 := by exact prefixLift 2361224
  have htrace : WordTrace (prefixWord ++ tailWord_2361224) baseStart_2361224 baseEnd_2361224 := by
    simpa [prefixWord, tailWord_2361224, baseEnd_2361224] using wordTrace_append hprefix tailTrace_2361224
  have hstable : (prefixWord ++ tailWord_2361224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361224).length < 2 ^ (prefixWord ++ tailWord_2361224).sum := by decide
  have hdescent : baseEnd_2361224 < baseStart_2361224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361235 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 5, 6]
def baseStart_2361235 : Nat := 118140960795 + 2361235 * 2 ^ 59
def prefixEnd_2361235 : Nat := 4983230072969 + 3 ^ 40 * 2361235 * 2
def baseEnd_2361235 : Nat := 808298995479449593935589

theorem tailTrace_2361235 : CollatzResearch.WordTrace tailWord_2361235 prefixEnd_2361235 808298995479449593935589 := by
  unfold tailWord_2361235
  simp only [CollatzResearch.WordTrace]
  refine ⟨86121315600656336677397159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57414210400437557784931439 86121315600656336677397159)
  ·
    refine ⟨129181973400984505016095739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86121315600656336677397159 129181973400984505016095739)
    ·
      refine ⟨193772960101476757524143609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129181973400984505016095739 193772960101476757524143609)
      ·
        refine ⟨145329720076107568143107707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193772960101476757524143609 145329720076107568143107707)
        ·
          refine ⟨217994580114161352214661561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145329720076107568143107707 217994580114161352214661561)
          ·
            refine ⟨163495935085621014160996171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217994580114161352214661561 163495935085621014160996171)
            ·
              refine ⟨245243902628431521241494257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163495935085621014160996171 245243902628431521241494257)
              ·
                refine ⟨183932926971323640931120693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 245243902628431521241494257 183932926971323640931120693)
                ·
                  refine ⟨17243711903561591337292565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183932926971323640931120693 17243711903561591337292565)
                  ·
                    refine ⟨808298995479449593935589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17243711903561591337292565 808298995479449593935589)
                    ·
                      rfl

theorem cell22_2361235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_2361235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361235 prefixEnd_2361235 := by exact prefixLift 2361235
  have htrace : WordTrace (prefixWord ++ tailWord_2361235) baseStart_2361235 baseEnd_2361235 := by
    simpa [prefixWord, tailWord_2361235, baseEnd_2361235] using wordTrace_append hprefix tailTrace_2361235
  have hstable : (prefixWord ++ tailWord_2361235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361235).length < 2 ^ (prefixWord ++ tailWord_2361235).sum := by decide
  have hdescent : baseEnd_2361235 < baseStart_2361235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361237 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_2361237 : Nat := 118140960795 + 2361237 * 2 ^ 59
def prefixEnd_2361237 : Nat := 4983230072969 + 3 ^ 40 * 2361237 * 2
def baseEnd_2361237 : Nat := 808299680120322255385583

theorem tailTrace_2361237 : CollatzResearch.WordTrace tailWord_2361237 prefixEnd_2361237 808299680120322255385583 := by
  unfold tailWord_2361237
  simp only [CollatzResearch.WordTrace]
  refine ⟨86121388546649091018969965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57414259031099394012646643 86121388546649091018969965)
  ·
    refine ⟨32295520704993409132113737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86121388546649091018969965 32295520704993409132113737)
    ·
      refine ⟨24221640528745056849085303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32295520704993409132113737 24221640528745056849085303)
      ·
        refine ⟨36332460793117585273627955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24221640528745056849085303 36332460793117585273627955)
        ·
          refine ⟨54498691189676377910441933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36332460793117585273627955 54498691189676377910441933)
          ·
            refine ⟨20437009196128641716415725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54498691189676377910441933 20437009196128641716415725)
            ·
              refine ⟨7663878448548240643655897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20437009196128641716415725 7663878448548240643655897)
              ·
                refine ⟨5747908836411180482741923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7663878448548240643655897 5747908836411180482741923)
                ·
                  refine ⟨8621863254616770724112885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5747908836411180482741923 8621863254616770724112885)
                  ·
                    refine ⟨808299680120322255385583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8621863254616770724112885 808299680120322255385583)
                    ·
                      rfl

theorem cell22_2361237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_2361237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361237 prefixEnd_2361237 := by exact prefixLift 2361237
  have htrace : WordTrace (prefixWord ++ tailWord_2361237) baseStart_2361237 baseEnd_2361237 := by
    simpa [prefixWord, tailWord_2361237, baseEnd_2361237] using wordTrace_append hprefix tailTrace_2361237
  have hstable : (prefixWord ++ tailWord_2361237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361237).length < 2 ^ (prefixWord ++ tailWord_2361237).sum := by decide
  have hdescent : baseEnd_2361237 < baseStart_2361237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361316 : List Nat := [2, 3, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_2361316 : Nat := 118140960795 + 2361316 * 2 ^ 59
def prefixEnd_2361316 : Nat := 4983230072969 + 3 ^ 40 * 2361316 * 2
def baseEnd_2361316 : Nat := 808326723434792382660341

theorem tailTrace_2361316 : CollatzResearch.WordTrace tailWord_2361316 prefixEnd_2361316 808326723434792382660341 := by
  unfold tailWord_2361316
  simp only [CollatzResearch.WordTrace]
  refine ⟨43062134956681443755547901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57416179942241925007397201 43062134956681443755547901)
  ·
    refine ⟨16148300608755541408330463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43062134956681443755547901 16148300608755541408330463)
    ·
      refine ⟨24222450913133312112495695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16148300608755541408330463 24222450913133312112495695)
      ·
        refine ⟨36333676369699968168743543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24222450913133312112495695 36333676369699968168743543)
        ·
          refine ⟨54500514554549952253115315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36333676369699968168743543 54500514554549952253115315)
          ·
            refine ⟨81750771831824928379672973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54500514554549952253115315 81750771831824928379672973)
            ·
              refine ⟨30656539436934348142377365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81750771831824928379672973 30656539436934348142377365)
              ·
                refine ⟨1437025286106297569173939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30656539436934348142377365 1437025286106297569173939)
                ·
                  refine ⟨2155537929159446353760909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437025286106297569173939 2155537929159446353760909)
                  ·
                    refine ⟨808326723434792382660341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2155537929159446353760909 808326723434792382660341)
                    ·
                      rfl

theorem cell22_2361316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_2361316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361316 prefixEnd_2361316 := by exact prefixLift 2361316
  have htrace : WordTrace (prefixWord ++ tailWord_2361316) baseStart_2361316 baseEnd_2361316 := by
    simpa [prefixWord, tailWord_2361316, baseEnd_2361316] using wordTrace_append hprefix tailTrace_2361316
  have hstable : (prefixWord ++ tailWord_2361316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361316).length < 2 ^ (prefixWord ++ tailWord_2361316).sum := by decide
  have hdescent : baseEnd_2361316 < baseStart_2361316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361327 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 2, 5]
def baseStart_2361327 : Nat := 118140960795 + 2361327 * 2 ^ 59
def prefixEnd_2361327 : Nat := 4983230072969 + 3 ^ 40 * 2361327 * 2
def baseEnd_2361327 : Nat := 808330488959592020635307

theorem tailTrace_2361327 : CollatzResearch.WordTrace tailWord_2361327 prefixEnd_2361327 808330488959592020635307 := by
  unfold tailWord_2361327
  simp only [CollatzResearch.WordTrace]
  refine ⟨86124671116323036389746235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57416447410882024259830823 86124671116323036389746235)
  ·
    refine ⟨129187006674484554584619353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86124671116323036389746235 129187006674484554584619353)
    ·
      refine ⟨96890255005863415938464515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129187006674484554584619353 96890255005863415938464515)
      ·
        refine ⟨145335382508795123907696773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96890255005863415938464515 145335382508795123907696773)
        ·
          refine ⟨27250384220399085732693145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145335382508795123907696773 27250384220399085732693145)
          ·
            refine ⟨20437788165299314299519859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27250384220399085732693145 20437788165299314299519859)
            ·
              refine ⟨30656682247948971449279789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20437788165299314299519859 30656682247948971449279789)
              ·
                refine ⟨11496255842980864293479921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30656682247948971449279789 11496255842980864293479921)
                ·
                  refine ⟨8622191882235648220109941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11496255842980864293479921 8622191882235648220109941)
                  ·
                    refine ⟨808330488959592020635307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8622191882235648220109941 808330488959592020635307)
                    ·
                      rfl

theorem cell22_2361327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_2361327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361327 prefixEnd_2361327 := by exact prefixLift 2361327
  have htrace : WordTrace (prefixWord ++ tailWord_2361327) baseStart_2361327 baseEnd_2361327 := by
    simpa [prefixWord, tailWord_2361327, baseEnd_2361327] using wordTrace_append hprefix tailTrace_2361327
  have hstable : (prefixWord ++ tailWord_2361327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361327).length < 2 ^ (prefixWord ++ tailWord_2361327).sum := by decide
  have hdescent : baseEnd_2361327 < baseStart_2361327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361380 : List Nat := [2, 3, 1, 4, 3, 1, 2, 1, 5]
def baseStart_2361380 : Nat := 118140960795 + 2361380 * 2 ^ 59
def prefixEnd_2361380 : Nat := 4983230072969 + 3 ^ 40 * 2361380 * 2
def baseEnd_2361380 : Nat := 269449543980905849686715

theorem tailTrace_2361380 : CollatzResearch.WordTrace tailWord_2361380 prefixEnd_2361380 269449543980905849686715 := by
  unfold tailWord_2361380
  simp only [CollatzResearch.WordTrace]
  refine ⟨43063302092565513220712797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57417736123420684294283729 43063302092565513220712797)
  ·
    refine ⟨16148738284712067457767299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43063302092565513220712797 16148738284712067457767299)
    ·
      refine ⟨24223107427068101186650949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16148738284712067457767299 24223107427068101186650949)
      ·
        refine ⟨4541832642575268972497053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24223107427068101186650949 4541832642575268972497053)
        ·
          refine ⟨1703187240965725864686395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4541832642575268972497053 1703187240965725864686395)
          ·
            refine ⟨2554780861448588797029593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703187240965725864686395 2554780861448588797029593)
            ·
              refine ⟨1916085646086441597772195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2554780861448588797029593 1916085646086441597772195)
              ·
                refine ⟨2874128469129662396658293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1916085646086441597772195 2874128469129662396658293)
                ·
                  refine ⟨269449543980905849686715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2874128469129662396658293 269449543980905849686715)
                  ·
                    rfl

theorem cell22_2361380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_2361380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361380 prefixEnd_2361380 := by exact prefixLift 2361380
  have htrace : WordTrace (prefixWord ++ tailWord_2361380) baseStart_2361380 baseEnd_2361380 := by
    simpa [prefixWord, tailWord_2361380, baseEnd_2361380] using wordTrace_append hprefix tailTrace_2361380
  have hstable : (prefixWord ++ tailWord_2361380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361380).length < 2 ^ (prefixWord ++ tailWord_2361380).sum := by decide
  have hdescent : baseEnd_2361380 < baseStart_2361380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361387 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 1, 6]
def baseStart_2361387 : Nat := 118140960795 + 2361387 * 2 ^ 59
def prefixEnd_2361387 : Nat := 4983230072969 + 3 ^ 40 * 2361387 * 2
def baseEnd_2361387 : Nat := 808351028185771864135123

theorem tailTrace_2361387 : CollatzResearch.WordTrace tailWord_2361387 prefixEnd_2361387 808351028185771864135123 := by
  unfold tailWord_2361387
  simp only [CollatzResearch.WordTrace]
  refine ⟨86126859496105666636930415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57417906330737111091286943 86126859496105666636930415)
  ·
    refine ⟨129190289244158499955395623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86126859496105666636930415 129190289244158499955395623)
    ·
      refine ⟨193785433866237749933093435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129190289244158499955395623 193785433866237749933093435)
      ·
        refine ⟨290678150799356624899640153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193785433866237749933093435 290678150799356624899640153)
        ·
          refine ⟨218008613099517468674730115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290678150799356624899640153 218008613099517468674730115)
          ·
            refine ⟨327012919649276203012095173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218008613099517468674730115 327012919649276203012095173)
            ·
              refine ⟨61314922434239288064767845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 327012919649276203012095173 61314922434239288064767845)
              ·
                refine ⟨11496547956419866512143971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61314922434239288064767845 11496547956419866512143971)
                ·
                  refine ⟨17244821934629799768215957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11496547956419866512143971 17244821934629799768215957)
                  ·
                    refine ⟨808351028185771864135123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17244821934629799768215957 808351028185771864135123)
                    ·
                      rfl

theorem cell22_2361387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_2361387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361387 prefixEnd_2361387 := by exact prefixLift 2361387
  have htrace : WordTrace (prefixWord ++ tailWord_2361387) baseStart_2361387 baseEnd_2361387 := by
    simpa [prefixWord, tailWord_2361387, baseEnd_2361387] using wordTrace_append hprefix tailTrace_2361387
  have hstable : (prefixWord ++ tailWord_2361387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361387).length < 2 ^ (prefixWord ++ tailWord_2361387).sum := by decide
  have hdescent : baseEnd_2361387 < baseStart_2361387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361421 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2361421 : Nat := 118140960795 + 2361421 * 2 ^ 59
def prefixEnd_2361421 : Nat := 4983230072969 + 3 ^ 40 * 2361421 * 2
def baseEnd_2361421 : Nat := 808362667080607108785019

theorem tailTrace_2361421 : CollatzResearch.WordTrace tailWord_2361421 prefixEnd_2361421 808362667080607108785019 := by
  unfold tailWord_2361421
  simp only [CollatzResearch.WordTrace]
  refine ⟨86128099577982490443668117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57418733051988326962445411 86128099577982490443668117)
  ·
    refine ⟨4037254667717929239546943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86128099577982490443668117 4037254667717929239546943)
    ·
      refine ⟨6055882001576893859320415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4037254667717929239546943 6055882001576893859320415)
      ·
        refine ⟨9083823002365340788980623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6055882001576893859320415 9083823002365340788980623)
        ·
          refine ⟨13625734503548011183470935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9083823002365340788980623 13625734503548011183470935)
          ·
            refine ⟨20438601755322016775206403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13625734503548011183470935 20438601755322016775206403)
            ·
              refine ⟨30657902632983025162809605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20438601755322016775206403 30657902632983025162809605)
              ·
                refine ⟨5748356743684317218026801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30657902632983025162809605 5748356743684317218026801)
                ·
                  refine ⟨4311267557763237913520101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5748356743684317218026801 4311267557763237913520101)
                  ·
                    refine ⟨808362667080607108785019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4311267557763237913520101 808362667080607108785019)
                    ·
                      rfl

theorem cell22_2361421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2361421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361421 prefixEnd_2361421 := by exact prefixLift 2361421
  have htrace : WordTrace (prefixWord ++ tailWord_2361421) baseStart_2361421 baseEnd_2361421 := by
    simpa [prefixWord, tailWord_2361421, baseEnd_2361421] using wordTrace_append hprefix tailTrace_2361421
  have hstable : (prefixWord ++ tailWord_2361421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361421).length < 2 ^ (prefixWord ++ tailWord_2361421).sum := by decide
  have hdescent : baseEnd_2361421 < baseStart_2361421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361436 : List Nat := [2, 2, 4, 1, 1, 4, 1, 7]
def baseStart_2361436 : Nat := 118140960795 + 2361436 * 2 ^ 59
def prefixEnd_2361436 : Nat := 4983230072969 + 3 ^ 40 * 2361436 * 2
def baseEnd_2361436 : Nat := 89818644654128007739997

theorem tailTrace_2361436 : CollatzResearch.WordTrace tailWord_2361436 prefixEnd_2361436 89818644654128007739997 := by
  unfold tailWord_2361436
  simp only [CollatzResearch.WordTrace]
  refine ⟨43064323336464074002732081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57419097781952098670309441 43064323336464074002732081)
  ·
    refine ⟨32298242502348055502049061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43064323336464074002732081 32298242502348055502049061)
    ·
      refine ⟨6055920469190260406634199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32298242502348055502049061 6055920469190260406634199)
      ·
        refine ⟨9083880703785390609951299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6055920469190260406634199 9083880703785390609951299)
        ·
          refine ⟨13625821055678085914926949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9083880703785390609951299 13625821055678085914926949)
          ·
            refine ⟨2554841447939641109048803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13625821055678085914926949 2554841447939641109048803)
            ·
              refine ⟨3832262171909461663573205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554841447939641109048803 3832262171909461663573205)
              ·
                refine ⟨89818644654128007739997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3832262171909461663573205 89818644654128007739997)
                ·
                  rfl

theorem cell22_2361436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 7].length) (baseStart_2361436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361436 prefixEnd_2361436 := by exact prefixLift 2361436
  have htrace : WordTrace (prefixWord ++ tailWord_2361436) baseStart_2361436 baseEnd_2361436 := by
    simpa [prefixWord, tailWord_2361436, baseEnd_2361436] using wordTrace_append hprefix tailTrace_2361436
  have hstable : (prefixWord ++ tailWord_2361436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361436).length < 2 ^ (prefixWord ++ tailWord_2361436).sum := by decide
  have hdescent : baseEnd_2361436 < baseStart_2361436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361468 : List Nat := [2, 2, 2, 1, 1, 4, 1, 5, 1, 3]
def baseStart_2361468 : Nat := 118140960795 + 2361468 * 2 ^ 59
def prefixEnd_2361468 : Nat := 4983230072969 + 3 ^ 40 * 2361468 * 2
def baseEnd_2361468 : Nat := 808378756141114652859875

theorem tailTrace_2361468 : CollatzResearch.WordTrace tailWord_2361468 prefixEnd_2361468 808378756141114652859875 := by
  unfold tailWord_2361468
  simp only [CollatzResearch.WordTrace]
  refine ⟨43064906904406108735314529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57419875872541478313752705 43064906904406108735314529)
  ·
    refine ⟨32298680178304581551485897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43064906904406108735314529 32298680178304581551485897)
    ·
      refine ⟨24224010133728436163614423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32298680178304581551485897 24224010133728436163614423)
      ·
        refine ⟨36336015200592654245421635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24224010133728436163614423 36336015200592654245421635)
        ·
          refine ⟨54504022800888981368132453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36336015200592654245421635 54504022800888981368132453)
          ·
            refine ⟨10219504275166684006524835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54504022800888981368132453 10219504275166684006524835)
            ·
              refine ⟨15329256412750026009787253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10219504275166684006524835 15329256412750026009787253)
              ·
                refine ⟨1437117788695314938417555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15329256412750026009787253 1437117788695314938417555)
                ·
                  refine ⟨2155676683042972407626333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437117788695314938417555 2155676683042972407626333)
                  ·
                    refine ⟨808378756141114652859875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2155676683042972407626333 808378756141114652859875)
                    ·
                      rfl

theorem cell22_2361468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_2361468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361468 prefixEnd_2361468 := by exact prefixLift 2361468
  have htrace : WordTrace (prefixWord ++ tailWord_2361468) baseStart_2361468 baseEnd_2361468 := by
    simpa [prefixWord, tailWord_2361468, baseEnd_2361468] using wordTrace_append hprefix tailTrace_2361468
  have hstable : (prefixWord ++ tailWord_2361468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361468).length < 2 ^ (prefixWord ++ tailWord_2361468).sum := by decide
  have hdescent : baseEnd_2361468 < baseStart_2361468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361479 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2361479 : Nat := 118140960795 + 2361479 * 2 ^ 59
def prefixEnd_2361479 : Nat := 4983230072969 + 3 ^ 40 * 2361479 * 2
def baseEnd_2361479 : Nat := 808382521665914290834841

theorem tailTrace_2361479 : CollatzResearch.WordTrace tailWord_2361479 prefixEnd_2361479 808382521665914290834841 := by
  unfold tailWord_2361479
  simp only [CollatzResearch.WordTrace]
  refine ⟨86130215011772366349279491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57420143341181577566186327 86130215011772366349279491)
  ·
    refine ⟨129195322517658549523919237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86130215011772366349279491 129195322517658549523919237)
    ·
      refine ⟨24224122972060978035734857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129195322517658549523919237 24224122972060978035734857)
      ·
        refine ⟨18168092229045733526801143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24224122972060978035734857 18168092229045733526801143)
        ·
          refine ⟨27252138343568600290201715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18168092229045733526801143 27252138343568600290201715)
          ·
            refine ⟨40878207515352900435302573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27252138343568600290201715 40878207515352900435302573)
            ·
              refine ⟨15329327818257337663238465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40878207515352900435302573 15329327818257337663238465)
              ·
                refine ⟨11496995863693003247428849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15329327818257337663238465 11496995863693003247428849)
                ·
                  refine ⟨8622746897769752435571637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11496995863693003247428849 8622746897769752435571637)
                  ·
                    refine ⟨808382521665914290834841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8622746897769752435571637 808382521665914290834841)
                    ·
                      rfl

theorem cell22_2361479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2361479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361479 prefixEnd_2361479 := by exact prefixLift 2361479
  have htrace : WordTrace (prefixWord ++ tailWord_2361479) baseStart_2361479 baseEnd_2361479 := by
    simpa [prefixWord, tailWord_2361479, baseEnd_2361479] using wordTrace_append hprefix tailTrace_2361479
  have hstable : (prefixWord ++ tailWord_2361479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361479).length < 2 ^ (prefixWord ++ tailWord_2361479).sum := by decide
  have hdescent : baseEnd_2361479 < baseStart_2361479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361509 : List Nat := [1, 3, 1, 2, 1, 3, 1, 4, 6]
def baseStart_2361509 : Nat := 118140960795 + 2361509 * 2 ^ 59
def prefixEnd_2361509 : Nat := 4983230072969 + 3 ^ 40 * 2361509 * 2
def baseEnd_2361509 : Nat := 269464263759668070861583

theorem tailTrace_2361509 : CollatzResearch.WordTrace tailWord_2361509 prefixEnd_2361509 269464263759668070861583 := by
  unfold tailWord_2361509
  simp only [CollatzResearch.WordTrace]
  refine ⟨86131309201663681472871581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57420872801109120981914387 86131309201663681472871581)
  ·
    refine ⟨32299240950623880552326843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86131309201663681472871581 32299240950623880552326843)
    ·
      refine ⟨48448861425935820828490265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32299240950623880552326843 48448861425935820828490265)
      ·
        refine ⟨36336646069451865621367699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48448861425935820828490265 36336646069451865621367699)
        ·
          refine ⟨54504969104177798432051549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36336646069451865621367699 54504969104177798432051549)
          ·
            refine ⟨20439363414066674412019331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54504969104177798432051549 20439363414066674412019331)
            ·
              refine ⟨30659045121100011618028997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20439363414066674412019331 30659045121100011618028997)
              ·
                refine ⟨5748570960206252178380437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30659045121100011618028997 5748570960206252178380437)
                ·
                  refine ⟨269464263759668070861583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5748570960206252178380437 269464263759668070861583)
                  ·
                    rfl

theorem cell22_2361509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_2361509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361509 prefixEnd_2361509 := by exact prefixLift 2361509
  have htrace : WordTrace (prefixWord ++ tailWord_2361509) baseStart_2361509 baseEnd_2361509 := by
    simpa [prefixWord, tailWord_2361509, baseEnd_2361509] using wordTrace_append hprefix tailTrace_2361509
  have hstable : (prefixWord ++ tailWord_2361509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361509).length < 2 ^ (prefixWord ++ tailWord_2361509).sum := by decide
  have hdescent : baseEnd_2361509 < baseStart_2361509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361541 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 4, 3]
def baseStart_2361541 : Nat := 118140960795 + 2361541 * 2 ^ 59
def prefixEnd_2361541 : Nat := 4983230072969 + 3 ^ 40 * 2361541 * 2
def baseEnd_2361541 : Nat := 808403745532966795784651

theorem tailTrace_2361541 : CollatzResearch.WordTrace tailWord_2361541 prefixEnd_2361541 808403745532966795784651 := by
  unfold tailWord_2361541
  simp only [CollatzResearch.WordTrace]
  refine ⟨86132476337547750938036477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57421650891698500625357651 86132476337547750938036477)
  ·
    refine ⟨32299678626580406601763679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86132476337547750938036477 32299678626580406601763679)
    ·
      refine ⟨48449517939870609902645519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32299678626580406601763679 48449517939870609902645519)
      ·
        refine ⟨72674276909805914853968279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48449517939870609902645519 72674276909805914853968279)
        ·
          refine ⟨109011415364708872280952419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72674276909805914853968279 109011415364708872280952419)
          ·
            refine ⟨163517123047063308421428629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109011415364708872280952419 163517123047063308421428629)
            ·
              refine ⟨7664865142831092582254467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163517123047063308421428629 7664865142831092582254467)
              ·
                refine ⟨11497297714246638873381701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7664865142831092582254467 11497297714246638873381701)
                ·
                  refine ⟨2155743321421244788759069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11497297714246638873381701 2155743321421244788759069)
                  ·
                    refine ⟨808403745532966795784651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2155743321421244788759069 808403745532966795784651)
                    ·
                      rfl

theorem cell22_2361541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_2361541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361541 prefixEnd_2361541 := by exact prefixLift 2361541
  have htrace : WordTrace (prefixWord ++ tailWord_2361541) baseStart_2361541 baseEnd_2361541 := by
    simpa [prefixWord, tailWord_2361541, baseEnd_2361541] using wordTrace_append hprefix tailTrace_2361541
  have hstable : (prefixWord ++ tailWord_2361541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361541).length < 2 ^ (prefixWord ++ tailWord_2361541).sum := by decide
  have hdescent : baseEnd_2361541 < baseStart_2361541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361573 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_2361573 : Nat := 118140960795 + 2361573 * 2 ^ 59
def prefixEnd_2361573 : Nat := 4983230072969 + 3 ^ 40 * 2361573 * 2
def baseEnd_2361573 : Nat := 808414699786929378984553

theorem tailTrace_2361573 : CollatzResearch.WordTrace tailWord_2361573 prefixEnd_2361573 808414699786929378984553 := by
  unfold tailWord_2361573
  simp only [CollatzResearch.WordTrace]
  refine ⟨86133643473431820403201373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57422428982287880268800915 86133643473431820403201373)
  ·
    refine ⟨32300116302536932651200515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86133643473431820403201373 32300116302536932651200515)
    ·
      refine ⟨48450174453805398976800773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32300116302536932651200515 48450174453805398976800773)
      ·
        refine ⟨9084407710088512308150145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48450174453805398976800773 9084407710088512308150145)
        ·
          refine ⟨6813305782566384231112609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9084407710088512308150145 6813305782566384231112609)
          ·
            refine ⟨5109979336924788173334457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6813305782566384231112609 5109979336924788173334457)
            ·
              refine ⟨3832484502693591130000843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5109979336924788173334457 3832484502693591130000843)
              ·
                refine ⟨5748726754040386695001265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832484502693591130000843 5748726754040386695001265)
                ·
                  refine ⟨4311545065530290021250949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5748726754040386695001265 4311545065530290021250949)
                  ·
                    refine ⟨808414699786929378984553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4311545065530290021250949 808414699786929378984553)
                    ·
                      rfl

theorem cell22_2361573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_2361573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361573 prefixEnd_2361573 := by exact prefixLift 2361573
  have htrace : WordTrace (prefixWord ++ tailWord_2361573) baseStart_2361573 baseEnd_2361573 := by
    simpa [prefixWord, tailWord_2361573, baseEnd_2361573] using wordTrace_append hprefix tailTrace_2361573
  have hstable : (prefixWord ++ tailWord_2361573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361573).length < 2 ^ (prefixWord ++ tailWord_2361573).sum := by decide
  have hdescent : baseEnd_2361573 < baseStart_2361573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361584 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_2361584 : Nat := 118140960795 + 2361584 * 2 ^ 59
def prefixEnd_2361584 : Nat := 4983230072969 + 3 ^ 40 * 2361584 * 2
def baseEnd_2361584 : Nat := 808418465311729016959519

theorem tailTrace_2361584 : CollatzResearch.WordTrace tailWord_2361584 prefixEnd_2361584 808418465311729016959519 := by
  unfold tailWord_2361584
  simp only [CollatzResearch.WordTrace]
  refine ⟨43067022338195984640925903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57422696450927979521234537 43067022338195984640925903)
  ·
    refine ⟨64600533507293976961388855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43067022338195984640925903 64600533507293976961388855)
    ·
      refine ⟨96900800260940965442083283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64600533507293976961388855 96900800260940965442083283)
      ·
        refine ⟨145351200391411448163124925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96900800260940965442083283 145351200391411448163124925)
        ·
          refine ⟨54506700146779293061171847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145351200391411448163124925 54506700146779293061171847)
          ·
            refine ⟨81760050220168939591757771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54506700146779293061171847 81760050220168939591757771)
            ·
              refine ⟨122640075330253409387636657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81760050220168939591757771 122640075330253409387636657)
              ·
                refine ⟨91980056497690057040727493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122640075330253409387636657 91980056497690057040727493)
                ·
                  refine ⟨17246260593316885695136405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91980056497690057040727493 17246260593316885695136405)
                  ·
                    refine ⟨808418465311729016959519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17246260593316885695136405 808418465311729016959519)
                    ·
                      rfl

theorem cell22_2361584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_2361584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361584 prefixEnd_2361584 := by exact prefixLift 2361584
  have htrace : WordTrace (prefixWord ++ tailWord_2361584) baseStart_2361584 baseEnd_2361584 := by
    simpa [prefixWord, tailWord_2361584, baseEnd_2361584] using wordTrace_append hprefix tailTrace_2361584
  have hstable : (prefixWord ++ tailWord_2361584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361584).length < 2 ^ (prefixWord ++ tailWord_2361584).sum := by decide
  have hdescent : baseEnd_2361584 < baseStart_2361584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361637 : List Nat := [1, 3, 1, 2, 5, 1, 2, 3, 1, 3]
def baseStart_2361637 : Nat := 118140960795 + 2361637 * 2 ^ 59
def prefixEnd_2361637 : Nat := 4983230072969 + 3 ^ 40 * 2361637 * 2
def baseEnd_2361637 : Nat := 808436608294854545384357

theorem tailTrace_2361637 : CollatzResearch.WordTrace tailWord_2361637 prefixEnd_2361637 808436608294854545384357 := by
  unfold tailWord_2361637
  simp only [CollatzResearch.WordTrace]
  refine ⟨86135977745199959333531165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57423985163466639555687443 86135977745199959333531165)
  ·
    refine ⟨32300991654449984750074187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86135977745199959333531165 32300991654449984750074187)
    ·
      refine ⟨48451487481674977125111281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32300991654449984750074187 48451487481674977125111281)
      ·
        refine ⟨36338615611256232843833461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48451487481674977125111281 36338615611256232843833461)
        ·
          refine ⟨3406745213555271829109387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36338615611256232843833461 3406745213555271829109387)
          ·
            refine ⟨5110117820332907743664081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406745213555271829109387 5110117820332907743664081)
            ·
              refine ⟨3832588365249680807748061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5110117820332907743664081 3832588365249680807748061)
              ·
                refine ⟨1437220636968630302905523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3832588365249680807748061 1437220636968630302905523)
                ·
                  refine ⟨2155830955452945454358285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437220636968630302905523 2155830955452945454358285)
                  ·
                    refine ⟨808436608294854545384357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2155830955452945454358285 808436608294854545384357)
                    ·
                      rfl

theorem cell22_2361637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_2361637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361637 prefixEnd_2361637 := by exact prefixLift 2361637
  have htrace : WordTrace (prefixWord ++ tailWord_2361637) baseStart_2361637 baseEnd_2361637 := by
    simpa [prefixWord, tailWord_2361637, baseEnd_2361637] using wordTrace_append hprefix tailTrace_2361637
  have hstable : (prefixWord ++ tailWord_2361637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361637).length < 2 ^ (prefixWord ++ tailWord_2361637).sum := by decide
  have hdescent : baseEnd_2361637 < baseStart_2361637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361650 : List Nat := [3, 2, 1, 1, 5, 2, 1, 2, 5]
def baseStart_2361650 : Nat := 118140960795 + 2361650 * 2 ^ 59
def prefixEnd_2361650 : Nat := 4983230072969 + 3 ^ 40 * 2361650 * 2
def baseEnd_2361650 : Nat := 269480352820175614936439

theorem tailTrace_2361650 : CollatzResearch.WordTrace tailWord_2361650 prefixEnd_2361650 269480352820175614936439 := by
  unfold tailWord_2361650
  simp only [CollatzResearch.WordTrace]
  refine ⟨21534112973538215638438601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57424301262768575035836269 21534112973538215638438601)
  ·
    refine ⟨16150584730153661728828951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21534112973538215638438601 16150584730153661728828951)
    ·
      refine ⟨24225877095230492593243427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16150584730153661728828951 24225877095230492593243427)
      ·
        refine ⟨36338815642845738889865141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24225877095230492593243427 36338815642845738889865141)
        ·
          refine ⟨3406763966516788020924857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36338815642845738889865141 3406763966516788020924857)
          ·
            refine ⟨2555072974887591015693643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3406763966516788020924857 2555072974887591015693643)
            ·
              refine ⟨3832609462331386523540465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555072974887591015693643 3832609462331386523540465)
              ·
                refine ⟨2874457096748539892655349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3832609462331386523540465 2874457096748539892655349)
                ·
                  refine ⟨269480352820175614936439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2874457096748539892655349 269480352820175614936439)
                  ·
                    rfl

theorem cell22_2361650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_2361650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361650 prefixEnd_2361650 := by exact prefixLift 2361650
  have htrace : WordTrace (prefixWord ++ tailWord_2361650) baseStart_2361650 baseEnd_2361650 := by
    simpa [prefixWord, tailWord_2361650, baseEnd_2361650] using wordTrace_append hprefix tailTrace_2361650
  have hstable : (prefixWord ++ tailWord_2361650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361650).length < 2 ^ (prefixWord ++ tailWord_2361650).sum := by decide
  have hdescent : baseEnd_2361650 < baseStart_2361650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361751 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 9]
def baseStart_2361751 : Nat := 118140960795 + 2361751 * 2 ^ 59
def prefixEnd_2361751 : Nat := 4983230072969 + 3 ^ 40 * 2361751 * 2
def baseEnd_2361751 : Nat := 269491877608198749344669

theorem tailTrace_2361751 : CollatzResearch.WordTrace tailWord_2361751 prefixEnd_2361751 269491877608198749344669 := by
  unfold tailWord_2361751
  simp only [CollatzResearch.WordTrace]
  refine ⟨86140135666786956803181107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57426757111191304535454071 86140135666786956803181107)
  ·
    refine ⟨129210203500180435204771661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86140135666786956803181107 129210203500180435204771661)
    ·
      refine ⟨48453826312567663201789373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129210203500180435204771661 48453826312567663201789373)
      ·
        refine ⟨18170184867212873700671015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48453826312567663201789373 18170184867212873700671015)
        ·
          refine ⟨27255277300819310551006523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18170184867212873700671015 27255277300819310551006523)
          ·
            refine ⟨40882915951228965826509785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27255277300819310551006523 40882915951228965826509785)
            ·
              refine ⟨30662186963421724369882339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40882915951228965826509785 30662186963421724369882339)
              ·
                refine ⟨45993280445132586554823509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30662186963421724369882339 45993280445132586554823509)
                ·
                  refine ⟨269491877608198749344669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45993280445132586554823509 269491877608198749344669)
                  ·
                    rfl

theorem cell22_2361751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 9].length) (baseStart_2361751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361751 prefixEnd_2361751 := by exact prefixLift 2361751
  have htrace : WordTrace (prefixWord ++ tailWord_2361751) baseStart_2361751 baseEnd_2361751 := by
    simpa [prefixWord, tailWord_2361751, baseEnd_2361751] using wordTrace_append hprefix tailTrace_2361751
  have hstable : (prefixWord ++ tailWord_2361751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361751).length < 2 ^ (prefixWord ++ tailWord_2361751).sum := by decide
  have hdescent : baseEnd_2361751 < baseStart_2361751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361783 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 2, 5]
def baseStart_2361783 : Nat := 118140960795 + 2361783 * 2 ^ 59
def prefixEnd_2361783 : Nat := 4983230072969 + 3 ^ 40 * 2361783 * 2
def baseEnd_2361783 : Nat := 808486587078558831233909

theorem tailTrace_2361783 : CollatzResearch.WordTrace tailWord_2361783 prefixEnd_2361783 808486587078558831233909 := by
  unfold tailWord_2361783
  simp only [CollatzResearch.WordTrace]
  refine ⟨86141302802671026268346003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57427535201780684178897335 86141302802671026268346003)
  ·
    refine ⟨129211954204006539402519005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86141302802671026268346003 129211954204006539402519005)
    ·
      refine ⟨48454482826502452275944627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129211954204006539402519005 48454482826502452275944627)
      ·
        refine ⟨72681724239753678413916941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48454482826502452275944627 72681724239753678413916941)
        ·
          refine ⟨27255646589907629405218853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72681724239753678413916941 27255646589907629405218853)
          ·
            refine ⟨5110433735607680513478535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27255646589907629405218853 5110433735607680513478535)
            ·
              refine ⟨7665650603411520770217803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5110433735607680513478535 7665650603411520770217803)
              ·
                refine ⟨11498475905117281155326705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7665650603411520770217803 11498475905117281155326705)
                ·
                  refine ⟨8623856928837960866495029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11498475905117281155326705 8623856928837960866495029)
                  ·
                    refine ⟨808486587078558831233909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8623856928837960866495029 808486587078558831233909)
                    ·
                      rfl

theorem cell22_2361783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_2361783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361783 prefixEnd_2361783 := by exact prefixLift 2361783
  have htrace : WordTrace (prefixWord ++ tailWord_2361783) baseStart_2361783 baseEnd_2361783 := by
    simpa [prefixWord, tailWord_2361783, baseEnd_2361783] using wordTrace_append hprefix tailTrace_2361783
  have hstable : (prefixWord ++ tailWord_2361783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361783).length < 2 ^ (prefixWord ++ tailWord_2361783).sum := by decide
  have hdescent : baseEnd_2361783 < baseStart_2361783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361811 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 4, 9]
def baseStart_2361811 : Nat := 118140960795 + 2361811 * 2 ^ 59
def prefixEnd_2361811 : Nat := 4983230072969 + 3 ^ 40 * 2361811 * 2
def baseEnd_2361811 : Nat := 808496172050776091533823

theorem tailTrace_2361811 : CollatzResearch.WordTrace tailWord_2361811 prefixEnd_2361811 808496172050776091533823 := by
  unfold tailWord_2361811
  simp only [CollatzResearch.WordTrace]
  refine ⟨86142324046569587050365287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57428216031046391366910191 86142324046569587050365287)
  ·
    refine ⟨129213486069854380575547931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86142324046569587050365287 129213486069854380575547931)
    ·
      refine ⟨193820229104781570863321897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129213486069854380575547931 193820229104781570863321897)
      ·
        refine ⟨145365171828586178147491423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193820229104781570863321897 145365171828586178147491423)
        ·
          refine ⟨218047757742879267221237135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145365171828586178147491423 218047757742879267221237135)
          ·
            refine ⟨327071636614318900831855703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218047757742879267221237135 327071636614318900831855703)
            ·
              refine ⟨490607454921478351247783555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327071636614318900831855703 490607454921478351247783555)
              ·
                refine ⟨735911182382217526871675333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 490607454921478351247783555 735911182382217526871675333)
                ·
                  refine ⟨137983346696665786288439125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 735911182382217526871675333 137983346696665786288439125)
                  ·
                    refine ⟨808496172050776091533823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 137983346696665786288439125 808496172050776091533823)
                    ·
                      rfl

theorem cell22_2361811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_2361811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361811 prefixEnd_2361811 := by exact prefixLift 2361811
  have htrace : WordTrace (prefixWord ++ tailWord_2361811) baseStart_2361811 baseEnd_2361811 := by
    simpa [prefixWord, tailWord_2361811, baseEnd_2361811] using wordTrace_append hprefix tailTrace_2361811
  have hstable : (prefixWord ++ tailWord_2361811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361811).length < 2 ^ (prefixWord ++ tailWord_2361811).sum := by decide
  have hdescent : baseEnd_2361811 < baseStart_2361811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361860 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_2361860 : Nat := 118140960795 + 2361860 * 2 ^ 59
def prefixEnd_2361860 : Nat := 4983230072969 + 3 ^ 40 * 2361860 * 2
def baseEnd_2361860 : Nat := 808512945752156297058673

theorem tailTrace_2361860 : CollatzResearch.WordTrace tailWord_2361860 prefixEnd_2361860 808512945752156297058673 := by
  unfold tailWord_2361860
  simp only [CollatzResearch.WordTrace]
  refine ⟨43072055611696034209449517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57429407482261378945932689 43072055611696034209449517)
  ·
    refine ⟨16152020854386012828543569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43072055611696034209449517 16152020854386012828543569)
    ·
      refine ⟨12114015640789509621407677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16152020854386012828543569 12114015640789509621407677)
      ·
        refine ⟨4542755865296066108027879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12114015640789509621407677 4542755865296066108027879)
        ·
          refine ⟨6814133797944099162041819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4542755865296066108027879 6814133797944099162041819)
          ·
            refine ⟨10221200696916148743062729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6814133797944099162041819 10221200696916148743062729)
            ·
              refine ⟨7665900522687111557297047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10221200696916148743062729 7665900522687111557297047)
              ·
                refine ⟨11498850784030667335945571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7665900522687111557297047 11498850784030667335945571)
                ·
                  refine ⟨17248276176046001003918357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11498850784030667335945571 17248276176046001003918357)
                  ·
                    refine ⟨808512945752156297058673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17248276176046001003918357 808512945752156297058673)
                    ·
                      rfl

theorem cell22_2361860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_2361860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361860 prefixEnd_2361860 := by exact prefixLift 2361860
  have htrace : WordTrace (prefixWord ++ tailWord_2361860) baseStart_2361860 baseEnd_2361860 := by
    simpa [prefixWord, tailWord_2361860, baseEnd_2361860] using wordTrace_append hprefix tailTrace_2361860
  have hstable : (prefixWord ++ tailWord_2361860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361860).length < 2 ^ (prefixWord ++ tailWord_2361860).sum := by decide
  have hdescent : baseEnd_2361860 < baseStart_2361860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361892 : List Nat := [2, 3, 1, 5, 1, 1, 2, 7]
def baseStart_2361892 : Nat := 118140960795 + 2361892 * 2 ^ 59
def prefixEnd_2361892 : Nat := 4983230072969 + 3 ^ 40 * 2361892 * 2
def baseEnd_2361892 : Nat := 89835988889568764473175

theorem tailTrace_2361892 : CollatzResearch.WordTrace tailWord_2361892 prefixEnd_2361892 89835988889568764473175 := by
  unfold tailWord_2361892
  simp only [CollatzResearch.WordTrace]
  refine ⟨43072639179638068942031965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57430185572850758589375953 43072639179638068942031965)
  ·
    refine ⟨16152239692364275853261987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43072639179638068942031965 16152239692364275853261987)
    ·
      refine ⟨24228359538546413779892981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16152239692364275853261987 24228359538546413779892981)
      ·
        refine ⟨2271408706738726291864967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24228359538546413779892981 2271408706738726291864967)
        ·
          refine ⟨3407113060108089437797451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271408706738726291864967 3407113060108089437797451)
          ·
            refine ⟨5110669590162134156696177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3407113060108089437797451 5110669590162134156696177)
            ·
              refine ⟨3833002192621600617522133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5110669590162134156696177 3833002192621600617522133)
              ·
                refine ⟨89835988889568764473175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3833002192621600617522133 89835988889568764473175)
                ·
                  rfl

theorem cell22_2361892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 7].length) (baseStart_2361892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361892 prefixEnd_2361892 := by exact prefixLift 2361892
  have htrace : WordTrace (prefixWord ++ tailWord_2361892) baseStart_2361892 baseEnd_2361892 := by
    simpa [prefixWord, tailWord_2361892, baseEnd_2361892] using wordTrace_append hprefix tailTrace_2361892
  have hstable : (prefixWord ++ tailWord_2361892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361892).length < 2 ^ (prefixWord ++ tailWord_2361892).sum := by decide
  have hdescent : baseEnd_2361892 < baseStart_2361892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361896 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 2, 3]
def baseStart_2361896 : Nat := 118140960795 + 2361896 * 2 ^ 59
def prefixEnd_2361896 : Nat := 4983230072969 + 3 ^ 40 * 2361896 * 2
def baseEnd_2361896 : Nat := 808525269287864203158563

theorem tailTrace_2361896 : CollatzResearch.WordTrace tailWord_2361896 prefixEnd_2361896 808525269287864203158563 := by
  unfold tailWord_2361896
  simp only [CollatzResearch.WordTrace]
  refine ⟨43072712125630823283604771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57430282834174431044806361 43072712125630823283604771)
  ·
    refine ⟨64609068188446234925407157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43072712125630823283604771 64609068188446234925407157)
    ·
      refine ⟨6057100142666834524256921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64609068188446234925407157 6057100142666834524256921)
      ·
        refine ⟨4542825107000125893192691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6057100142666834524256921 4542825107000125893192691)
        ·
          refine ⟨6814237660500188839789037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4542825107000125893192691 6814237660500188839789037)
          ·
            refine ⟨2555339122687570814920889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6814237660500188839789037 2555339122687570814920889)
            ·
              refine ⟨1916504342015678111190667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2555339122687570814920889 1916504342015678111190667)
              ·
                refine ⟨2874756513023517166786001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1916504342015678111190667 2874756513023517166786001)
                ·
                  refine ⟨2156067384767637875089501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2874756513023517166786001 2156067384767637875089501)
                  ·
                    refine ⟨808525269287864203158563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156067384767637875089501 808525269287864203158563)
                    ·
                      rfl

theorem cell22_2361896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_2361896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361896 prefixEnd_2361896 := by exact prefixLift 2361896
  have htrace : WordTrace (prefixWord ++ tailWord_2361896) baseStart_2361896 baseEnd_2361896 := by
    simpa [prefixWord, tailWord_2361896, baseEnd_2361896] using wordTrace_append hprefix tailTrace_2361896
  have hstable : (prefixWord ++ tailWord_2361896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361896).length < 2 ^ (prefixWord ++ tailWord_2361896).sum := by decide
  have hdescent : baseEnd_2361896 < baseStart_2361896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361965 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 8]
def baseStart_2361965 : Nat := 118140960795 + 2361965 * 2 ^ 59
def prefixEnd_2361965 : Nat := 4983230072969 + 3 ^ 40 * 2361965 * 2
def baseEnd_2361965 : Nat := 269516296465990341061117

theorem tailTrace_2361965 : CollatzResearch.WordTrace tailWord_2361965 prefixEnd_2361965 269516296465990341061117 := by
  unfold tailWord_2361965
  simp only [CollatzResearch.WordTrace]
  refine ⟨86147940888011671351471349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57431960592007780900980899 86147940888011671351471349)
  ·
    refine ⟨8076369458251094189200439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86147940888011671351471349 8076369458251094189200439)
    ·
      refine ⟨12114554187376641283800659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8076369458251094189200439 12114554187376641283800659)
      ·
        refine ⟨18171831281064961925700989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12114554187376641283800659 18171831281064961925700989)
        ·
          refine ⟨6814436730399360722137871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18171831281064961925700989 6814436730399360722137871)
          ·
            refine ⟨10221655095599041083206807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6814436730399360722137871 10221655095599041083206807)
            ·
              refine ⟨15332482643398561624810211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10221655095599041083206807 15332482643398561624810211)
              ·
                refine ⟨22998723965097842437215317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15332482643398561624810211 22998723965097842437215317)
                ·
                  refine ⟨269516296465990341061117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22998723965097842437215317 269516296465990341061117)
                  ·
                    rfl

theorem cell22_2361965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_2361965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361965 prefixEnd_2361965 := by exact prefixLift 2361965
  have htrace : WordTrace (prefixWord ++ tailWord_2361965) baseStart_2361965 baseEnd_2361965 := by
    simpa [prefixWord, tailWord_2361965, baseEnd_2361965] using wordTrace_append hprefix tailTrace_2361965
  have hstable : (prefixWord ++ tailWord_2361965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361965).length < 2 ^ (prefixWord ++ tailWord_2361965).sum := by decide
  have hdescent : baseEnd_2361965 < baseStart_2361965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361980 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_2361980 : Nat := 118140960795 + 2361980 * 2 ^ 59
def prefixEnd_2361980 : Nat := 4983230072969 + 3 ^ 40 * 2361980 * 2
def baseEnd_2361980 : Nat := 808554024204515984058305

theorem tailTrace_2361980 : CollatzResearch.WordTrace tailWord_2361980 prefixEnd_2361980 808554024204515984058305 := by
  unfold tailWord_2361980
  simp only [CollatzResearch.WordTrace]
  refine ⟨43074243991478664456633697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57432325321971552608844929 43074243991478664456633697)
  ·
    refine ⟨32305682993608998342475273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43074243991478664456633697 32305682993608998342475273)
    ·
      refine ⟨24229262245206748756856455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32305682993608998342475273 24229262245206748756856455)
      ·
        refine ⟨36343893367810123135284683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24229262245206748756856455 36343893367810123135284683)
        ·
          refine ⟨54515840051715184702927025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36343893367810123135284683 54515840051715184702927025)
          ·
            refine ⟨40886880038786388527195269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54515840051715184702927025 40886880038786388527195269)
            ·
              refine ⟨7666290007272447848849113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40886880038786388527195269 7666290007272447848849113)
              ·
                refine ⟨5749717505454335886636835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7666290007272447848849113 5749717505454335886636835)
                ·
                  refine ⟨8624576258181503829955253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5749717505454335886636835 8624576258181503829955253)
                  ·
                    refine ⟨808554024204515984058305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8624576258181503829955253 808554024204515984058305)
                    ·
                      rfl

theorem cell22_2361980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_2361980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361980 prefixEnd_2361980 := by exact prefixLift 2361980
  have htrace : WordTrace (prefixWord ++ tailWord_2361980) baseStart_2361980 baseEnd_2361980 := by
    simpa [prefixWord, tailWord_2361980, baseEnd_2361980] using wordTrace_append hprefix tailTrace_2361980
  have hstable : (prefixWord ++ tailWord_2361980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361980).length < 2 ^ (prefixWord ++ tailWord_2361980).sum := by decide
  have hdescent : baseEnd_2361980 < baseStart_2361980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361984 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 1, 4]
def baseStart_2361984 : Nat := 118140960795 + 2361984 * 2 ^ 59
def prefixEnd_2361984 : Nat := 4983230072969 + 3 ^ 40 * 2361984 * 2
def baseEnd_2361984 : Nat := 808555393486261306958293

theorem tailTrace_2361984 : CollatzResearch.WordTrace tailWord_2361984 prefixEnd_2361984 808555393486261306958293 := by
  unfold tailWord_2361984
  simp only [CollatzResearch.WordTrace]
  refine ⟨43074316937471418798206503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57432422583295225064275337 43074316937471418798206503)
  ·
    refine ⟨64611475406207128197309755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43074316937471418798206503 64611475406207128197309755)
    ·
      refine ⟨96917213109310692295964633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64611475406207128197309755 96917213109310692295964633)
      ·
        refine ⟨72687909831983019221973475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96917213109310692295964633 72687909831983019221973475)
        ·
          refine ⟨109031864747974528832960213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72687909831983019221973475 109031864747974528832960213)
          ·
            refine ⟨2555434330030653019522505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 109031864747974528832960213 2555434330030653019522505)
            ·
              refine ⟨1916575747522989764641879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2555434330030653019522505 1916575747522989764641879)
              ·
                refine ⟨2874863621284484646962819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1916575747522989764641879 2874863621284484646962819)
                ·
                  refine ⟨4312295431926726970444229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874863621284484646962819 4312295431926726970444229)
                  ·
                    refine ⟨808555393486261306958293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4312295431926726970444229 808555393486261306958293)
                    ·
                      rfl

theorem cell22_2361984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 4].length) (baseStart_2361984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2361984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2361984 prefixEnd_2361984 := by exact prefixLift 2361984
  have htrace : WordTrace (prefixWord ++ tailWord_2361984) baseStart_2361984 baseEnd_2361984 := by
    simpa [prefixWord, tailWord_2361984, baseEnd_2361984] using wordTrace_append hprefix tailTrace_2361984
  have hstable : (prefixWord ++ tailWord_2361984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361984).length < 2 ^ (prefixWord ++ tailWord_2361984).sum := by decide
  have hdescent : baseEnd_2361984 < baseStart_2361984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362033 : List Nat := [1, 2, 2, 6, 2, 1, 1, 3, 4]
def baseStart_2362033 : Nat := 118140960795 + 2362033 * 2 ^ 59
def prefixEnd_2362033 : Nat := 4983230072969 + 3 ^ 40 * 2362033 * 2
def baseEnd_2362033 : Nat := 269524055729213837494381

theorem tailTrace_2362033 : CollatzResearch.WordTrace tailWord_2362033 prefixEnd_2362033 269524055729213837494381 := by
  unfold tailWord_2362033
  simp only [CollatzResearch.WordTrace]
  refine ⟨86150421051765318964946753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57433614034510212643297835 86150421051765318964946753)
  ·
    refine ⟨64612815788823989223710065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86150421051765318964946753 64612815788823989223710065)
    ·
      refine ⟨48459611841617991917782549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64612815788823989223710065 48459611841617991917782549)
      ·
        refine ⟨2271544305075843371146057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48459611841617991917782549 2271544305075843371146057)
        ·
          refine ⟨1703658228806882528359543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2271544305075843371146057 1703658228806882528359543)
          ·
            refine ⟨2555487343210323792539315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703658228806882528359543 2555487343210323792539315)
            ·
              refine ⟨3833231014815485688808973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555487343210323792539315 3833231014815485688808973)
              ·
                refine ⟨1437461630555807133303365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3833231014815485688808973 1437461630555807133303365)
                ·
                  refine ⟨269524055729213837494381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1437461630555807133303365 269524055729213837494381)
                  ·
                    rfl

theorem cell22_2362033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 3, 4].length) (baseStart_2362033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362033 prefixEnd_2362033 := by exact prefixLift 2362033
  have htrace : WordTrace (prefixWord ++ tailWord_2362033) baseStart_2362033 baseEnd_2362033 := by
    simpa [prefixWord, tailWord_2362033, baseEnd_2362033] using wordTrace_append hprefix tailTrace_2362033
  have hstable : (prefixWord ++ tailWord_2362033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362033).length < 2 ^ (prefixWord ++ tailWord_2362033).sum := by decide
  have hdescent : baseEnd_2362033 < baseStart_2362033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362072 : List Nat := [2, 1, 2, 2, 3, 3, 1, 3, 5]
def baseStart_2362072 : Nat := 118140960795 + 2362072 * 2 ^ 59
def prefixEnd_2362072 : Nat := 4983230072969 + 3 ^ 40 * 2362072 * 2
def baseEnd_2362072 : Nat := 269528505894886136919341

theorem tailTrace_2362072 : CollatzResearch.WordTrace tailWord_2362072 prefixEnd_2362072 269528505894886136919341 := by
  unfold tailWord_2362072
  simp only [CollatzResearch.WordTrace]
  refine ⟨43075921749312014312808235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57434562332416019083744313 43075921749312014312808235)
  ·
    refine ⟨64613882623968021469212353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43075921749312014312808235 64613882623968021469212353)
    ·
      refine ⟨48460411967976016101909265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64613882623968021469212353 48460411967976016101909265)
      ·
        refine ⟨36345308975982012076431949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48460411967976016101909265 36345308975982012076431949)
        ·
          refine ⟨13629490865993254528661981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36345308975982012076431949 13629490865993254528661981)
          ·
            refine ⟨5111059074747470448248243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13629490865993254528661981 5111059074747470448248243)
            ·
              refine ⟨7666588612121205672372365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5111059074747470448248243 7666588612121205672372365)
              ·
                refine ⟨2874970729545452127139637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7666588612121205672372365 2874970729545452127139637)
                ·
                  refine ⟨269528505894886136919341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2874970729545452127139637 269528505894886136919341)
                  ·
                    rfl

theorem cell22_2362072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_2362072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362072 prefixEnd_2362072 := by exact prefixLift 2362072
  have htrace : WordTrace (prefixWord ++ tailWord_2362072) baseStart_2362072 baseEnd_2362072 := by
    simpa [prefixWord, tailWord_2362072, baseEnd_2362072] using wordTrace_append hprefix tailTrace_2362072
  have hstable : (prefixWord ++ tailWord_2362072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362072).length < 2 ^ (prefixWord ++ tailWord_2362072).sum := by decide
  have hdescent : baseEnd_2362072 < baseStart_2362072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362110 : List Nat := [4, 2, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_2362110 : Nat := 118140960795 + 2362110 * 2 ^ 59
def prefixEnd_2362110 : Nat := 4983230072969 + 3 ^ 40 * 2362110 * 2
def baseEnd_2362110 : Nat := 808598525861238978307907

theorem tailTrace_2362110 : CollatzResearch.WordTrace tailWord_2362110 prefixEnd_2362110 808598525861238978307907 := by
  unfold tailWord_2362110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10769153684060795139437473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57435486314990907410333189 10769153684060795139437473)
  ·
    refine ⟨8076865263045596354578105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10769153684060795139437473 8076865263045596354578105)
    ·
      refine ⟨6057648947284197265933579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8076865263045596354578105 6057648947284197265933579)
      ·
        refine ⟨9086473420926295898900369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6057648947284197265933579 9086473420926295898900369)
        ·
          refine ⟨6814855065694721924175277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9086473420926295898900369 6814855065694721924175277)
          ·
            refine ⟨2555570649635520721565729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6814855065694721924175277 2555570649635520721565729)
            ·
              refine ⟨1916677987226640541174297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2555570649635520721565729 1916677987226640541174297)
              ·
                refine ⟨1437508490419980405880723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1916677987226640541174297 1437508490419980405880723)
                ·
                  refine ⟨2156262735629970608821085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437508490419980405880723 2156262735629970608821085)
                  ·
                    refine ⟨808598525861238978307907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156262735629970608821085 808598525861238978307907)
                    ·
                      rfl

theorem cell22_2362110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_2362110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362110 prefixEnd_2362110 := by exact prefixLift 2362110
  have htrace : WordTrace (prefixWord ++ tailWord_2362110) baseStart_2362110 baseEnd_2362110 := by
    simpa [prefixWord, tailWord_2362110, baseEnd_2362110] using wordTrace_append hprefix tailTrace_2362110
  have hstable : (prefixWord ++ tailWord_2362110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362110).length < 2 ^ (prefixWord ++ tailWord_2362110).sum := by decide
  have hdescent : baseEnd_2362110 < baseStart_2362110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362115 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 5, 5]
def baseStart_2362115 : Nat := 118140960795 + 2362115 * 2 ^ 59
def prefixEnd_2362115 : Nat := 4983230072969 + 3 ^ 40 * 2362115 * 2
def baseEnd_2362115 : Nat := 808600237463420631932891

theorem tailTrace_2362115 : CollatzResearch.WordTrace tailWord_2362115 prefixEnd_2362115 808600237463420631932891 := by
  unfold tailWord_2362115
  simp only [CollatzResearch.WordTrace]
  refine ⟨86153411837468246969431799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57435607891645497979621199 86153411837468246969431799)
  ·
    refine ⟨129230117756202370454147699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86153411837468246969431799 129230117756202370454147699)
    ·
      refine ⟨193845176634303555681221549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129230117756202370454147699 193845176634303555681221549)
      ·
        refine ⟨72691941237863833380458081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193845176634303555681221549 72691941237863833380458081)
        ·
          refine ⟨54518955928397875035343561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72691941237863833380458081 54518955928397875035343561)
          ·
            refine ⟨40889216946298406276507671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54518955928397875035343561 40889216946298406276507671)
            ·
              refine ⟨61333825419447609414761507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40889216946298406276507671 61333825419447609414761507)
              ·
                refine ⟨92000738129171414122142261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61333825419447609414761507 92000738129171414122142261)
                ·
                  refine ⟨8625069199609820073950837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92000738129171414122142261 8625069199609820073950837)
                  ·
                    refine ⟨808600237463420631932891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8625069199609820073950837 808600237463420631932891)
                    ·
                      rfl

theorem cell22_2362115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_2362115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362115 prefixEnd_2362115 := by exact prefixLift 2362115
  have htrace : WordTrace (prefixWord ++ tailWord_2362115) baseStart_2362115 baseEnd_2362115 := by
    simpa [prefixWord, tailWord_2362115, baseEnd_2362115] using wordTrace_append hprefix tailTrace_2362115
  have hstable : (prefixWord ++ tailWord_2362115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362115).length < 2 ^ (prefixWord ++ tailWord_2362115).sum := by decide
  have hdescent : baseEnd_2362115 < baseStart_2362115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362160 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_2362160 : Nat := 118140960795 + 2362160 * 2 ^ 59
def prefixEnd_2362160 : Nat := 4983230072969 + 3 ^ 40 * 2362160 * 2
def baseEnd_2362160 : Nat := 808615641883055514557753

theorem tailTrace_2362160 : CollatzResearch.WordTrace tailWord_2362160 prefixEnd_2362160 808615641883055514557753 := by
  unfold tailWord_2362160
  simp only [CollatzResearch.WordTrace]
  refine ⟨43077526561152609827409967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57436702081536813103213289 43077526561152609827409967)
  ·
    refine ⟨64616289841728914741114951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43077526561152609827409967 64616289841728914741114951)
    ·
      refine ⟨96924434762593372111672427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64616289841728914741114951 96924434762593372111672427)
      ·
        refine ⟨145386652143890058167508641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96924434762593372111672427 145386652143890058167508641)
        ·
          refine ⟨109039989107917543625631481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145386652143890058167508641 109039989107917543625631481)
          ·
            refine ⟨81779991830938157719223611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109039989107917543625631481 81779991830938157719223611)
            ·
              refine ⟨122669987746407236578835417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81779991830938157719223611 122669987746407236578835417)
              ·
                refine ⟨92002490809805427434126563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122669987746407236578835417 92002490809805427434126563)
                ·
                  refine ⟨138003736214708141151189845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92002490809805427434126563 138003736214708141151189845)
                  ·
                    refine ⟨808615641883055514557753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 138003736214708141151189845 808615641883055514557753)
                    ·
                      rfl

theorem cell22_2362160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_2362160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362160 prefixEnd_2362160 := by exact prefixLift 2362160
  have htrace : WordTrace (prefixWord ++ tailWord_2362160) baseStart_2362160 baseEnd_2362160 := by
    simpa [prefixWord, tailWord_2362160, baseEnd_2362160] using wordTrace_append hprefix tailTrace_2362160
  have hstable : (prefixWord ++ tailWord_2362160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362160).length < 2 ^ (prefixWord ++ tailWord_2362160).sum := by decide
  have hdescent : baseEnd_2362160 < baseStart_2362160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362194 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 3, 3]
def baseStart_2362194 : Nat := 118140960795 + 2362194 * 2 ^ 59
def prefixEnd_2362194 : Nat := 4983230072969 + 3 ^ 40 * 2362194 * 2
def baseEnd_2362194 : Nat := 808627280777890759207649

theorem tailTrace_2362194 : CollatzResearch.WordTrace tailWord_2362194 prefixEnd_2362194 808627280777890759207649 := by
  unfold tailWord_2362194
  simp only [CollatzResearch.WordTrace]
  refine ⟨21539073301045510865389409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57437528802788028974371757 21539073301045510865389409)
  ·
    refine ⟨16154304975784133149042057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21539073301045510865389409 16154304975784133149042057)
    ·
      refine ⟨12115728731838099861781543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16154304975784133149042057 12115728731838099861781543)
      ·
        refine ⟨18173593097757149792672315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12115728731838099861781543 18173593097757149792672315)
        ·
          refine ⟨27260389646635724689008473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18173593097757149792672315 27260389646635724689008473)
          ·
            refine ⟨20445292234976793516756355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27260389646635724689008473 20445292234976793516756355)
            ·
              refine ⟨30667938352465190275134533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20445292234976793516756355 30667938352465190275134533)
              ·
                refine ⟨5750238441087223176587725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30667938352465190275134533 5750238441087223176587725)
                ·
                  refine ⟨2156339415407708691220397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5750238441087223176587725 2156339415407708691220397)
                  ·
                    refine ⟨808627280777890759207649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156339415407708691220397 808627280777890759207649)
                    ·
                      rfl

theorem cell22_2362194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_2362194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362194 prefixEnd_2362194 := by exact prefixLift 2362194
  have htrace : WordTrace (prefixWord ++ tailWord_2362194) baseStart_2362194 baseEnd_2362194 := by
    simpa [prefixWord, tailWord_2362194, baseEnd_2362194] using wordTrace_append hprefix tailTrace_2362194
  have hstable : (prefixWord ++ tailWord_2362194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362194).length < 2 ^ (prefixWord ++ tailWord_2362194).sum := by decide
  have hdescent : baseEnd_2362194 < baseStart_2362194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362196 : List Nat := [2, 4, 1, 1, 4, 2, 2, 6]
def baseStart_2362196 : Nat := 118140960795 + 2362196 * 2 ^ 59
def prefixEnd_2362196 : Nat := 4983230072969 + 3 ^ 40 * 2362196 * 2
def baseEnd_2362196 : Nat := 89847551713195935628627

theorem tailTrace_2362196 : CollatzResearch.WordTrace tailWord_2362196 prefixEnd_2362196 89847551713195935628627 := by
  unfold tailWord_2362196
  simp only [CollatzResearch.WordTrace]
  refine ⟨43078183075087398901565221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57437577433449865202086961 43078183075087398901565221)
  ·
    refine ⟨8077159326578887294043479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43078183075087398901565221 8077159326578887294043479)
    ·
      refine ⟨12115738989868330941065219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8077159326578887294043479 12115738989868330941065219)
      ·
        refine ⟨18173608484802496411597829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12115738989868330941065219 18173608484802496411597829)
        ·
          refine ⟨3407551590900468077174593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18173608484802496411597829 3407551590900468077174593)
          ·
            refine ⟨2555663693175351057880945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3407551590900468077174593 2555663693175351057880945)
            ·
              refine ⟨1916747769881513293410709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2555663693175351057880945 1916747769881513293410709)
              ·
                refine ⟨89847551713195935628627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1916747769881513293410709 89847551713195935628627)
                ·
                  rfl

theorem cell22_2362196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 6].length) (baseStart_2362196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362196 prefixEnd_2362196 := by exact prefixLift 2362196
  have htrace : WordTrace (prefixWord ++ tailWord_2362196) baseStart_2362196 baseEnd_2362196 := by
    simpa [prefixWord, tailWord_2362196, baseEnd_2362196] using wordTrace_append hprefix tailTrace_2362196
  have hstable : (prefixWord ++ tailWord_2362196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362196).length < 2 ^ (prefixWord ++ tailWord_2362196).sum := by decide
  have hdescent : baseEnd_2362196 < baseStart_2362196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362252 : List Nat := [2, 2, 1, 2, 1, 2, 2, 4, 6]
def baseStart_2362252 : Nat := 118140960795 + 2362252 * 2 ^ 59
def prefixEnd_2362252 : Nat := 4983230072969 + 3 ^ 40 * 2362252 * 2
def baseEnd_2362252 : Nat := 269549045121065980419157

theorem tailTrace_2362252 : CollatzResearch.WordTrace tailWord_2362252 prefixEnd_2362252 269549045121065980419157 := by
  unfold tailWord_2362252
  simp only [CollatzResearch.WordTrace]
  refine ⟨43079204318985959683584505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57438939091981279578112673 43079204318985959683584505)
  ·
    refine ⟨32309403239239469762688379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43079204318985959683584505 32309403239239469762688379)
    ·
      refine ⟨48464104858859204644032569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32309403239239469762688379 48464104858859204644032569)
      ·
        refine ⟨36348078644144403483024427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48464104858859204644032569 36348078644144403483024427)
        ·
          refine ⟨54522117966216605224536641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36348078644144403483024427 54522117966216605224536641)
          ·
            refine ⟨40891588474662453918402481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54522117966216605224536641 40891588474662453918402481)
            ·
              refine ⟨30668691355996840438801861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40891588474662453918402481 30668691355996840438801861)
              ·
                refine ⟨5750379629249407582275349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30668691355996840438801861 5750379629249407582275349)
                ·
                  refine ⟨269549045121065980419157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5750379629249407582275349 269549045121065980419157)
                  ·
                    rfl

theorem cell22_2362252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_2362252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362252 prefixEnd_2362252 := by exact prefixLift 2362252
  have htrace : WordTrace (prefixWord ++ tailWord_2362252) baseStart_2362252 baseEnd_2362252 := by
    simpa [prefixWord, tailWord_2362252, baseEnd_2362252] using wordTrace_append hprefix tailTrace_2362252
  have hstable : (prefixWord ++ tailWord_2362252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362252).length < 2 ^ (prefixWord ++ tailWord_2362252).sum := by decide
  have hdescent : baseEnd_2362252 < baseStart_2362252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362301 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_2362301 : Nat := 118140960795 + 2362301 * 2 ^ 59
def prefixEnd_2362301 : Nat := 4983230072969 + 3 ^ 40 * 2362301 * 2
def baseEnd_2362301 : Nat := 808663909064578146782321

theorem tailTrace_2362301 : CollatzResearch.WordTrace tailWord_2362301 prefixEnd_2362301 808663909064578146782321 := by
  unfold tailWord_2362301
  simp only [CollatzResearch.WordTrace]
  refine ⟨86160195814794400735702757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57440130543196267157135171 86160195814794400735702757)
  ·
    refine ⟨16155036715273950137944267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86160195814794400735702757 16155036715273950137944267)
    ·
      refine ⟨24232555072910925206916401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16155036715273950137944267 24232555072910925206916401)
      ·
        refine ⟨18174416304683193905187301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24232555072910925206916401 18174416304683193905187301)
        ·
          refine ⟨3407703057128098857222619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18174416304683193905187301 3407703057128098857222619)
          ·
            refine ⟨5111554585692148285833929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3407703057128098857222619 5111554585692148285833929)
            ·
              refine ⟨3833665939269111214375447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5111554585692148285833929 3833665939269111214375447)
              ·
                refine ⟨5750498908903666821563171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3833665939269111214375447 5750498908903666821563171)
                ·
                  refine ⟨8625748363355500232344757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5750498908903666821563171 8625748363355500232344757)
                  ·
                    refine ⟨808663909064578146782321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8625748363355500232344757 808663909064578146782321)
                    ·
                      rfl

theorem cell22_2362301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_2362301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362301 prefixEnd_2362301 := by exact prefixLift 2362301
  have htrace : WordTrace (prefixWord ++ tailWord_2362301) baseStart_2362301 baseEnd_2362301 := by
    simpa [prefixWord, tailWord_2362301, baseEnd_2362301] using wordTrace_append hprefix tailTrace_2362301
  have hstable : (prefixWord ++ tailWord_2362301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362301).length < 2 ^ (prefixWord ++ tailWord_2362301).sum := by decide
  have hdescent : baseEnd_2362301 < baseStart_2362301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362327 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 1, 8]
def baseStart_2362327 : Nat := 118140960795 + 2362327 * 2 ^ 59
def prefixEnd_2362327 : Nat := 4983230072969 + 3 ^ 40 * 2362327 * 2
def baseEnd_2362327 : Nat := 808672809395922745632241

theorem tailTrace_2362327 : CollatzResearch.WordTrace tailWord_2362327 prefixEnd_2362327 808672809395922745632241 := by
  unfold tailWord_2362327
  simp only [CollatzResearch.WordTrace]
  refine ⟨86161144112700207176149235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57440762741800138117432823 86161144112700207176149235)
  ·
    refine ⟨129241716169050310764223853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86161144112700207176149235 129241716169050310764223853)
    ·
      refine ⟨48465643563393866536583945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129241716169050310764223853 48465643563393866536583945)
      ·
        refine ⟨36349232672545399902437959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48465643563393866536583945 36349232672545399902437959)
        ·
          refine ⟨54523849008818099853656939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36349232672545399902437959 54523849008818099853656939)
          ·
            refine ⟨81785773513227149780485409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54523849008818099853656939 81785773513227149780485409)
            ·
              refine ⟨61339330134920362335364057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81785773513227149780485409 61339330134920362335364057)
              ·
                refine ⟨46004497601190271751523043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61339330134920362335364057 46004497601190271751523043)
                ·
                  refine ⟨69006746401785407627284565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46004497601190271751523043 69006746401785407627284565)
                  ·
                    refine ⟨808672809395922745632241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69006746401785407627284565 808672809395922745632241)
                    ·
                      rfl

theorem cell22_2362327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_2362327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362327 prefixEnd_2362327 := by exact prefixLift 2362327
  have htrace : WordTrace (prefixWord ++ tailWord_2362327) baseStart_2362327 baseEnd_2362327 := by
    simpa [prefixWord, tailWord_2362327, baseEnd_2362327] using wordTrace_append hprefix tailTrace_2362327
  have hstable : (prefixWord ++ tailWord_2362327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362327).length < 2 ^ (prefixWord ++ tailWord_2362327).sum := by decide
  have hdescent : baseEnd_2362327 < baseStart_2362327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362335 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 2, 3]
def baseStart_2362335 : Nat := 118140960795 + 2362335 * 2 ^ 59
def prefixEnd_2362335 : Nat := 4983230072969 + 3 ^ 40 * 2362335 * 2
def baseEnd_2362335 : Nat := 808675547959413391432217

theorem tailTrace_2362335 : CollatzResearch.WordTrace tailWord_2362335 prefixEnd_2362335 808675547959413391432217 := by
  unfold tailWord_2362335
  simp only [CollatzResearch.WordTrace]
  refine ⟨86161435896671224542440459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57440957264447483028293639 86161435896671224542440459)
  ·
    refine ⟨129242153845006836813660689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86161435896671224542440459 129242153845006836813660689)
    ·
      refine ⟨96931615383755127610245517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129242153845006836813660689 96931615383755127610245517)
      ·
        refine ⟨36349355768908172853842069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96931615383755127610245517 36349355768908172853842069)
        ·
          refine ⟨1703876051667570602523847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36349355768908172853842069 1703876051667570602523847)
          ·
            refine ⟨2555814077501355903785771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703876051667570602523847 2555814077501355903785771)
            ·
              refine ⟨3833721116252033855678657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555814077501355903785771 3833721116252033855678657)
              ·
                refine ⟨2875290837189025391758993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3833721116252033855678657 2875290837189025391758993)
                ·
                  refine ⟨2156468127891769043819245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2875290837189025391758993 2156468127891769043819245)
                  ·
                    refine ⟨808675547959413391432217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156468127891769043819245 808675547959413391432217)
                    ·
                      rfl

theorem cell22_2362335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 2, 3].length) (baseStart_2362335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362335 prefixEnd_2362335 := by exact prefixLift 2362335
  have htrace : WordTrace (prefixWord ++ tailWord_2362335) baseStart_2362335 baseEnd_2362335 := by
    simpa [prefixWord, tailWord_2362335, baseEnd_2362335] using wordTrace_append hprefix tailTrace_2362335
  have hstable : (prefixWord ++ tailWord_2362335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362335).length < 2 ^ (prefixWord ++ tailWord_2362335).sum := by decide
  have hdescent : baseEnd_2362335 < baseStart_2362335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362346 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 3, 3]
def baseStart_2362346 : Nat := 118140960795 + 2362346 * 2 ^ 59
def prefixEnd_2362346 : Nat := 4983230072969 + 3 ^ 40 * 2362346 * 2
def baseEnd_2362346 : Nat := 808679313484213029407183

theorem tailTrace_2362346 : CollatzResearch.WordTrace tailWord_2362346 prefixEnd_2362346 808679313484213029407183 := by
  unfold tailWord_2362346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21540459274907843355272723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57441224733087582280727261 21540459274907843355272723)
  ·
    refine ⟨32310688912361765032909085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21540459274907843355272723 32310688912361765032909085)
    ·
      refine ⟨12116508342135661887340907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32310688912361765032909085 12116508342135661887340907)
      ·
        refine ⟨18174762513203492831011361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12116508342135661887340907 18174762513203492831011361)
        ·
          refine ⟨13631071884902619623258521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18174762513203492831011361 13631071884902619623258521)
          ·
            refine ⟨10223303913676964717443891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13631071884902619623258521 10223303913676964717443891)
            ·
              refine ⟨15334955870515447076165837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10223303913676964717443891 15334955870515447076165837)
              ·
                refine ⟨5750608451443292653562189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15334955870515447076165837 5750608451443292653562189)
                ·
                  refine ⟨2156478169291234745085821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5750608451443292653562189 2156478169291234745085821)
                  ·
                    refine ⟨808679313484213029407183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156478169291234745085821 808679313484213029407183)
                    ·
                      rfl

theorem cell22_2362346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_2362346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362346 prefixEnd_2362346 := by exact prefixLift 2362346
  have htrace : WordTrace (prefixWord ++ tailWord_2362346) baseStart_2362346 baseEnd_2362346 := by
    simpa [prefixWord, tailWord_2362346, baseEnd_2362346] using wordTrace_append hprefix tailTrace_2362346
  have hstable : (prefixWord ++ tailWord_2362346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362346).length < 2 ^ (prefixWord ++ tailWord_2362346).sum := by decide
  have hdescent : baseEnd_2362346 < baseStart_2362346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362380 : List Nat := [2, 2, 1, 2, 3, 4, 1, 3, 1, 3]
def baseStart_2362380 : Nat := 118140960795 + 2362380 * 2 ^ 59
def prefixEnd_2362380 : Nat := 4983230072969 + 3 ^ 40 * 2362380 * 2
def baseEnd_2362380 : Nat := 808690952379048274057079

theorem tailTrace_2362380 : CollatzResearch.WordTrace tailWord_2362380 prefixEnd_2362380 808690952379048274057079 := by
  unfold tailWord_2362380
  simp only [CollatzResearch.WordTrace]
  refine ⟨43081538590754098613914297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57442051454338798151885729 43081538590754098613914297)
  ·
    refine ⟨32311153943065573960435723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43081538590754098613914297 32311153943065573960435723)
    ·
      refine ⟨48466730914598360940653585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32311153943065573960435723 48466730914598360940653585)
      ·
        refine ⟨36350048185948770705490189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48466730914598360940653585 36350048185948770705490189)
        ·
          refine ⟨13631268069730789014558821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36350048185948770705490189 13631268069730789014558821)
          ·
            refine ⟨2555862763074522940229779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13631268069730789014558821 2555862763074522940229779)
            ·
              refine ⟨3833794144611784410344669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555862763074522940229779 3833794144611784410344669)
              ·
                refine ⟨1437672804229419153879251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3833794144611784410344669 1437672804229419153879251)
                ·
                  refine ⟨2156509206344128730818877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437672804229419153879251 2156509206344128730818877)
                  ·
                    refine ⟨808690952379048274057079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156509206344128730818877 808690952379048274057079)
                    ·
                      rfl

theorem cell22_2362380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_2362380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362380 prefixEnd_2362380 := by exact prefixLift 2362380
  have htrace : WordTrace (prefixWord ++ tailWord_2362380) baseStart_2362380 baseEnd_2362380 := by
    simpa [prefixWord, tailWord_2362380, baseEnd_2362380] using wordTrace_append hprefix tailTrace_2362380
  have hstable : (prefixWord ++ tailWord_2362380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362380).length < 2 ^ (prefixWord ++ tailWord_2362380).sum := by decide
  have hdescent : baseEnd_2362380 < baseStart_2362380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362397 : List Nat := [1, 4, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_2362397 : Nat := 118140960795 + 2362397 * 2 ^ 59
def prefixEnd_2362397 : Nat := 4983230072969 + 3 ^ 40 * 2362397 * 2
def baseEnd_2362397 : Nat := 808696771826465896382027

theorem tailTrace_2362397 : CollatzResearch.WordTrace tailWord_2362397 prefixEnd_2362397 808696771826465896382027 := by
  unfold tailWord_2362397
  simp only [CollatzResearch.WordTrace]
  refine ⟨86163697222446609131197445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57442464814964406087464963 86163697222446609131197445)
  ·
    refine ⟨16155693229208739212099521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86163697222446609131197445 16155693229208739212099521)
    ·
      refine ⟨12116769921906554409074641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16155693229208739212099521 12116769921906554409074641)
      ·
        refine ⟨9087577441429915806805981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12116769921906554409074641 9087577441429915806805981)
        ·
          refine ⟨3407841540536218427552243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9087577441429915806805981 3407841540536218427552243)
          ·
            refine ⟨5111762310804327641328365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3407841540536218427552243 5111762310804327641328365)
            ·
              refine ⟨1916910866551622865498137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5111762310804327641328365 1916910866551622865498137)
              ·
                refine ⟨1437683149913717149123603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1916910866551622865498137 1437683149913717149123603)
                ·
                  refine ⟨2156524724870575723685405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437683149913717149123603 2156524724870575723685405)
                  ·
                    refine ⟨808696771826465896382027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156524724870575723685405 808696771826465896382027)
                    ·
                      rfl

theorem cell22_2362397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_2362397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362397 prefixEnd_2362397 := by exact prefixLift 2362397
  have htrace : WordTrace (prefixWord ++ tailWord_2362397) baseStart_2362397 baseEnd_2362397 := by
    simpa [prefixWord, tailWord_2362397, baseEnd_2362397] using wordTrace_append hprefix tailTrace_2362397
  have hstable : (prefixWord ++ tailWord_2362397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362397).length < 2 ^ (prefixWord ++ tailWord_2362397).sum := by decide
  have hdescent : baseEnd_2362397 < baseStart_2362397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362410 : List Nat := [3, 1, 4, 1, 3, 2, 2, 1, 5]
def baseStart_2362410 : Nat := 118140960795 + 2362410 * 2 ^ 59
def prefixEnd_2362410 : Nat := 4983230072969 + 3 ^ 40 * 2362410 * 2
def baseEnd_2362410 : Nat := 269567073997379398602329

theorem tailTrace_2362410 : CollatzResearch.WordTrace tailWord_2362410 prefixEnd_2362410 269567073997379398602329 := by
  unfold tailWord_2362410
  simp only [CollatzResearch.WordTrace]
  refine ⟨21541042842849878087855171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57442780914266341567613789 21541042842849878087855171)
  ·
    refine ⟨32311564264274817131782757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21541042842849878087855171 32311564264274817131782757)
    ·
      refine ⟨6058418299551528212209267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32311564264274817131782757 6058418299551528212209267)
      ·
        refine ⟨9087627449327292318313901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6058418299551528212209267 9087627449327292318313901)
        ·
          refine ⟨3407860293497734619367713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9087627449327292318313901 3407860293497734619367713)
          ·
            refine ⟨2555895220123300964525785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3407860293497734619367713 2555895220123300964525785)
            ·
              refine ⟨1916921415092475723394339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2555895220123300964525785 1916921415092475723394339)
              ·
                refine ⟨2875382122638713585091509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1916921415092475723394339 2875382122638713585091509)
                ·
                  refine ⟨269567073997379398602329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2875382122638713585091509 269567073997379398602329)
                  ·
                    rfl

theorem cell22_2362410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_2362410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362410 prefixEnd_2362410 := by exact prefixLift 2362410
  have htrace : WordTrace (prefixWord ++ tailWord_2362410) baseStart_2362410 baseEnd_2362410 := by
    simpa [prefixWord, tailWord_2362410, baseEnd_2362410] using wordTrace_append hprefix tailTrace_2362410
  have hstable : (prefixWord ++ tailWord_2362410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362410).length < 2 ^ (prefixWord ++ tailWord_2362410).sum := by decide
  have hdescent : baseEnd_2362410 < baseStart_2362410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362419 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 1, 5]
def baseStart_2362419 : Nat := 118140960795 + 2362419 * 2 ^ 59
def prefixEnd_2362419 : Nat := 4983230072969 + 3 ^ 40 * 2362419 * 2
def baseEnd_2362419 : Nat := 808704302876065172331959

theorem tailTrace_2362419 : CollatzResearch.WordTrace tailWord_2362419 prefixEnd_2362419 808704302876065172331959 := by
  unfold tailWord_2362419
  simp only [CollatzResearch.WordTrace]
  refine ⟨86164499628366906888498311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57442999752244604592332207 86164499628366906888498311)
  ·
    refine ⟨129246749442550360332747467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86164499628366906888498311 129246749442550360332747467)
    ·
      refine ⟨193870124163825540499121201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129246749442550360332747467 193870124163825540499121201)
      ·
        refine ⟨145402593122869155374340901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193870124163825540499121201 145402593122869155374340901)
        ·
          refine ⟨27262986210537966632688919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 145402593122869155374340901 27262986210537966632688919)
          ·
            refine ⟨40894479315806949949033379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27262986210537966632688919 40894479315806949949033379)
            ·
              refine ⟨61341718973710424923550069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40894479315806949949033379 61341718973710424923550069)
              ·
                refine ⟨5750786153785352336582819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61341718973710424923550069 5750786153785352336582819)
                ·
                  refine ⟨8626179230678028504874229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5750786153785352336582819 8626179230678028504874229)
                  ·
                    refine ⟨808704302876065172331959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8626179230678028504874229 808704302876065172331959)
                    ·
                      rfl

theorem cell22_2362419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 5].length) (baseStart_2362419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362419 prefixEnd_2362419 := by exact prefixLift 2362419
  have htrace : WordTrace (prefixWord ++ tailWord_2362419) baseStart_2362419 baseEnd_2362419 := by
    simpa [prefixWord, tailWord_2362419, baseEnd_2362419] using wordTrace_append hprefix tailTrace_2362419
  have hstable : (prefixWord ++ tailWord_2362419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362419).length < 2 ^ (prefixWord ++ tailWord_2362419).sum := by decide
  have hdescent : baseEnd_2362419 < baseStart_2362419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362453 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 2, 3]
def baseStart_2362453 : Nat := 118140960795 + 2362453 * 2 ^ 59
def prefixEnd_2362453 : Nat := 4983230072969 + 3 ^ 40 * 2362453 * 2
def baseEnd_2362453 : Nat := 808715941770900416981855

theorem tailTrace_2362453 : CollatzResearch.WordTrace tailWord_2362453 prefixEnd_2362453 808715941770900416981855 := by
  unfold tailWord_2362453
  simp only [CollatzResearch.WordTrace]
  refine ⟨86165739710243730695236013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57443826473495820463490675 86165739710243730695236013)
  ·
    refine ⟨32312152391341399010713505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86165739710243730695236013 32312152391341399010713505)
    ·
      refine ⟨24234114293506049258035129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32312152391341399010713505 24234114293506049258035129)
      ·
        refine ⟨18175585720129536943526347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24234114293506049258035129 18175585720129536943526347)
        ·
          refine ⟨27263378580194305415289521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18175585720129536943526347 27263378580194305415289521)
          ·
            refine ⟨20447533935145729061467141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27263378580194305415289521 20447533935145729061467141)
            ·
              refine ⟨3833912612839824199025089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20447533935145729061467141 3833912612839824199025089)
              ·
                refine ⟨2875434459629868149268817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3833912612839824199025089 2875434459629868149268817)
                ·
                  refine ⟨2156575844722401111951613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2875434459629868149268817 2156575844722401111951613)
                  ·
                    refine ⟨808715941770900416981855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156575844722401111951613 808715941770900416981855)
                    ·
                      rfl

theorem cell22_2362453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_2362453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362453 prefixEnd_2362453 := by exact prefixLift 2362453
  have htrace : WordTrace (prefixWord ++ tailWord_2362453) baseStart_2362453 baseEnd_2362453 := by
    simpa [prefixWord, tailWord_2362453, baseEnd_2362453] using wordTrace_append hprefix tailTrace_2362453
  have hstable : (prefixWord ++ tailWord_2362453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362453).length < 2 ^ (prefixWord ++ tailWord_2362453).sum := by decide
  have hdescent : baseEnd_2362453 < baseStart_2362453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362479 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 2, 6]
def baseStart_2362479 : Nat := 118140960795 + 2362479 * 2 ^ 59
def prefixEnd_2362479 : Nat := 4983230072969 + 3 ^ 40 * 2362479 * 2
def baseEnd_2362479 : Nat := 808724842102245015831775

theorem tailTrace_2362479 : CollatzResearch.WordTrace tailWord_2362479 prefixEnd_2362479 808724842102245015831775 := by
  unfold tailWord_2362479
  simp only [CollatzResearch.WordTrace]
  refine ⟨86166688008149537135682491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57444458672099691423788327 86166688008149537135682491)
  ·
    refine ⟨129250032012224305703523737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86166688008149537135682491 129250032012224305703523737)
    ·
      refine ⟨96937524009168229277642803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129250032012224305703523737 96937524009168229277642803)
      ·
        refine ⟨145406286013752343916464205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96937524009168229277642803 145406286013752343916464205)
        ·
          refine ⟨54527357255157128968674077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145406286013752343916464205 54527357255157128968674077)
          ·
            refine ⟨20447758970683923363252779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54527357255157128968674077 20447758970683923363252779)
            ·
              refine ⟨30671638456025885044879169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20447758970683923363252779 30671638456025885044879169)
              ·
                refine ⟨23003728842019413783659377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30671638456025885044879169 23003728842019413783659377)
                ·
                  refine ⟨17252796631514560337744533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23003728842019413783659377 17252796631514560337744533)
                  ·
                    refine ⟨808724842102245015831775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17252796631514560337744533 808724842102245015831775)
                    ·
                      rfl

theorem cell22_2362479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_2362479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362479 prefixEnd_2362479 := by exact prefixLift 2362479
  have htrace : WordTrace (prefixWord ++ tailWord_2362479) baseStart_2362479 baseEnd_2362479 := by
    simpa [prefixWord, tailWord_2362479, baseEnd_2362479] using wordTrace_append hprefix tailTrace_2362479
  have hstable : (prefixWord ++ tailWord_2362479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362479).length < 2 ^ (prefixWord ++ tailWord_2362479).sum := by decide
  have hdescent : baseEnd_2362479 < baseStart_2362479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362528 : List Nat := [2, 1, 1, 4, 2, 1, 5, 1, 5]
def baseStart_2362528 : Nat := 118140960795 + 2362528 * 2 ^ 59
def prefixEnd_2362528 : Nat := 4983230072969 + 3 ^ 40 * 2362528 * 2
def baseEnd_2362528 : Nat := 269580538601208407118875

theorem tailTrace_2362528 : CollatzResearch.WordTrace tailWord_2362528 prefixEnd_2362528 269580538601208407118875 := by
  unfold tailWord_2362528
  simp only [CollatzResearch.WordTrace]
  refine ⟨43084237592486009252108119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57445650123314679002810825 43084237592486009252108119)
  ·
    refine ⟨64626356388729013878162179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43084237592486009252108119 64626356388729013878162179)
    ·
      refine ⟨96939534583093520817243269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64626356388729013878162179 96939534583093520817243269)
      ·
        refine ⟨18176162734330035153233113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96939534583093520817243269 18176162734330035153233113)
        ·
          refine ⟨13632122050747526364924835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18176162734330035153233113 13632122050747526364924835)
          ·
            refine ⟨20448183076121289547387253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13632122050747526364924835 20448183076121289547387253)
            ·
              refine ⟨1917017163386370895067555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20448183076121289547387253 1917017163386370895067555)
              ·
                refine ⟨2875525745079556342601333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917017163386370895067555 2875525745079556342601333)
                ·
                  refine ⟨269580538601208407118875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2875525745079556342601333 269580538601208407118875)
                  ·
                    rfl

theorem cell22_2362528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 1, 5].length) (baseStart_2362528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362528 prefixEnd_2362528 := by exact prefixLift 2362528
  have htrace : WordTrace (prefixWord ++ tailWord_2362528) baseStart_2362528 baseEnd_2362528 := by
    simpa [prefixWord, tailWord_2362528, baseEnd_2362528] using wordTrace_append hprefix tailTrace_2362528
  have hstable : (prefixWord ++ tailWord_2362528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362528).length < 2 ^ (prefixWord ++ tailWord_2362528).sum := by decide
  have hdescent : baseEnd_2362528 < baseStart_2362528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362566 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2362566 : Nat := 118140960795 + 2362566 * 2 ^ 59
def prefixEnd_2362566 : Nat := 4983230072969 + 3 ^ 40 * 2362566 * 2
def baseEnd_2362566 : Nat := 808754623980205788906509

theorem tailTrace_2362566 : CollatzResearch.WordTrace tailWord_2362566 prefixEnd_2362566 808754623980205788906509 := by
  unfold tailWord_2362566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2692808161213573468565611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57446574105889567329399701 2692808161213573468565611)
  ·
    refine ⟨4039212241820360202848417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2692808161213573468565611 4039212241820360202848417)
    ·
      refine ⟨3029409181365270152136313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4039212241820360202848417 3029409181365270152136313)
      ·
        refine ⟨2272056886023952614102235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3029409181365270152136313 2272056886023952614102235)
        ·
          refine ⟨3408085329035928921153353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272056886023952614102235 3408085329035928921153353)
          ·
            refine ⟨2556063996776946690865015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408085329035928921153353 2556063996776946690865015)
            ·
              refine ⟨3834095995165420036297523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556063996776946690865015 3834095995165420036297523)
              ·
                refine ⟨5751143992748130054446285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3834095995165420036297523 5751143992748130054446285)
                ·
                  refine ⟨2156678997280548770417357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5751143992748130054446285 2156678997280548770417357)
                  ·
                    refine ⟨808754623980205788906509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156678997280548770417357 808754623980205788906509)
                    ·
                      rfl

theorem cell22_2362566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2362566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362566 prefixEnd_2362566 := by exact prefixLift 2362566
  have htrace : WordTrace (prefixWord ++ tailWord_2362566) baseStart_2362566 baseEnd_2362566 := by
    simpa [prefixWord, tailWord_2362566, baseEnd_2362566] using wordTrace_append hprefix tailTrace_2362566
  have hstable : (prefixWord ++ tailWord_2362566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362566).length < 2 ^ (prefixWord ++ tailWord_2362566).sum := by decide
  have hdescent : baseEnd_2362566 < baseStart_2362566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362586 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_2362586 : Nat := 118140960795 + 2362586 * 2 ^ 59
def prefixEnd_2362586 : Nat := 4983230072969 + 3 ^ 40 * 2362586 * 2
def baseEnd_2362586 : Nat := 808761470388932403406447

theorem tailTrace_2362586 : CollatzResearch.WordTrace tailWord_2362586 prefixEnd_2362586 808761470388932403406447 := by
  unfold tailWord_2362586
  simp only [CollatzResearch.WordTrace]
  refine ⟨21542647654690473602456903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57447060412507929606551741 21542647654690473602456903)
  ·
    refine ⟨32313971482035710403685355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21542647654690473602456903 32313971482035710403685355)
    ·
      refine ⟨48470957223053565605528033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32313971482035710403685355 48470957223053565605528033)
      ·
        refine ⟨36353217917290174204146025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48470957223053565605528033 36353217917290174204146025)
        ·
          refine ⟨27264913437967630653109519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36353217917290174204146025 27264913437967630653109519)
          ·
            refine ⟨40897370156951445979664279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27264913437967630653109519 40897370156951445979664279)
            ·
              refine ⟨61346055235427168969496419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40897370156951445979664279 61346055235427168969496419)
              ·
                refine ⟨92019082853140753454244629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61346055235427168969496419 92019082853140753454244629)
                ·
                  refine ⟨4313394508740972818167717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 92019082853140753454244629 4313394508740972818167717)
                  ·
                    refine ⟨808761470388932403406447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4313394508740972818167717 808761470388932403406447)
                    ·
                      rfl

theorem cell22_2362586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_2362586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362586 prefixEnd_2362586 := by exact prefixLift 2362586
  have htrace : WordTrace (prefixWord ++ tailWord_2362586) baseStart_2362586 baseEnd_2362586 := by
    simpa [prefixWord, tailWord_2362586, baseEnd_2362586] using wordTrace_append hprefix tailTrace_2362586
  have hstable : (prefixWord ++ tailWord_2362586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362586).length < 2 ^ (prefixWord ++ tailWord_2362586).sum := by decide
  have hdescent : baseEnd_2362586 < baseStart_2362586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362603 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 2, 4]
def baseStart_2362603 : Nat := 118140960795 + 2362603 * 2 ^ 59
def prefixEnd_2362603 : Nat := 4983230072969 + 3 ^ 40 * 2362603 * 2
def baseEnd_2362603 : Nat := 808767289836350025731395

theorem tailTrace_2362603 : CollatzResearch.WordTrace tailWord_2362603 prefixEnd_2362603 808767289836350025731395 := by
  unfold tailWord_2362603
  simp only [CollatzResearch.WordTrace]
  refine ⟨86171210659700306313196463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57447473773133537542130975 86171210659700306313196463)
  ·
    refine ⟨129256815989550459469794695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86171210659700306313196463 129256815989550459469794695)
    ·
      refine ⟨193885223984325689204692043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129256815989550459469794695 193885223984325689204692043)
      ·
        refine ⟨290827835976488533807038065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193885223984325689204692043 290827835976488533807038065)
        ·
          refine ⟨218120876982366400355278549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290827835976488533807038065 218120876982366400355278549)
          ·
            refine ⟨5112208054274212508326841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 218120876982366400355278549 5112208054274212508326841)
            ·
              refine ⟨3834156040705659381245131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5112208054274212508326841 3834156040705659381245131)
              ·
                refine ⟨5751234061058489071867697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3834156040705659381245131 5751234061058489071867697)
                ·
                  refine ⟨4313425545793866803900773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5751234061058489071867697 4313425545793866803900773)
                  ·
                    refine ⟨808767289836350025731395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4313425545793866803900773 808767289836350025731395)
                    ·
                      rfl

theorem cell22_2362603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 4].length) (baseStart_2362603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362603 prefixEnd_2362603 := by exact prefixLift 2362603
  have htrace : WordTrace (prefixWord ++ tailWord_2362603) baseStart_2362603 baseEnd_2362603 := by
    simpa [prefixWord, tailWord_2362603, baseEnd_2362603] using wordTrace_append hprefix tailTrace_2362603
  have hstable : (prefixWord ++ tailWord_2362603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362603).length < 2 ^ (prefixWord ++ tailWord_2362603).sum := by decide
  have hdescent : baseEnd_2362603 < baseStart_2362603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362622 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2362622 : Nat := 118140960795 + 2362622 * 2 ^ 59
def prefixEnd_2362622 : Nat := 4983230072969 + 3 ^ 40 * 2362622 * 2
def baseEnd_2362622 : Nat := 808773793924640309506337

theorem tailTrace_2362622 : CollatzResearch.WordTrace tailWord_2362622 prefixEnd_2362622 808773793924640309506337 := by
  unfold tailWord_2362622
  simp only [CollatzResearch.WordTrace]
  refine ⟨10771487955828934069767265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57447935764420981705425413 10771487955828934069767265)
  ·
    refine ⟨8078615966871700552325449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10771487955828934069767265 8078615966871700552325449)
    ·
      refine ⟨6058961975153775414244087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8078615966871700552325449 6058961975153775414244087)
      ·
        refine ⟨9088442962730663121366131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6058961975153775414244087 9088442962730663121366131)
        ·
          refine ⟨13632664444095994682049197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9088442962730663121366131 13632664444095994682049197)
          ·
            refine ⟨5112249166535998005768449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13632664444095994682049197 5112249166535998005768449)
            ·
              refine ⟨3834186874901998504326337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5112249166535998005768449 3834186874901998504326337)
              ·
                refine ⟨2875640156176498878244753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3834186874901998504326337 2875640156176498878244753)
                ·
                  refine ⟨2156730117132374158683565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2875640156176498878244753 2156730117132374158683565)
                  ·
                    refine ⟨808773793924640309506337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156730117132374158683565 808773793924640309506337)
                    ·
                      rfl

theorem cell22_2362622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2362622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362622 prefixEnd_2362622 := by exact prefixLift 2362622
  have htrace : WordTrace (prefixWord ++ tailWord_2362622) baseStart_2362622 baseEnd_2362622 := by
    simpa [prefixWord, tailWord_2362622, baseEnd_2362622] using wordTrace_append hprefix tailTrace_2362622
  have hstable : (prefixWord ++ tailWord_2362622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362622).length < 2 ^ (prefixWord ++ tailWord_2362622).sum := by decide
  have hdescent : baseEnd_2362622 < baseStart_2362622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362633 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 3, 3]
def baseStart_2362633 : Nat := 118140960795 + 2362633 * 2 ^ 59
def prefixEnd_2362633 : Nat := 4983230072969 + 3 ^ 40 * 2362633 * 2
def baseEnd_2362633 : Nat := 808777559449439947481303

theorem tailTrace_2362633 : CollatzResearch.WordTrace tailWord_2362633 prefixEnd_2362633 808777559449439947481303 := by
  unfold tailWord_2362633
  simp only [CollatzResearch.WordTrace]
  refine ⟨86172304849591621436788553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57448203233061080957859035 86172304849591621436788553)
  ·
    refine ⟨64629228637193716077591415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86172304849591621436788553 64629228637193716077591415)
    ·
      refine ⟨96943842955790574116387123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64629228637193716077591415 96943842955790574116387123)
      ·
        refine ⟨145415764433685861174580685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96943842955790574116387123 145415764433685861174580685)
        ·
          refine ⟨54530911662632197940467757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145415764433685861174580685 54530911662632197940467757)
          ·
            refine ⟨20449091873487074227675409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54530911662632197940467757 20449091873487074227675409)
            ·
              refine ⟨15336818905115305670756557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20449091873487074227675409 15336818905115305670756557)
              ·
                refine ⟨5751307089418239626533709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15336818905115305670756557 5751307089418239626533709)
                ·
                  refine ⟨2156740158531839859950141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5751307089418239626533709 2156740158531839859950141)
                  ·
                    refine ⟨808777559449439947481303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156740158531839859950141 808777559449439947481303)
                    ·
                      rfl

theorem cell22_2362633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 3].length) (baseStart_2362633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362633 prefixEnd_2362633 := by exact prefixLift 2362633
  have htrace : WordTrace (prefixWord ++ tailWord_2362633) baseStart_2362633 baseEnd_2362633 := by
    simpa [prefixWord, tailWord_2362633, baseEnd_2362633] using wordTrace_append hprefix tailTrace_2362633
  have hstable : (prefixWord ++ tailWord_2362633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362633).length < 2 ^ (prefixWord ++ tailWord_2362633).sum := by decide
  have hdescent : baseEnd_2362633 < baseStart_2362633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362650 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 3, 3]
def baseStart_2362650 : Nat := 118140960795 + 2362650 * 2 ^ 59
def prefixEnd_2362650 : Nat := 4983230072969 + 3 ^ 40 * 2362650 * 2
def baseEnd_2362650 : Nat := 808783378896857569806251

theorem tailTrace_2362650 : CollatzResearch.WordTrace tailWord_2362650 prefixEnd_2362650 808783378896857569806251 := by
  unfold tailWord_2362650
  simp only [CollatzResearch.WordTrace]
  refine ⟨21543231222632508335039351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57448616593686688893438269 21543231222632508335039351)
  ·
    refine ⟨32314846833948762502559027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21543231222632508335039351 32314846833948762502559027)
    ·
      refine ⟨48472270250923143753838541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32314846833948762502559027 48472270250923143753838541)
      ·
        refine ⟨18177101344096178907689453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48472270250923143753838541 18177101344096178907689453)
        ·
          refine ⟨6816413004036067090383545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18177101344096178907689453 6816413004036067090383545)
          ·
            refine ⟨5112309753027050317787659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6816413004036067090383545 5112309753027050317787659)
            ·
              refine ⟨7668464629540575476681489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112309753027050317787659 7668464629540575476681489)
              ·
                refine ⟨5751348472155431607511117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7668464629540575476681489 5751348472155431607511117)
                ·
                  refine ⟨2156755677058286852816669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5751348472155431607511117 2156755677058286852816669)
                  ·
                    refine ⟨808783378896857569806251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156755677058286852816669 808783378896857569806251)
                    ·
                      rfl

theorem cell22_2362650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_2362650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362650 prefixEnd_2362650 := by exact prefixLift 2362650
  have htrace : WordTrace (prefixWord ++ tailWord_2362650) baseStart_2362650 baseEnd_2362650 := by
    simpa [prefixWord, tailWord_2362650, baseEnd_2362650] using wordTrace_append hprefix tailTrace_2362650
  have hstable : (prefixWord ++ tailWord_2362650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362650).length < 2 ^ (prefixWord ++ tailWord_2362650).sum := by decide
  have hdescent : baseEnd_2362650 < baseStart_2362650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362654 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2362654 : Nat := 118140960795 + 2362654 * 2 ^ 59
def prefixEnd_2362654 : Nat := 4983230072969 + 3 ^ 40 * 2362654 * 2
def baseEnd_2362654 : Nat := 808784748178602892706239

theorem tailTrace_2362654 : CollatzResearch.WordTrace tailWord_2362654 prefixEnd_2362654 808784748178602892706239 := by
  unfold tailWord_2362654
  simp only [CollatzResearch.WordTrace]
  refine ⟨10771633847814442752912877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57448713855010361348868677 10771633847814442752912877)
  ·
    refine ⟨4039362692930416032342329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10771633847814442752912877 4039362692930416032342329)
    ·
      refine ⟨3029522019697812024256747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4039362692930416032342329 3029522019697812024256747)
      ·
        refine ⟨4544283029546718036385121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3029522019697812024256747 4544283029546718036385121)
        ·
          refine ⟨3408212272160038527288841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4544283029546718036385121 3408212272160038527288841)
          ·
            refine ⟨2556159204120028895466631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408212272160038527288841 2556159204120028895466631)
            ·
              refine ⟨3834238806180043343199947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556159204120028895466631 3834238806180043343199947)
              ·
                refine ⟨5751358209270065014799921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3834238806180043343199947 5751358209270065014799921)
                ·
                  refine ⟨4313518656952548761099941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5751358209270065014799921 4313518656952548761099941)
                  ·
                    refine ⟨808784748178602892706239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4313518656952548761099941 808784748178602892706239)
                    ·
                      rfl

theorem cell22_2362654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2362654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362654 prefixEnd_2362654 := by exact prefixLift 2362654
  have htrace : WordTrace (prefixWord ++ tailWord_2362654) baseStart_2362654 baseEnd_2362654 := by
    simpa [prefixWord, tailWord_2362654, baseEnd_2362654] using wordTrace_append hprefix tailTrace_2362654
  have hstable : (prefixWord ++ tailWord_2362654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362654).length < 2 ^ (prefixWord ++ tailWord_2362654).sum := by decide
  have hdescent : baseEnd_2362654 < baseStart_2362654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362708 : List Nat := [2, 4, 1, 1, 2, 1, 1, 4, 6]
def baseStart_2362708 : Nat := 118140960795 + 2362708 * 2 ^ 59
def prefixEnd_2362708 : Nat := 4983230072969 + 3 ^ 40 * 2362708 * 2
def baseEnd_2362708 : Nat := 269601077827388250618691

theorem tailTrace_2362708 : CollatzResearch.WordTrace tailWord_2362708 prefixEnd_2362708 269601077827388250618691 := by
  unfold tailWord_2362708
  simp only [CollatzResearch.WordTrace]
  refine ⟨43087520162159954622884389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57450026882879939497179185 43087520162159954622884389)
  ·
    refine ⟨8078910030404991491790823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43087520162159954622884389 8078910030404991491790823)
    ·
      refine ⟨12118365045607487237686235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8078910030404991491790823 12118365045607487237686235)
      ·
        refine ⟨18177547568411230856529353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12118365045607487237686235 18177547568411230856529353)
        ·
          refine ⟨13633160676308423142397015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18177547568411230856529353 13633160676308423142397015)
          ·
            refine ⟨20449741014462634713595523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13633160676308423142397015 20449741014462634713595523)
            ·
              refine ⟨30674611521693952070393285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20449741014462634713595523 30674611521693952070393285)
              ·
                refine ⟨5751489660317616013198741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30674611521693952070393285 5751489660317616013198741)
                ·
                  refine ⟨269601077827388250618691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5751489660317616013198741 269601077827388250618691)
                  ·
                    rfl

theorem cell22_2362708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_2362708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362708 prefixEnd_2362708 := by exact prefixLift 2362708
  have htrace : WordTrace (prefixWord ++ tailWord_2362708) baseStart_2362708 baseEnd_2362708 := by
    simpa [prefixWord, tailWord_2362708, baseEnd_2362708] using wordTrace_append hprefix tailTrace_2362708
  have hstable : (prefixWord ++ tailWord_2362708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362708).length < 2 ^ (prefixWord ++ tailWord_2362708).sum := by decide
  have hdescent : baseEnd_2362708 < baseStart_2362708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362757 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 2, 3]
def baseStart_2362757 : Nat := 118140960795 + 2362757 * 2 ^ 59
def prefixEnd_2362757 : Nat := 4983230072969 + 3 ^ 40 * 2362757 * 2
def baseEnd_2362757 : Nat := 808820007183544957380923

theorem tailTrace_2362757 : CollatzResearch.WordTrace tailWord_2362757 prefixEnd_2362757 808820007183544957380923 := by
  unfold tailWord_2362757
  simp only [CollatzResearch.WordTrace]
  refine ⟨86176827501142390614302525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57451218334094927076201683 86176827501142390614302525)
  ·
    refine ⟨32316310312928396480363447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86176827501142390614302525 32316310312928396480363447)
    ·
      refine ⟨48474465469392594720545171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32316310312928396480363447 48474465469392594720545171)
      ·
        refine ⟨72711698204088892080817757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48474465469392594720545171 72711698204088892080817757)
        ·
          refine ⟨27266886826533334530306659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72711698204088892080817757 27266886826533334530306659)
          ·
            refine ⟨40900330239800001795459989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27266886826533334530306659 40900330239800001795459989)
            ·
              refine ⟨1917202979990625084162187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40900330239800001795459989 1917202979990625084162187)
              ·
                refine ⟨2875804469985937626243281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917202979990625084162187 2875804469985937626243281)
                ·
                  refine ⟨2156853352489453219682461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2875804469985937626243281 2156853352489453219682461)
                  ·
                    refine ⟨808820007183544957380923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156853352489453219682461 808820007183544957380923)
                    ·
                      rfl

theorem cell22_2362757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_2362757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362757 prefixEnd_2362757 := by exact prefixLift 2362757
  have htrace : WordTrace (prefixWord ++ tailWord_2362757) baseStart_2362757 baseEnd_2362757 := by
    simpa [prefixWord, tailWord_2362757, baseEnd_2362757] using wordTrace_append hprefix tailTrace_2362757
  have hstable : (prefixWord ++ tailWord_2362757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362757).length < 2 ^ (prefixWord ++ tailWord_2362757).sum := by decide
  have hdescent : baseEnd_2362757 < baseStart_2362757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362772 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2362772 : Nat := 118140960795 + 2362772 * 2 ^ 59
def prefixEnd_2362772 : Nat := 4983230072969 + 3 ^ 40 * 2362772 * 2
def baseEnd_2362772 : Nat := 808825141990089918255877

theorem tailTrace_2362772 : CollatzResearch.WordTrace tailWord_2362772 prefixEnd_2362772 808825141990089918255877 := by
  unfold tailWord_2362772
  simp only [CollatzResearch.WordTrace]
  refine ⟨43088687298044024088049285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57451583064058698784065713 43088687298044024088049285)
  ·
    refine ⟨8079128868383254516509241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43088687298044024088049285 8079128868383254516509241)
    ·
      refine ⟨6059346651287440887381931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8079128868383254516509241 6059346651287440887381931)
      ·
        refine ⟨9089019976931161331072897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6059346651287440887381931 9089019976931161331072897)
        ·
          refine ⟨6816764982698370998304673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9089019976931161331072897 6816764982698370998304673)
          ·
            refine ⟨5112573737023778248728505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6816764982698370998304673 5112573737023778248728505)
            ·
              refine ⟨3834430302767833686546379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5112573737023778248728505 3834430302767833686546379)
              ·
                refine ⟨5751645454151750529819569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3834430302767833686546379 5751645454151750529819569)
                ·
                  refine ⟨4313734090613812897364677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5751645454151750529819569 4313734090613812897364677)
                  ·
                    refine ⟨808825141990089918255877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4313734090613812897364677 808825141990089918255877)
                    ·
                      rfl

theorem cell22_2362772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2362772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362772 prefixEnd_2362772 := by exact prefixLift 2362772
  have htrace : WordTrace (prefixWord ++ tailWord_2362772) baseStart_2362772 baseEnd_2362772 := by
    simpa [prefixWord, tailWord_2362772, baseEnd_2362772] using wordTrace_append hprefix tailTrace_2362772
  have hstable : (prefixWord ++ tailWord_2362772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362772).length < 2 ^ (prefixWord ++ tailWord_2362772).sum := by decide
  have hdescent : baseEnd_2362772 < baseStart_2362772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362836 : List Nat := [2, 4, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_2362836 : Nat := 118140960795 + 2362836 * 2 ^ 59
def prefixEnd_2362836 : Nat := 4983230072969 + 3 ^ 40 * 2362836 * 2
def baseEnd_2362836 : Nat := 808847050498015084655681

theorem tailTrace_2362836 : CollatzResearch.WordTrace tailWord_2362836 prefixEnd_2362836 808847050498015084655681 := by
  unfold tailWord_2362836
  simp only [CollatzResearch.WordTrace]
  refine ⟨43089854433928093553214181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57453139245237458070952241 43089854433928093553214181)
  ·
    refine ⟨8079347706361517541227659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43089854433928093553214181 8079347706361517541227659)
    ·
      refine ⟨12119021559542276311841489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8079347706361517541227659 12119021559542276311841489)
      ·
        refine ⟨9089266169656707233881117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12119021559542276311841489 9089266169656707233881117)
        ·
          refine ⟨3408474813621265212705419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9089266169656707233881117 3408474813621265212705419)
          ·
            refine ⟨5112712220431897819058129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408474813621265212705419 5112712220431897819058129)
            ·
              refine ⟨3834534165323923364293597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5112712220431897819058129 3834534165323923364293597)
              ·
                refine ⟨1437950311996471261610099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3834534165323923364293597 1437950311996471261610099)
                ·
                  refine ⟨2156925467994706892415149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437950311996471261610099 2156925467994706892415149)
                  ·
                    refine ⟨808847050498015084655681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2156925467994706892415149 808847050498015084655681)
                    ·
                      rfl

theorem cell22_2362836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_2362836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362836 prefixEnd_2362836 := by exact prefixLift 2362836
  have htrace : WordTrace (prefixWord ++ tailWord_2362836) baseStart_2362836 baseEnd_2362836 := by
    simpa [prefixWord, tailWord_2362836, baseEnd_2362836] using wordTrace_append hprefix tailTrace_2362836
  have hstable : (prefixWord ++ tailWord_2362836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362836).length < 2 ^ (prefixWord ++ tailWord_2362836).sum := by decide
  have hdescent : baseEnd_2362836 < baseStart_2362836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362890 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_2362890 : Nat := 118140960795 + 2362890 * 2 ^ 59
def prefixEnd_2362890 : Nat := 4983230072969 + 3 ^ 40 * 2362890 * 2
def baseEnd_2362890 : Nat := 808865535801576943805515

theorem tailTrace_2362890 : CollatzResearch.WordTrace tailWord_2362890 prefixEnd_2362890 808865535801576943805515 := by
  unfold tailWord_2362890
  simp only [CollatzResearch.WordTrace]
  refine ⟨21545419602415138582223531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57454452273107036219262749 21545419602415138582223531)
  ·
    refine ⟨32318129403622707873335297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21545419602415138582223531 32318129403622707873335297)
    ·
      refine ⟨24238597052717030905001473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32318129403622707873335297 24238597052717030905001473)
      ·
        refine ⟨18178947789537773178751105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24238597052717030905001473 18178947789537773178751105)
        ·
          refine ⟨13634210842153329884063329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18178947789537773178751105 13634210842153329884063329)
          ·
            refine ⟨10225658131614997413047497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13634210842153329884063329 10225658131614997413047497)
            ·
              refine ⟨7669243598711248059785623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10225658131614997413047497 7669243598711248059785623)
              ·
                refine ⟨11503865398066872089678435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7669243598711248059785623 11503865398066872089678435)
                ·
                  refine ⟨17255798097100308134517653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11503865398066872089678435 17255798097100308134517653)
                  ·
                    refine ⟨808865535801576943805515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17255798097100308134517653 808865535801576943805515)
                    ·
                      rfl

theorem cell22_2362890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_2362890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362890 prefixEnd_2362890 := by exact prefixLift 2362890
  have htrace : WordTrace (prefixWord ++ tailWord_2362890) baseStart_2362890 baseEnd_2362890 := by
    simpa [prefixWord, tailWord_2362890, baseEnd_2362890] using wordTrace_append hprefix tailTrace_2362890
  have hstable : (prefixWord ++ tailWord_2362890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362890).length < 2 ^ (prefixWord ++ tailWord_2362890).sum := by decide
  have hdescent : baseEnd_2362890 < baseStart_2362890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362926 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_2362926 : Nat := 118140960795 + 2362926 * 2 ^ 59
def prefixEnd_2362926 : Nat := 4983230072969 + 3 ^ 40 * 2362926 * 2
def baseEnd_2362926 : Nat := 808877859337284849905405

theorem tailTrace_2362926 : CollatzResearch.WordTrace tailWord_2362926 prefixEnd_2362926 808877859337284849905405 := by
  unfold tailWord_2362926
  simp only [CollatzResearch.WordTrace]
  refine ⟨10772873929691266559650579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57455327625020088318136421 10772873929691266559650579)
  ·
    refine ⟨16159310894536899839475869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10772873929691266559650579 16159310894536899839475869)
    ·
      refine ⟨6059741585451337439803451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16159310894536899839475869 6059741585451337439803451)
      ·
        refine ⟨9089612378177006159705177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6059741585451337439803451 9089612378177006159705177)
        ·
          refine ⟨6817209283632754619778883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9089612378177006159705177 6817209283632754619778883)
          ·
            refine ⟨10225813925449131929668325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6817209283632754619778883 10225813925449131929668325)
            ·
              refine ⟨1917340111021712236812811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10225813925449131929668325 1917340111021712236812811)
              ·
                refine ⟨2876010166532568355219217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917340111021712236812811 2876010166532568355219217)
                ·
                  refine ⟨2157007624899426266414413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2876010166532568355219217 2157007624899426266414413)
                  ·
                    refine ⟨808877859337284849905405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157007624899426266414413 808877859337284849905405)
                    ·
                      rfl

theorem cell22_2362926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_2362926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362926 prefixEnd_2362926 := by exact prefixLift 2362926
  have htrace : WordTrace (prefixWord ++ tailWord_2362926) baseStart_2362926 baseEnd_2362926 := by
    simpa [prefixWord, tailWord_2362926, baseEnd_2362926] using wordTrace_append hprefix tailTrace_2362926
  have hstable : (prefixWord ++ tailWord_2362926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362926).length < 2 ^ (prefixWord ++ tailWord_2362926).sum := by decide
  have hdescent : baseEnd_2362926 < baseStart_2362926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362954 : List Nat := [3, 1, 2, 1, 1, 3, 2, 5, 1, 3]
def baseStart_2362954 : Nat := 118140960795 + 2362954 * 2 ^ 59
def prefixEnd_2362954 : Nat := 4983230072969 + 3 ^ 40 * 2362954 * 2
def baseEnd_2362954 : Nat := 808887444309502110205319

theorem tailTrace_2362954 : CollatzResearch.WordTrace tailWord_2362954 prefixEnd_2362954 808887444309502110205319 := by
  unfold tailWord_2362954
  simp only [CollatzResearch.WordTrace]
  refine ⟨21546003170357173314805979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57456008454285795506149277 21546003170357173314805979)
  ·
    refine ⟨32319004755535759972208969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21546003170357173314805979 32319004755535759972208969)
    ·
      refine ⟨24239253566651819979156727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32319004755535759972208969 24239253566651819979156727)
      ·
        refine ⟨36358880349977729968735091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24239253566651819979156727 36358880349977729968735091)
        ·
          refine ⟨54538320524966594953102637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36358880349977729968735091 54538320524966594953102637)
          ·
            refine ⟨20451870196862473107413489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54538320524966594953102637 20451870196862473107413489)
            ·
              refine ⟨15338902647646854830560117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20451870196862473107413489 15338902647646854830560117)
              ·
                refine ⟨1438022123216892640365011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15338902647646854830560117 1438022123216892640365011)
                ·
                  refine ⟨2157033184825338960547517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438022123216892640365011 2157033184825338960547517)
                  ·
                    refine ⟨808887444309502110205319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2157033184825338960547517 808887444309502110205319)
                    ·
                      rfl

theorem cell22_2362954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_2362954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362954 prefixEnd_2362954 := by exact prefixLift 2362954
  have htrace : WordTrace (prefixWord ++ tailWord_2362954) baseStart_2362954 baseEnd_2362954 := by
    simpa [prefixWord, tailWord_2362954, baseEnd_2362954] using wordTrace_append hprefix tailTrace_2362954
  have hstable : (prefixWord ++ tailWord_2362954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362954).length < 2 ^ (prefixWord ++ tailWord_2362954).sum := by decide
  have hdescent : baseEnd_2362954 < baseStart_2362954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362965 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_2362965 : Nat := 118140960795 + 2362965 * 2 ^ 59
def prefixEnd_2362965 : Nat := 4983230072969 + 3 ^ 40 * 2362965 * 2
def baseEnd_2362965 : Nat := 808891209834301748180285

theorem tailTrace_2362965 : CollatzResearch.WordTrace tailWord_2362965 prefixEnd_2362965 808891209834301748180285 := by
  unfold tailWord_2362965
  simp only [CollatzResearch.WordTrace]
  refine ⟨86184413884388842137874349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57456275922925894758582899 86184413884388842137874349)
  ·
    refine ⟨32319155206645815801702881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86184413884388842137874349 32319155206645815801702881)
    ·
      refine ⟨24239366404984361851277161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32319155206645815801702881 24239366404984361851277161)
      ·
        refine ⟨18179524803738271388457871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24239366404984361851277161 18179524803738271388457871)
        ·
          refine ⟨27269287205607407082686807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18179524803738271388457871 27269287205607407082686807)
          ·
            refine ⟨40903930808411110624030211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27269287205607407082686807 40903930808411110624030211)
            ·
              refine ⟨61355896212616665936045317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40903930808411110624030211 61355896212616665936045317)
              ·
                refine ⟨11504230539865624863008497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61355896212616665936045317 11504230539865624863008497)
                ·
                  refine ⟨8628172904899218647256373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11504230539865624863008497 8628172904899218647256373)
                  ·
                    refine ⟨808891209834301748180285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8628172904899218647256373 808891209834301748180285)
                    ·
                      rfl

theorem cell22_2362965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_2362965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362965 prefixEnd_2362965 := by exact prefixLift 2362965
  have htrace : WordTrace (prefixWord ++ tailWord_2362965) baseStart_2362965 baseEnd_2362965 := by
    simpa [prefixWord, tailWord_2362965, baseEnd_2362965] using wordTrace_append hprefix tailTrace_2362965
  have hstable : (prefixWord ++ tailWord_2362965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362965).length < 2 ^ (prefixWord ++ tailWord_2362965).sum := by decide
  have hdescent : baseEnd_2362965 < baseStart_2362965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362967 : List Nat := [1, 1, 3, 2, 2, 4, 2, 2, 5]
def baseStart_2362967 : Nat := 118140960795 + 2362967 * 2 ^ 59
def prefixEnd_2362967 : Nat := 4983230072969 + 3 ^ 40 * 2362967 * 2
def baseEnd_2362967 : Nat := 269630631491724803210093

theorem tailTrace_2362967 : CollatzResearch.WordTrace tailWord_2362967 prefixEnd_2362967 269630631491724803210093 := by
  unfold tailWord_2362967
  simp only [CollatzResearch.WordTrace]
  refine ⟨86184486830381596479447155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57456324553587730986298103 86184486830381596479447155)
  ·
    refine ⟨129276730245572394719170733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86184486830381596479447155 129276730245572394719170733)
    ·
      refine ⟨48478773842089648019689025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129276730245572394719170733 48478773842089648019689025)
      ·
        refine ⟨36359080381567236014766769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48478773842089648019689025 36359080381567236014766769)
        ·
          refine ⟨27269310286175427011075077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36359080381567236014766769 27269310286175427011075077)
          ·
            refine ⟨5112995678657892564576577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27269310286175427011075077 5112995678657892564576577)
            ·
              refine ⟨3834746758993419423432433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5112995678657892564576577 3834746758993419423432433)
              ·
                refine ⟨2876060069245064567574325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3834746758993419423432433 2876060069245064567574325)
                ·
                  refine ⟨269630631491724803210093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2876060069245064567574325 269630631491724803210093)
                  ·
                    rfl

theorem cell22_2362967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 2, 5].length) (baseStart_2362967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2362967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2362967 prefixEnd_2362967 := by exact prefixLift 2362967
  have htrace : WordTrace (prefixWord ++ tailWord_2362967) baseStart_2362967 baseEnd_2362967 := by
    simpa [prefixWord, tailWord_2362967, baseEnd_2362967] using wordTrace_append hprefix tailTrace_2362967
  have hstable : (prefixWord ++ tailWord_2362967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362967).length < 2 ^ (prefixWord ++ tailWord_2362967).sum := by decide
  have hdescent : baseEnd_2362967 < baseStart_2362967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
