import V185TrunkScan23Chunk0863

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5113218 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_5113218 : Nat := 118140960795 + 5113218 * 2 ^ 59
def prefixEnd_5113218 : Nat := 4983230072969 + 3 ^ 40 * 5113218 * 2
def baseEnd_5113218 : Nat := 2625538525221280744759745

theorem tailTrace_5113218 : CollatzResearch.WordTrace tailWord_5113218 prefixEnd_5113218 2625538525221280744759745 := by
  unfold tailWord_5113218
  simp only [CollatzResearch.WordTrace]
  refine ⟨46623595397422982238771077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124329587726461285970056205 46623595397422982238771077)
  ·
    refine ⟨8741924137016809169769577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46623595397422982238771077 8741924137016809169769577)
    ·
      refine ⟨6556443102762606877327183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8741924137016809169769577 6556443102762606877327183)
      ·
        refine ⟨9834664654143910315990775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6556443102762606877327183 9834664654143910315990775)
        ·
          refine ⟨14751996981215865473986163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9834664654143910315990775 14751996981215865473986163)
          ·
            refine ⟨22127995471823798210979245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14751996981215865473986163 22127995471823798210979245)
            ·
              refine ⟨8297998301933924329117217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22127995471823798210979245 8297998301933924329117217)
              ·
                refine ⟨6223498726450443246837913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8297998301933924329117217 6223498726450443246837913)
                ·
                  refine ⟨4667624044837832435128435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6223498726450443246837913 4667624044837832435128435)
                  ·
                    refine ⟨7001436067256748652692653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4667624044837832435128435 7001436067256748652692653)
                    ·
                      refine ⟨2625538525221280744759745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7001436067256748652692653 2625538525221280744759745)
                      ·
                        rfl

theorem cell23_5113218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_5113218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113218 prefixEnd_5113218 := by exact prefixLift 5113218
  have htrace : WordTrace (prefixWord ++ tailWord_5113218) baseStart_5113218 baseEnd_5113218 := by
    simpa [prefixWord, tailWord_5113218, baseEnd_5113218] using wordTrace_append hprefix tailTrace_5113218
  have hstable : (prefixWord ++ tailWord_5113218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113218).length < 2 ^ (prefixWord ++ tailWord_5113218).sum := by decide
  have hdescent : baseEnd_5113218 < baseStart_5113218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113260 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_5113260 : Nat := 118140960795 + 5113260 * 2 ^ 59
def prefixEnd_5113260 : Nat := 4983230072969 + 3 ^ 40 * 5113260 * 2
def baseEnd_5113260 : Nat := 875186697136256526811517

theorem tailTrace_5113260 : CollatzResearch.WordTrace tailWord_5113260 prefixEnd_5113260 875186697136256526811517 := by
  unfold tailWord_5113260
  simp only [CollatzResearch.WordTrace]
  refine ⟨93247956727769885064056617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124330608970359846752075489 93247956727769885064056617)
  ·
    refine ⟨69935967545827413798042463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93247956727769885064056617 69935967545827413798042463)
    ·
      refine ⟨104903951318741120697063695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69935967545827413798042463 104903951318741120697063695)
      ·
        refine ⟨157355926978111681045595543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104903951318741120697063695 157355926978111681045595543)
        ·
          refine ⟨236033890467167521568393315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157355926978111681045595543 236033890467167521568393315)
          ·
            refine ⟨354050835700751282352589973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236033890467167521568393315 354050835700751282352589973)
            ·
              refine ⟨16596132923472716360277655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 354050835700751282352589973 16596132923472716360277655)
              ·
                refine ⟨24894199385209074540416483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16596132923472716360277655 24894199385209074540416483)
                ·
                  refine ⟨37341299077813611810624725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24894199385209074540416483 37341299077813611810624725)
                  ·
                    refine ⟨875186697136256526811517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37341299077813611810624725 875186697136256526811517)
                    ·
                      rfl

theorem cell23_5113260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_5113260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113260 prefixEnd_5113260 := by exact prefixLift 5113260
  have htrace : WordTrace (prefixWord ++ tailWord_5113260) baseStart_5113260 baseEnd_5113260 := by
    simpa [prefixWord, tailWord_5113260, baseEnd_5113260] using wordTrace_append hprefix tailTrace_5113260
  have hstable : (prefixWord ++ tailWord_5113260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113260).length < 2 ^ (prefixWord ++ tailWord_5113260).sum := by decide
  have hdescent : baseEnd_5113260 < baseStart_5113260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113277 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_5113277 : Nat := 118140960795 + 5113277 * 2 ^ 59
def prefixEnd_5113277 : Nat := 4983230072969 + 3 ^ 40 * 5113277 * 2
def baseEnd_5113277 : Nat := 875189606859965337973991

theorem tailTrace_5113277 : CollatzResearch.WordTrace tailWord_5113277 prefixEnd_5113277 875189606859965337973991 := by
  unfold tailWord_5113277
  simp only [CollatzResearch.WordTrace]
  refine ⟨186496533496478182031482085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124331022330985454687654723 186496533496478182031482085)
  ·
    refine ⟨34968100030589659130902891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186496533496478182031482085 34968100030589659130902891)
    ·
      refine ⟨52452150045884488696354337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34968100030589659130902891 52452150045884488696354337)
      ·
        refine ⟨39339112534413366522265753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52452150045884488696354337 39339112534413366522265753)
        ·
          refine ⟨29504334400810024891699315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39339112534413366522265753 29504334400810024891699315)
          ·
            refine ⟨44256501601215037337548973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29504334400810024891699315 44256501601215037337548973)
            ·
              refine ⟨16596188100455639001580865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44256501601215037337548973 16596188100455639001580865)
              ·
                refine ⟨12447141075341729251185649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16596188100455639001580865 12447141075341729251185649)
                ·
                  refine ⟨9335355806506296938389237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12447141075341729251185649 9335355806506296938389237)
                  ·
                    refine ⟨875189606859965337973991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9335355806506296938389237 875189606859965337973991)
                    ·
                      rfl

theorem cell23_5113277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_5113277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113277 prefixEnd_5113277 := by exact prefixLift 5113277
  have htrace : WordTrace (prefixWord ++ tailWord_5113277) baseStart_5113277 baseEnd_5113277 := by
    simpa [prefixWord, tailWord_5113277, baseEnd_5113277] using wordTrace_append hprefix tailTrace_5113277
  have hstable : (prefixWord ++ tailWord_5113277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113277).length < 2 ^ (prefixWord ++ tailWord_5113277).sum := by decide
  have hdescent : baseEnd_5113277 < baseStart_5113277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113341 : List Nat := [1, 4, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_5113341 : Nat := 118140960795 + 5113341 * 2 ^ 59
def prefixEnd_5113341 : Nat := 4983230072969 + 3 ^ 40 * 5113341 * 2
def baseEnd_5113341 : Nat := 875200561113927921173893

theorem tailTrace_5113341 : CollatzResearch.WordTrace tailWord_5113341 prefixEnd_5113341 875200561113927921173893 := by
  unfold tailWord_5113341
  simp only [CollatzResearch.WordTrace]
  refine ⟨186498867768246320961811877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124332578512164213974541251 186498867768246320961811877)
  ·
    refine ⟨34968537706546185180339727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186498867768246320961811877 34968537706546185180339727)
    ·
      refine ⟨52452806559819277770509591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34968537706546185180339727 52452806559819277770509591)
      ·
        refine ⟨78679209839728916655764387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52452806559819277770509591 78679209839728916655764387)
        ·
          refine ⟨118018814759593374983646581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78679209839728916655764387 118018814759593374983646581)
          ·
            refine ⟨11064263883711878904716867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118018814759593374983646581 11064263883711878904716867)
            ·
              refine ⟨16596395825567818357075301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11064263883711878904716867 16596395825567818357075301)
              ·
                refine ⟨3111824217293965941951619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16596395825567818357075301 3111824217293965941951619)
                ·
                  refine ⟨4667736325940948912927429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3111824217293965941951619 4667736325940948912927429)
                  ·
                    refine ⟨875200561113927921173893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4667736325940948912927429 875200561113927921173893)
                    ·
                      rfl

theorem cell23_5113341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_5113341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113341 prefixEnd_5113341 := by exact prefixLift 5113341
  have htrace : WordTrace (prefixWord ++ tailWord_5113341) baseStart_5113341 baseEnd_5113341 := by
    simpa [prefixWord, tailWord_5113341, baseEnd_5113341] using wordTrace_append hprefix tailTrace_5113341
  have hstable : (prefixWord ++ tailWord_5113341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113341).length < 2 ^ (prefixWord ++ tailWord_5113341).sum := by decide
  have hdescent : baseEnd_5113341 < baseStart_5113341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113368 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 2, 2, 3]
def baseStart_5113368 : Nat := 118140960795 + 5113368 * 2 ^ 59
def prefixEnd_5113368 : Nat := 4983230072969 + 3 ^ 40 * 5113368 * 2
def baseEnd_5113368 : Nat := 2625615547319455157884055

theorem tailTrace_5113368 : CollatzResearch.WordTrace tailWord_5113368 prefixEnd_5113368 2625615547319455157884055 := by
  unfold tailWord_5113368
  simp only [CollatzResearch.WordTrace]
  refine ⟨93249926269574252286522379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124333235026099003048696505 93249926269574252286522379)
  ·
    refine ⟨139874889404361378429783569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93249926269574252286522379 139874889404361378429783569)
    ·
      refine ⟨104906167053271033822337677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139874889404361378429783569 104906167053271033822337677)
      ·
        refine ⟨39339812644976637683376629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104906167053271033822337677 39339812644976637683376629)
        ·
          refine ⟨3688107435466559782816559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39339812644976637683376629 3688107435466559782816559)
          ·
            refine ⟨5532161153199839674224839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688107435466559782816559 5532161153199839674224839)
            ·
              refine ⟨8298241729799759511337259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5532161153199839674224839 8298241729799759511337259)
              ·
                refine ⟨12447362594699639267005889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8298241729799759511337259 12447362594699639267005889)
                ·
                  refine ⟨9335521946024729450254417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12447362594699639267005889 9335521946024729450254417)
                  ·
                    refine ⟨7001641459518547087690813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9335521946024729450254417 7001641459518547087690813)
                    ·
                      refine ⟨2625615547319455157884055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7001641459518547087690813 2625615547319455157884055)
                      ·
                        rfl

theorem cell23_5113368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_5113368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113368 prefixEnd_5113368 := by exact prefixLift 5113368
  have htrace : WordTrace (prefixWord ++ tailWord_5113368) baseStart_5113368 baseEnd_5113368 := by
    simpa [prefixWord, tailWord_5113368, baseEnd_5113368] using wordTrace_append hprefix tailTrace_5113368
  have hstable : (prefixWord ++ tailWord_5113368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113368).length < 2 ^ (prefixWord ++ tailWord_5113368).sum := by decide
  have hdescent : baseEnd_5113368 < baseStart_5113368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113407 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 5]
def baseStart_5113407 : Nat := 118140960795 + 5113407 * 2 ^ 59
def prefixEnd_5113407 : Nat := 4983230072969 + 3 ^ 40 * 5113407 * 2
def baseEnd_5113407 : Nat := 2625635573064980505296375

theorem tailTrace_5113407 : CollatzResearch.WordTrace tailWord_5113407 prefixEnd_5113407 2625635573064980505296375 := by
  unfold tailWord_5113407
  simp only [CollatzResearch.WordTrace]
  refine ⟨186501274986007214233714475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124334183324004809489142983 186501274986007214233714475)
  ·
    refine ⟨279751912479010821350571713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186501274986007214233714475 279751912479010821350571713)
    ·
      refine ⟨209813934359258116012928785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279751912479010821350571713 209813934359258116012928785)
      ·
        refine ⟨157360450769443587009696589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209813934359258116012928785 157360450769443587009696589)
        ·
          refine ⟨59010169038541345128636221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157360450769443587009696589 59010169038541345128636221)
          ·
            refine ⟨22128813389453004423238583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59010169038541345128636221 22128813389453004423238583)
            ·
              refine ⟨33193220084179506634857875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22128813389453004423238583 33193220084179506634857875)
              ·
                refine ⟨49789830126269259952286813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33193220084179506634857875 49789830126269259952286813)
                ·
                  refine ⟨18671186297350972482107555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49789830126269259952286813 18671186297350972482107555)
                  ·
                    refine ⟨28006779446026458723161333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18671186297350972482107555 28006779446026458723161333)
                    ·
                      refine ⟨2625635573064980505296375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28006779446026458723161333 2625635573064980505296375)
                      ·
                        rfl

theorem cell23_5113407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_5113407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113407 prefixEnd_5113407 := by exact prefixLift 5113407
  have htrace : WordTrace (prefixWord ++ tailWord_5113407) baseStart_5113407 baseEnd_5113407 := by
    simpa [prefixWord, tailWord_5113407, baseEnd_5113407] using wordTrace_append hprefix tailTrace_5113407
  have hstable : (prefixWord ++ tailWord_5113407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113407).length < 2 ^ (prefixWord ++ tailWord_5113407).sum := by decide
  have hdescent : baseEnd_5113407 < baseStart_5113407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113497 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_5113497 : Nat := 118140960795 + 5113497 * 2 ^ 59
def prefixEnd_5113497 : Nat := 4983230072969 + 3 ^ 40 * 5113497 * 2
def baseEnd_5113497 : Nat := 2625681786323885153170961

theorem tailTrace_5113497 : CollatzResearch.WordTrace tailWord_5113497 prefixEnd_5113497 2625681786323885153170961 := by
  unfold tailWord_5113497
  simp only [CollatzResearch.WordTrace]
  refine ⟨186504557555681159604490745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124336371703787439736327163 186504557555681159604490745)
  ·
    refine ⟨139878418166760869703368059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186504557555681159604490745 139878418166760869703368059)
    ·
      refine ⟨209817627250141304555052089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139878418166760869703368059 209817627250141304555052089)
      ·
        refine ⟨157363220437605978416289067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209817627250141304555052089 157363220437605978416289067)
        ·
          refine ⟨236044830656408967624433601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157363220437605978416289067 236044830656408967624433601)
          ·
            refine ⟨177033622992306725718325201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236044830656408967624433601 177033622992306725718325201)
            ·
              refine ⟨132775217244230044288743901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177033622992306725718325201 132775217244230044288743901)
              ·
                refine ⟨49790706466586266608278963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132775217244230044288743901 49790706466586266608278963)
                ·
                  refine ⟨74686059699879399912418445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49790706466586266608278963 74686059699879399912418445)
                  ·
                    refine ⟨28007272387454774967156917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74686059699879399912418445 28007272387454774967156917)
                    ·
                      refine ⟨2625681786323885153170961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28007272387454774967156917 2625681786323885153170961)
                      ·
                        rfl

theorem cell23_5113497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_5113497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113497 prefixEnd_5113497 := by exact prefixLift 5113497
  have htrace : WordTrace (prefixWord ++ tailWord_5113497) baseStart_5113497 baseEnd_5113497 := by
    simpa [prefixWord, tailWord_5113497, baseEnd_5113497] using wordTrace_append hprefix tailTrace_5113497
  have hstable : (prefixWord ++ tailWord_5113497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113497).length < 2 ^ (prefixWord ++ tailWord_5113497).sum := by decide
  have hdescent : baseEnd_5113497 < baseStart_5113497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113506 : List Nat := [3, 3, 1, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_5113506 : Nat := 118140960795 + 5113506 * 2 ^ 59
def prefixEnd_5113506 : Nat := 4983230072969 + 3 ^ 40 * 5113506 * 2
def baseEnd_5113506 : Nat := 2625686407649775617958421

theorem tailTrace_5113506 : CollatzResearch.WordTrace tailWord_5113506 prefixEnd_5113506 2625686407649775617958421 := by
  unfold tailWord_5113506
  simp only [CollatzResearch.WordTrace]
  refine ⟨46626221453162138535392093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124336590541765702761045581 46626221453162138535392093)
  ·
    refine ⟨17484833044935801950772035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46626221453162138535392093 17484833044935801950772035)
    ·
      refine ⟨26227249567403702926158053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17484833044935801950772035 26227249567403702926158053)
      ·
        refine ⟨4917609293888194298654635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26227249567403702926158053 4917609293888194298654635)
        ·
          refine ⟨7376413940832291447981953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4917609293888194298654635 7376413940832291447981953)
          ·
            refine ⟨5532310455624218585986465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7376413940832291447981953 5532310455624218585986465)
            ·
              refine ⟨4149232841718163939489849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5532310455624218585986465 4149232841718163939489849)
              ·
                refine ⟨3111924631288622954617387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4149232841718163939489849 3111924631288622954617387)
                ·
                  refine ⟨4667886946932934431926081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3111924631288622954617387 4667886946932934431926081)
                  ·
                    refine ⟨3500915210199700823944561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4667886946932934431926081 3500915210199700823944561)
                    ·
                      refine ⟨2625686407649775617958421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500915210199700823944561 2625686407649775617958421)
                      ·
                        rfl

theorem cell23_5113506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_5113506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113506 prefixEnd_5113506 := by exact prefixLift 5113506
  have htrace : WordTrace (prefixWord ++ tailWord_5113506) baseStart_5113506 baseEnd_5113506 := by
    simpa [prefixWord, tailWord_5113506, baseEnd_5113506] using wordTrace_append hprefix tailTrace_5113506
  have hstable : (prefixWord ++ tailWord_5113506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113506).length < 2 ^ (prefixWord ++ tailWord_5113506).sum := by decide
  have hdescent : baseEnd_5113506 < baseStart_5113506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113534 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_5113534 : Nat := 118140960795 + 5113534 * 2 ^ 59
def prefixEnd_5113534 : Nat := 4983230072969 + 3 ^ 40 * 5113534 * 2
def baseEnd_5113534 : Nat := 291744531678677945378699

theorem tailTrace_5113534 : CollatzResearch.WordTrace tailWord_5113534 prefixEnd_5113534 291744531678677945378699 := by
  unfold tailWord_5113534
  simp only [CollatzResearch.WordTrace]
  refine ⟨23313238382068389365448457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124337271371031409949058437 23313238382068389365448457)
  ·
    refine ⟨17484928786551292024086343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23313238382068389365448457 17484928786551292024086343)
    ·
      refine ⟨26227393179826938036129515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17484928786551292024086343 26227393179826938036129515)
      ·
        refine ⟨39341089769740407054194273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26227393179826938036129515 39341089769740407054194273)
        ·
          refine ⟨29505817327305305290645705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39341089769740407054194273 29505817327305305290645705)
          ·
            refine ⟨22129362995478978967984279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29505817327305305290645705 22129362995478978967984279)
            ·
              refine ⟨33194044493218468451976419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22129362995478978967984279 33194044493218468451976419)
              ·
                refine ⟨49791066739827702677964629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33194044493218468451976419 49791066739827702677964629)
                ·
                  refine ⟨291744531678677945378699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49791066739827702677964629 291744531678677945378699)
                  ·
                    rfl

theorem cell23_5113534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_5113534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113534 prefixEnd_5113534 := by exact prefixLift 5113534
  have htrace : WordTrace (prefixWord ++ tailWord_5113534) baseStart_5113534 baseEnd_5113534 := by
    simpa [prefixWord, tailWord_5113534, baseEnd_5113534] using wordTrace_append hprefix tailTrace_5113534
  have hstable : (prefixWord ++ tailWord_5113534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113534).length < 2 ^ (prefixWord ++ tailWord_5113534).sum := by decide
  have hdescent : baseEnd_5113534 < baseStart_5113534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113544 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_5113544 : Nat := 118140960795 + 5113544 * 2 ^ 59
def prefixEnd_5113544 : Nat := 4983230072969 + 3 ^ 40 * 5113544 * 2
def baseEnd_5113544 : Nat := 2625705919914646469283245

theorem tailTrace_5113544 : CollatzResearch.WordTrace tailWord_5113544 prefixEnd_5113544 2625705919914646469283245 := by
  unfold tailWord_5113544
  simp only [CollatzResearch.WordTrace]
  refine ⟨93253135893255443315725843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124337514524340591087634457 93253135893255443315725843)
  ·
    refine ⟨139879703839883164973588765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93253135893255443315725843 139879703839883164973588765)
    ·
      refine ⟨52454888939956186865095787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139879703839883164973588765 52454888939956186865095787)
      ·
        refine ⟨78682333409934280297643681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52454888939956186865095787 78682333409934280297643681)
        ·
          refine ⟨59011750057450710223232761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78682333409934280297643681 59011750057450710223232761)
          ·
            refine ⟨44258812543088032667424571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59011750057450710223232761 44258812543088032667424571)
            ·
              refine ⟨66388218814632049001136857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44258812543088032667424571 66388218814632049001136857)
              ·
                refine ⟨49791164110974036750852643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66388218814632049001136857 49791164110974036750852643)
                ·
                  refine ⟨74686746166461055126278965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49791164110974036750852643 74686746166461055126278965)
                  ·
                    refine ⟨7001882453105723918088653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74686746166461055126278965 7001882453105723918088653)
                    ·
                      refine ⟨2625705919914646469283245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7001882453105723918088653 2625705919914646469283245)
                      ·
                        rfl

theorem cell23_5113544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_5113544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113544 prefixEnd_5113544 := by exact prefixLift 5113544
  have htrace : WordTrace (prefixWord ++ tailWord_5113544) baseStart_5113544 baseEnd_5113544 := by
    simpa [prefixWord, tailWord_5113544, baseEnd_5113544] using wordTrace_append hprefix tailTrace_5113544
  have hstable : (prefixWord ++ tailWord_5113544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113544).length < 2 ^ (prefixWord ++ tailWord_5113544).sum := by decide
  have hdescent : baseEnd_5113544 < baseStart_5113544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113549 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_5113549 : Nat := 118140960795 + 5113549 * 2 ^ 59
def prefixEnd_5113549 : Nat := 4983230072969 + 3 ^ 40 * 5113549 * 2
def baseEnd_5113549 : Nat := 2625708487317918949720723

theorem tailTrace_5113549 : CollatzResearch.WordTrace tailWord_5113549 prefixEnd_5113549 2625708487317918949720723 := by
  unfold tailWord_5113549
  simp only [CollatzResearch.WordTrace]
  refine ⟨186506454151492772485383701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124337636100995181656922467 186506454151492772485383701)
  ·
    refine ⟨8742490038351223710252361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 186506454151492772485383701 8742490038351223710252361)
    ·
      refine ⟨6556867528763417782689271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8742490038351223710252361 6556867528763417782689271)
      ·
        refine ⟨9835301293145126674033907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6556867528763417782689271 9835301293145126674033907)
        ·
          refine ⟨14752951939717690011050861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9835301293145126674033907 14752951939717690011050861)
          ·
            refine ⟨5532356977394133754144073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14752951939717690011050861 5532356977394133754144073)
            ·
              refine ⟨4149267733045600315608055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5532356977394133754144073 4149267733045600315608055)
              ·
                refine ⟨6223901599568400473412083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149267733045600315608055 6223901599568400473412083)
                ·
                  refine ⟨9335852399352600710118125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6223901599568400473412083 9335852399352600710118125)
                  ·
                    refine ⟨3500944649757225266294297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9335852399352600710118125 3500944649757225266294297)
                    ·
                      refine ⟨2625708487317918949720723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500944649757225266294297 2625708487317918949720723)
                      ·
                        rfl

theorem cell23_5113549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_5113549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113549 prefixEnd_5113549 := by exact prefixLift 5113549
  have htrace : WordTrace (prefixWord ++ tailWord_5113549) baseStart_5113549 baseEnd_5113549 := by
    simpa [prefixWord, tailWord_5113549, baseEnd_5113549] using wordTrace_append hprefix tailTrace_5113549
  have hstable : (prefixWord ++ tailWord_5113549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113549).length < 2 ^ (prefixWord ++ tailWord_5113549).sum := by decide
  have hdescent : baseEnd_5113549 < baseStart_5113549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113584 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 4]
def baseStart_5113584 : Nat := 118140960795 + 5113584 * 2 ^ 59
def prefixEnd_5113584 : Nat := 4983230072969 + 3 ^ 40 * 5113584 * 2
def baseEnd_5113584 : Nat := 2625726459140826312783061

theorem tailTrace_5113584 : CollatzResearch.WordTrace tailWord_5113584 prefixEnd_5113584 2625726459140826312783061 := by
  unfold tailWord_5113584
  simp only [CollatzResearch.WordTrace]
  refine ⟨93253865353182986731453903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124338487137577315641938537 93253865353182986731453903)
  ·
    refine ⟨139880798029774480097180855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93253865353182986731453903 139880798029774480097180855)
    ·
      refine ⟨209821197044661720145771283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139880798029774480097180855 209821197044661720145771283)
      ·
        refine ⟨314731795566992580218656925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209821197044661720145771283 314731795566992580218656925)
        ·
          refine ⟨118024423337622217581996347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314731795566992580218656925 118024423337622217581996347)
          ·
            refine ⟨177036635006433326372994521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118024423337622217581996347 177036635006433326372994521)
            ·
              refine ⟨132777476254824994779745891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177036635006433326372994521 132777476254824994779745891)
              ·
                refine ⟨199166214382237492169618837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132777476254824994779745891 199166214382237492169618837)
                ·
                  refine ⟨9335916299167382445450883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 199166214382237492169618837 9335916299167382445450883)
                  ·
                    refine ⟨14003874448751073668176325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9335916299167382445450883 14003874448751073668176325)
                    ·
                      refine ⟨2625726459140826312783061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14003874448751073668176325 2625726459140826312783061)
                      ·
                        rfl

theorem cell23_5113584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_5113584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113584 prefixEnd_5113584 := by exact prefixLift 5113584
  have htrace : WordTrace (prefixWord ++ tailWord_5113584) baseStart_5113584 baseEnd_5113584 := by
    simpa [prefixWord, tailWord_5113584, baseEnd_5113584] using wordTrace_append hprefix tailTrace_5113584
  have hstable : (prefixWord ++ tailWord_5113584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113584).length < 2 ^ (prefixWord ++ tailWord_5113584).sum := by decide
  have hdescent : baseEnd_5113584 < baseStart_5113584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113601 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_5113601 : Nat := 118140960795 + 5113601 * 2 ^ 59
def prefixEnd_5113601 : Nat := 4983230072969 + 3 ^ 40 * 5113601 * 2
def baseEnd_5113601 : Nat := 2625735188311952746270483

theorem tailTrace_5113601 : CollatzResearch.WordTrace tailWord_5113601 prefixEnd_5113601 2625735188311952746270483 := by
  unfold tailWord_5113601
  simp only [CollatzResearch.WordTrace]
  refine ⟨186508350747304385366276657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124338900498202923577517771 186508350747304385366276657)
  ·
    refine ⟨139881263060478289024707493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186508350747304385366276657 139881263060478289024707493)
    ·
      refine ⟨26227736823839679192132655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139881263060478289024707493 26227736823839679192132655)
      ·
        refine ⟨39341605235759518788198983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26227736823839679192132655 39341605235759518788198983)
        ·
          refine ⟨59012407853639278182298475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39341605235759518788198983 59012407853639278182298475)
          ·
            refine ⟨88518611780458917273447713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59012407853639278182298475 88518611780458917273447713)
            ·
              refine ⟨66388958835344187955085785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88518611780458917273447713 66388958835344187955085785)
              ·
                refine ⟨49791719126508140966314339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66388958835344187955085785 49791719126508140966314339)
                ·
                  refine ⟨74687578689762211449471509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49791719126508140966314339 74687578689762211449471509)
                  ·
                    refine ⟨3500980251082603661693977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74687578689762211449471509 3500980251082603661693977)
                    ·
                      refine ⟨2625735188311952746270483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3500980251082603661693977 2625735188311952746270483)
                      ·
                        rfl

theorem cell23_5113601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_5113601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113601 prefixEnd_5113601 := by exact prefixLift 5113601
  have htrace : WordTrace (prefixWord ++ tailWord_5113601) baseStart_5113601 baseEnd_5113601 := by
    simpa [prefixWord, tailWord_5113601, baseEnd_5113601] using wordTrace_append hprefix tailTrace_5113601
  have hstable : (prefixWord ++ tailWord_5113601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113601).length < 2 ^ (prefixWord ++ tailWord_5113601).sum := by decide
  have hdescent : baseEnd_5113601 < baseStart_5113601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113614 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_5113614 : Nat := 118140960795 + 5113614 * 2 ^ 59
def prefixEnd_5113614 : Nat := 4983230072969 + 3 ^ 40 * 5113614 * 2
def baseEnd_5113614 : Nat := 2625741863560461195407923

theorem tailTrace_5113614 : CollatzResearch.WordTrace tailWord_5113614 prefixEnd_5113614 2625741863560461195407923 := by
  unfold tailWord_5113614
  simp only [CollatzResearch.WordTrace]
  refine ⟨23313603112032161073312487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124339216597504859057666597 23313603112032161073312487)
  ·
    refine ⟨34970404668048241609968731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23313603112032161073312487 34970404668048241609968731)
    ·
      refine ⟨52455607002072362414953097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34970404668048241609968731 52455607002072362414953097)
      ·
        refine ⟨39341705251554271811214823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52455607002072362414953097 39341705251554271811214823)
        ·
          refine ⟨59012557877331407716822235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39341705251554271811214823 59012557877331407716822235)
          ·
            refine ⟨88518836815997111575233353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59012557877331407716822235 88518836815997111575233353)
            ·
              refine ⟨66389127611997833681425015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88518836815997111575233353 66389127611997833681425015)
              ·
                refine ⟨99583691417996750522137523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66389127611997833681425015 99583691417996750522137523)
                ·
                  refine ⟨149375537126995125783206285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99583691417996750522137523 149375537126995125783206285)
                  ·
                    refine ⟨56015826422623172168702357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149375537126995125783206285 56015826422623172168702357)
                    ·
                      refine ⟨2625741863560461195407923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56015826422623172168702357 2625741863560461195407923)
                      ·
                        rfl

theorem cell23_5113614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_5113614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113614 prefixEnd_5113614 := by exact prefixLift 5113614
  have htrace : WordTrace (prefixWord ++ tailWord_5113614) baseStart_5113614 baseEnd_5113614 := by
    simpa [prefixWord, tailWord_5113614, baseEnd_5113614] using wordTrace_append hprefix tailTrace_5113614
  have hstable : (prefixWord ++ tailWord_5113614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113614).length < 2 ^ (prefixWord ++ tailWord_5113614).sum := by decide
  have hdescent : baseEnd_5113614 < baseStart_5113614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113618 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5113618 : Nat := 118140960795 + 5113618 * 2 ^ 59
def prefixEnd_5113618 : Nat := 4983230072969 + 3 ^ 40 * 5113618 * 2
def baseEnd_5113618 : Nat := 2625743917483079179757905

theorem tailTrace_5113618 : CollatzResearch.WordTrace tailWord_5113618 prefixEnd_5113618 2625743917483079179757905 := by
  unfold tailWord_5113618
  simp only [CollatzResearch.WordTrace]
  refine ⟨46627242697060699317411377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124339313858828531513097005 46627242697060699317411377)
  ·
    refine ⟨34970432022795524488058533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46627242697060699317411377 34970432022795524488058533)
    ·
      refine ⟨6556956004274160841510975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34970432022795524488058533 6556956004274160841510975)
      ·
        refine ⟨9835434006411241262266463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6556956004274160841510975 9835434006411241262266463)
        ·
          refine ⟨14753151009616861893399695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9835434006411241262266463 14753151009616861893399695)
          ·
            refine ⟨22129726514425292840099543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14753151009616861893399695 22129726514425292840099543)
            ·
              refine ⟨33194589771637939260149315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22129726514425292840099543 33194589771637939260149315)
              ·
                refine ⟨49791884657456908890223973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33194589771637939260149315 49791884657456908890223973)
                ·
                  refine ⟨9335978373273170416916995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49791884657456908890223973 9335978373273170416916995)
                  ·
                    refine ⟨14003967559909755625375493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9335978373273170416916995 14003967559909755625375493)
                    ·
                      refine ⟨2625743917483079179757905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14003967559909755625375493 2625743917483079179757905)
                      ·
                        rfl

theorem cell23_5113618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5113618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113618 prefixEnd_5113618 := by exact prefixLift 5113618
  have htrace : WordTrace (prefixWord ++ tailWord_5113618) baseStart_5113618 baseEnd_5113618 := by
    simpa [prefixWord, tailWord_5113618, baseEnd_5113618] using wordTrace_append hprefix tailTrace_5113618
  have hstable : (prefixWord ++ tailWord_5113618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113618).length < 2 ^ (prefixWord ++ tailWord_5113618).sum := by decide
  have hdescent : baseEnd_5113618 < baseStart_5113618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113621 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_5113621 : Nat := 118140960795 + 5113621 * 2 ^ 59
def prefixEnd_5113621 : Nat := 4983230072969 + 3 ^ 40 * 5113621 * 2
def baseEnd_5113621 : Nat := 2625745457925042668020391

theorem tailTrace_5113621 : CollatzResearch.WordTrace tailWord_5113621 prefixEnd_5113621 2625745457925042668020391 := by
  unfold tailWord_5113621
  simp only [CollatzResearch.WordTrace]
  refine ⟨186509080207231928782004717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124339386804821285854669811 186509080207231928782004717)
  ·
    refine ⟨69940905077711973293251769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186509080207231928782004717 69940905077711973293251769)
    ·
      refine ⟨52455678808283979969938827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69940905077711973293251769 52455678808283979969938827)
      ·
        refine ⟨78683518212425969954908241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52455678808283979969938827 78683518212425969954908241)
        ·
          refine ⟨59012638659319477466181181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78683518212425969954908241 59012638659319477466181181)
          ·
            refine ⟨22129739497244804049817943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59012638659319477466181181 22129739497244804049817943)
            ·
              refine ⟨33194609245867206074726915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22129739497244804049817943 33194609245867206074726915)
              ·
                refine ⟨49791913868800809112090373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33194609245867206074726915 49791913868800809112090373)
                ·
                  refine ⟨9335983850400151708516945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49791913868800809112090373 9335983850400151708516945)
                  ·
                    refine ⟨7001987887800113781387709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9335983850400151708516945 7001987887800113781387709)
                    ·
                      refine ⟨2625745457925042668020391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7001987887800113781387709 2625745457925042668020391)
                      ·
                        rfl

theorem cell23_5113621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_5113621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113621 prefixEnd_5113621 := by exact prefixLift 5113621
  have htrace : WordTrace (prefixWord ++ tailWord_5113621) baseStart_5113621 baseEnd_5113621 := by
    simpa [prefixWord, tailWord_5113621, baseEnd_5113621] using wordTrace_append hprefix tailTrace_5113621
  have hstable : (prefixWord ++ tailWord_5113621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113621).length < 2 ^ (prefixWord ++ tailWord_5113621).sum := by decide
  have hdescent : baseEnd_5113621 < baseStart_5113621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113624 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 8]
def baseStart_5113624 : Nat := 118140960795 + 5113624 * 2 ^ 59
def prefixEnd_5113624 : Nat := 4983230072969 + 3 ^ 40 * 5113624 * 2
def baseEnd_5113624 : Nat := 291749666485222906253653

theorem tailTrace_5113624 : CollatzResearch.WordTrace tailWord_5113624 prefixEnd_5113624 291749666485222906253653 := by
  unfold tailWord_5113624
  simp only [CollatzResearch.WordTrace]
  refine ⟨93254594813110530147181963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124339459750814040196242617 93254594813110530147181963)
  ·
    refine ⟨139881892219665795220772945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93254594813110530147181963 139881892219665795220772945)
    ·
      refine ⟨104911419164749346415579709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139881892219665795220772945 104911419164749346415579709)
      ·
        refine ⟨39341782186781004905842391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104911419164749346415579709 39341782186781004905842391)
        ·
          refine ⟨59012673280171507358763587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39341782186781004905842391 59012673280171507358763587)
          ·
            refine ⟨88519009920257261038145381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59012673280171507358763587 88519009920257261038145381)
            ·
              refine ⟨16597314360048236444652259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88519009920257261038145381 16597314360048236444652259)
              ·
                refine ⟨24895971540072354666978389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16597314360048236444652259 24895971540072354666978389)
                ·
                  refine ⟨291749666485222906253653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24895971540072354666978389 291749666485222906253653)
                  ·
                    rfl

theorem cell23_5113624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 8].length) (baseStart_5113624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113624 prefixEnd_5113624 := by exact prefixLift 5113624
  have htrace : WordTrace (prefixWord ++ tailWord_5113624) baseStart_5113624 baseEnd_5113624 := by
    simpa [prefixWord, tailWord_5113624, baseEnd_5113624] using wordTrace_append hprefix tailTrace_5113624
  have hstable : (prefixWord ++ tailWord_5113624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113624).length < 2 ^ (prefixWord ++ tailWord_5113624).sum := by decide
  have hdescent : baseEnd_5113624 < baseStart_5113624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113671 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 1, 5]
def baseStart_5113671 : Nat := 118140960795 + 5113671 * 2 ^ 59
def prefixEnd_5113671 : Nat := 4983230072969 + 3 ^ 40 * 5113671 * 2
def baseEnd_5113671 : Nat := 875257043985922490798387

theorem tailTrace_5113671 : CollatzResearch.WordTrace tailWord_5113671 prefixEnd_5113671 875257043985922490798387 := by
  unfold tailWord_5113671
  simp only [CollatzResearch.WordTrace]
  refine ⟨186510903857050787321324867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124340602571367191547549911 186510903857050787321324867)
  ·
    refine ⟨279766355785576180981987301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186510903857050787321324867 279766355785576180981987301)
    ·
      refine ⟨52456191709795533934122619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279766355785576180981987301 52456191709795533934122619)
      ·
        refine ⟨78684287564693300901183929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52456191709795533934122619 78684287564693300901183929)
        ·
          refine ⟨59013215673519975675887947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78684287564693300901183929 59013215673519975675887947)
          ·
            refine ⟨88519823510279963513831921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59013215673519975675887947 88519823510279963513831921)
            ·
              refine ⟨66389867632709972635373941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88519823510279963513831921 66389867632709972635373941)
              ·
                refine ⟨6224050090566559934566307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66389867632709972635373941 6224050090566559934566307)
                ·
                  refine ⟨9336075135849839901849461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224050090566559934566307 9336075135849839901849461)
                  ·
                    refine ⟨875257043985922490798387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9336075135849839901849461 875257043985922490798387)
                    ·
                      rfl

theorem cell23_5113671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_5113671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113671 prefixEnd_5113671 := by exact prefixLift 5113671
  have htrace : WordTrace (prefixWord ++ tailWord_5113671) baseStart_5113671 baseEnd_5113671 := by
    simpa [prefixWord, tailWord_5113671, baseEnd_5113671] using wordTrace_append hprefix tailTrace_5113671
  have hstable : (prefixWord ++ tailWord_5113671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113671).length < 2 ^ (prefixWord ++ tailWord_5113671).sum := by decide
  have hdescent : baseEnd_5113671 < baseStart_5113671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113701 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 6, 4]
def baseStart_5113701 : Nat := 118140960795 + 5113701 * 2 ^ 59
def prefixEnd_5113701 : Nat := 4983230072969 + 3 ^ 40 * 5113701 * 2
def baseEnd_5113701 : Nat := 875262178792467451673341

theorem tailTrace_5113701 : CollatzResearch.WordTrace tailWord_5113701 prefixEnd_5113701 875262178792467451673341 := by
  unfold tailWord_5113701
  simp only [CollatzResearch.WordTrace]
  refine ⟨186511998046942102444916957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124341332031294734963277971 186511998046942102444916957)
  ·
    refine ⟨69941999267603288416843859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186511998046942102444916957 69941999267603288416843859)
    ·
      refine ⟨104912998901404932625265789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69941999267603288416843859 104912998901404932625265789)
      ·
        refine ⟨39342374588026849734474671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104912998901404932625265789 39342374588026849734474671)
        ·
          refine ⟨59013561882040274601712007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39342374588026849734474671 59013561882040274601712007)
          ·
            refine ⟨88520342823060411902568011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59013561882040274601712007 88520342823060411902568011)
            ·
              refine ⟨132780514234590617853852017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88520342823060411902568011 132780514234590617853852017)
              ·
                refine ⟨99585385675942963390389013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132780514234590617853852017 99585385675942963390389013)
                ·
                  refine ⟨4668064953559826408924485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99585385675942963390389013 4668064953559826408924485)
                  ·
                    refine ⟨875262178792467451673341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4668064953559826408924485 875262178792467451673341)
                    ·
                      rfl

theorem cell23_5113701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_5113701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113701 prefixEnd_5113701 := by exact prefixLift 5113701
  have htrace : WordTrace (prefixWord ++ tailWord_5113701) baseStart_5113701 baseEnd_5113701 := by
    simpa [prefixWord, tailWord_5113701, baseEnd_5113701] using wordTrace_append hprefix tailTrace_5113701
  have hstable : (prefixWord ++ tailWord_5113701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113701).length < 2 ^ (prefixWord ++ tailWord_5113701).sum := by decide
  have hdescent : baseEnd_5113701 < baseStart_5113701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113721 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 4]
def baseStart_5113721 : Nat := 118140960795 + 5113721 * 2 ^ 59
def prefixEnd_5113721 : Nat := 4983230072969 + 3 ^ 40 * 5113721 * 2
def baseEnd_5113721 : Nat := 2625796805990492276769931

theorem tailTrace_5113721 : CollatzResearch.WordTrace tailWord_5113721 prefixEnd_5113721 2625796805990492276769931 := by
  unfold tailWord_5113721
  simp only [CollatzResearch.WordTrace]
  refine ⟨186512727506869645860645017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124341818337913097240430011 186512727506869645860645017)
  ·
    refine ⟨139884545630152234395483763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186512727506869645860645017 139884545630152234395483763)
    ·
      refine ⟨209826818445228351593225645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139884545630152234395483763 209826818445228351593225645)
      ·
        refine ⟨78685056916960631847459617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209826818445228351593225645 78685056916960631847459617)
        ·
          refine ⟨59013792687720473885594713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78685056916960631847459617 59013792687720473885594713)
          ·
            refine ⟨44260344515790355414196035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59013792687720473885594713 44260344515790355414196035)
            ·
              refine ⟨66390516773685533121294053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44260344515790355414196035 66390516773685533121294053)
              ·
                refine ⟨12448221895066037460242635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66390516773685533121294053 12448221895066037460242635)
                ·
                  refine ⟨18672332842599056190363953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12448221895066037460242635 18672332842599056190363953)
                  ·
                    refine ⟨14004249631949292142772965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18672332842599056190363953 14004249631949292142772965)
                    ·
                      refine ⟨2625796805990492276769931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14004249631949292142772965 2625796805990492276769931)
                      ·
                        rfl

theorem cell23_5113721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_5113721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113721 prefixEnd_5113721 := by exact prefixLift 5113721
  have htrace : WordTrace (prefixWord ++ tailWord_5113721) baseStart_5113721 baseEnd_5113721 := by
    simpa [prefixWord, tailWord_5113721, baseEnd_5113721] using wordTrace_append hprefix tailTrace_5113721
  have hstable : (prefixWord ++ tailWord_5113721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113721).length < 2 ^ (prefixWord ++ tailWord_5113721).sum := by decide
  have hdescent : baseEnd_5113721 < baseStart_5113721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113728 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 3]
def baseStart_5113728 : Nat := 118140960795 + 5113728 * 2 ^ 59
def prefixEnd_5113728 : Nat := 4983230072969 + 3 ^ 40 * 5113728 * 2
def baseEnd_5113728 : Nat := 2625800400355073749382399

theorem tailTrace_5113728 : CollatzResearch.WordTrace tailWord_5113728 prefixEnd_5113728 2625800400355073749382399 := by
  unfold tailWord_5113728
  simp only [CollatzResearch.WordTrace]
  refine ⟨93256491408922143028074919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124341988545229524037433225 93256491408922143028074919)
  ·
    refine ⟨139884737113383214542112379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93256491408922143028074919 139884737113383214542112379)
    ·
      refine ⟨209827105670074821813168569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139884737113383214542112379 209827105670074821813168569)
      ·
        refine ⟨157370329252556116359876427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209827105670074821813168569 157370329252556116359876427)
        ·
          refine ⟨236055493878834174539814641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157370329252556116359876427 236055493878834174539814641)
          ·
            refine ⟨177041620409125630904860981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236055493878834174539814641 177041620409125630904860981)
            ·
              refine ⟨16597651913355527897330717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177041620409125630904860981 16597651913355527897330717)
              ·
                refine ⟨6224119467508322961499019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16597651913355527897330717 6224119467508322961499019)
                ·
                  refine ⟨9336179201262484442248529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224119467508322961499019 9336179201262484442248529)
                  ·
                    refine ⟨7002134400946863331686397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9336179201262484442248529 7002134400946863331686397)
                    ·
                      refine ⟨2625800400355073749382399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7002134400946863331686397 2625800400355073749382399)
                      ·
                        rfl

theorem cell23_5113728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_5113728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113728 prefixEnd_5113728 := by exact prefixLift 5113728
  have htrace : WordTrace (prefixWord ++ tailWord_5113728) baseStart_5113728 baseEnd_5113728 := by
    simpa [prefixWord, tailWord_5113728, baseEnd_5113728] using wordTrace_append hprefix tailTrace_5113728
  have hstable : (prefixWord ++ tailWord_5113728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113728).length < 2 ^ (prefixWord ++ tailWord_5113728).sum := by decide
  have hdescent : baseEnd_5113728 < baseStart_5113728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113752 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 1, 6]
def baseStart_5113752 : Nat := 118140960795 + 5113752 * 2 ^ 59
def prefixEnd_5113752 : Nat := 4983230072969 + 3 ^ 40 * 5113752 * 2
def baseEnd_5113752 : Nat := 875270907963593885160763

theorem tailTrace_5113752 : CollatzResearch.WordTrace tailWord_5113752 prefixEnd_5113752 875270907963593885160763 := by
  unfold tailWord_5113752
  simp only [CollatzResearch.WordTrace]
  refine ⟨93256929084878669077511755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124342572113171558770015673 93256929084878669077511755)
  ·
    refine ⟨139885393627318003616267633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93256929084878669077511755 139885393627318003616267633)
    ·
      refine ⟨104914045220488502712200725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139885393627318003616267633 104914045220488502712200725)
      ·
        refine ⟨4917845869710398564634409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104914045220488502712200725 4917845869710398564634409)
        ·
          refine ⟨3688384402282798923475807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4917845869710398564634409 3688384402282798923475807)
          ·
            refine ⟨5532576603424198385213711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3688384402282798923475807 5532576603424198385213711)
            ·
              refine ⟨8298864905136297577820567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5532576603424198385213711 8298864905136297577820567)
              ·
                refine ⟨12448297357704446366730851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8298864905136297577820567 12448297357704446366730851)
                ·
                  refine ⟨18672446036556669550096277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12448297357704446366730851 18672446036556669550096277)
                  ·
                    refine ⟨875270907963593885160763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18672446036556669550096277 875270907963593885160763)
                    ·
                      rfl

theorem cell23_5113752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_5113752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113752 prefixEnd_5113752 := by exact prefixLift 5113752
  have htrace : WordTrace (prefixWord ++ tailWord_5113752) baseStart_5113752 baseEnd_5113752 := by
    simpa [prefixWord, tailWord_5113752, baseEnd_5113752] using wordTrace_append hprefix tailTrace_5113752
  have hstable : (prefixWord ++ tailWord_5113752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113752).length < 2 ^ (prefixWord ++ tailWord_5113752).sum := by decide
  have hdescent : baseEnd_5113752 < baseStart_5113752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113762 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_5113762 : Nat := 118140960795 + 5113762 * 2 ^ 59
def prefixEnd_5113762 : Nat := 4983230072969 + 3 ^ 40 * 5113762 * 2
def baseEnd_5113762 : Nat := 2625817858697326616357243

theorem tailTrace_5113762 : CollatzResearch.WordTrace tailWord_5113762 prefixEnd_5113762 2625817858697326616357243 := by
  unfold tailWord_5113762
  simp only [CollatzResearch.WordTrace]
  refine ⟨46628555724930277465721885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124342815266480739908591693 46628555724930277465721885)
  ·
    refine ⟨17485708396848854049645707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46628555724930277465721885 17485708396848854049645707)
    ·
      refine ⟨26228562595273281074468561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17485708396848854049645707 26228562595273281074468561)
      ·
        refine ⟨19671421946454960805851421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26228562595273281074468561 19671421946454960805851421)
        ·
          refine ⟨7376783229920610302194283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19671421946454960805851421 7376783229920610302194283)
          ·
            refine ⟨11065174844880915453291425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7376783229920610302194283 11065174844880915453291425)
            ·
              refine ⟨8298881133660686589968569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11065174844880915453291425 8298881133660686589968569)
              ·
                refine ⟨6224160850245514942476427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8298881133660686589968569 6224160850245514942476427)
                ·
                  refine ⟨9336241275368272413714641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224160850245514942476427 9336241275368272413714641)
                  ·
                    refine ⟨7002180956526204310285981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9336241275368272413714641 7002180956526204310285981)
                    ·
                      refine ⟨2625817858697326616357243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7002180956526204310285981 2625817858697326616357243)
                      ·
                        rfl

theorem cell23_5113762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_5113762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113762 prefixEnd_5113762 := by exact prefixLift 5113762
  have htrace : WordTrace (prefixWord ++ tailWord_5113762) baseStart_5113762 baseEnd_5113762 := by
    simpa [prefixWord, tailWord_5113762, baseEnd_5113762] using wordTrace_append hprefix tailTrace_5113762
  have hstable : (prefixWord ++ tailWord_5113762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113762).length < 2 ^ (prefixWord ++ tailWord_5113762).sum := by decide
  have hdescent : baseEnd_5113762 < baseStart_5113762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113785 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 1, 3, 2]
def baseStart_5113785 : Nat := 118140960795 + 5113785 * 2 ^ 59
def prefixEnd_5113785 : Nat := 4983230072969 + 3 ^ 40 * 5113785 * 2
def baseEnd_5113785 : Nat := 2625829668752380026369637

theorem tailTrace_5113785 : CollatzResearch.WordTrace tailWord_5113785 prefixEnd_5113785 2625829668752380026369637 := by
  unfold tailWord_5113785
  simp only [CollatzResearch.WordTrace]
  refine ⟨186515061778637784790974809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124343374519091856527316539 186515061778637784790974809)
  ·
    refine ⟨139886296333978338593231107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186515061778637784790974809 139886296333978338593231107)
    ·
      refine ⟨209829444500967507889846661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139886296333978338593231107 209829444500967507889846661)
      ·
        refine ⟨39343020843931407729346249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209829444500967507889846661 39343020843931407729346249)
        ·
          refine ⟨29507265632948555797009687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39343020843931407729346249 29507265632948555797009687)
          ·
            refine ⟨44260898449422833695514531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29507265632948555797009687 44260898449422833695514531)
            ·
              refine ⟨66391347674134250543271797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44260898449422833695514531 66391347674134250543271797)
              ·
                refine ⟨6224188844450085988431731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66391347674134250543271797 6224188844450085988431731)
                ·
                  refine ⟨9336283266675128982647597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224188844450085988431731 9336283266675128982647597)
                  ·
                    refine ⟨3501106225003173368492849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9336283266675128982647597 3501106225003173368492849)
                    ·
                      refine ⟨2625829668752380026369637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3501106225003173368492849 2625829668752380026369637)
                      ·
                        rfl

theorem cell23_5113785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_5113785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113785 prefixEnd_5113785 := by exact prefixLift 5113785
  have htrace : WordTrace (prefixWord ++ tailWord_5113785) baseStart_5113785 baseEnd_5113785 := by
    simpa [prefixWord, tailWord_5113785, baseEnd_5113785] using wordTrace_append hprefix tailTrace_5113785
  have hstable : (prefixWord ++ tailWord_5113785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113785).length < 2 ^ (prefixWord ++ tailWord_5113785).sum := by decide
  have hdescent : baseEnd_5113785 < baseStart_5113785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113801 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 1, 6, 3]
def baseStart_5113801 : Nat := 118140960795 + 5113801 * 2 ^ 59
def prefixEnd_5113801 : Nat := 4983230072969 + 3 ^ 40 * 5113801 * 2
def baseEnd_5113801 : Nat := 2625837884442851963769563

theorem tailTrace_5113801 : CollatzResearch.WordTrace tailWord_5113801 prefixEnd_5113801 2625837884442851963769563 := by
  unfold tailWord_5113801
  simp only [CollatzResearch.WordTrace]
  refine ⟨186515645346579819523557257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124343763564386546349038171 186515645346579819523557257)
  ·
    refine ⟨139886734009934864642667943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186515645346579819523557257 139886734009934864642667943)
    ·
      refine ⟨209830101014902296964001915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139886734009934864642667943 209830101014902296964001915)
      ·
        refine ⟨314745151522353445446002873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209830101014902296964001915 314745151522353445446002873)
        ·
          refine ⟨236058863641765084084502155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314745151522353445446002873 236058863641765084084502155)
          ·
            refine ⟨354088295462647626126753233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236058863641765084084502155 354088295462647626126753233)
            ·
              refine ⟨265566221596985719595064925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354088295462647626126753233 265566221596985719595064925)
              ·
                refine ⟨99587333098869644848149347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265566221596985719595064925 99587333098869644848149347)
                ·
                  refine ⟨149380999648304467272224021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99587333098869644848149347 149380999648304467272224021)
                  ·
                    refine ⟨7002234358514271903385501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 149380999648304467272224021 7002234358514271903385501)
                    ·
                      refine ⟨2625837884442851963769563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7002234358514271903385501 2625837884442851963769563)
                      ·
                        rfl

theorem cell23_5113801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6, 3].length) (baseStart_5113801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113801 prefixEnd_5113801 := by exact prefixLift 5113801
  have htrace : WordTrace (prefixWord ++ tailWord_5113801) baseStart_5113801 baseEnd_5113801 := by
    simpa [prefixWord, tailWord_5113801, baseEnd_5113801] using wordTrace_append hprefix tailTrace_5113801
  have hstable : (prefixWord ++ tailWord_5113801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113801).length < 2 ^ (prefixWord ++ tailWord_5113801).sum := by decide
  have hdescent : baseEnd_5113801 < baseStart_5113801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113885 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_5113885 : Nat := 118140960795 + 5113885 * 2 ^ 59
def prefixEnd_5113885 : Nat := 4983230072969 + 3 ^ 40 * 5113885 * 2
def baseEnd_5113885 : Nat := 875293672272609878373059

theorem tailTrace_5113885 : CollatzResearch.WordTrace tailWord_5113885 prefixEnd_5113885 875293672272609878373059 := by
  unfold tailWord_5113885
  simp only [CollatzResearch.WordTrace]
  refine ⟨186518709078275501869615109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124345806052183667913076739 186518709078275501869615109)
  ·
    refine ⟨34972257952176656600552833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186518709078275501869615109 34972257952176656600552833)
    ·
      refine ⟨26229193464132492450414625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34972257952176656600552833 26229193464132492450414625)
      ·
        refine ⟨19671895098099369337810969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26229193464132492450414625 19671895098099369337810969)
        ·
          refine ⟨14753921323574527003358227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19671895098099369337810969 14753921323574527003358227)
          ·
            refine ⟨22130881985361790505037341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14753921323574527003358227 22130881985361790505037341)
            ·
              refine ⟨8299080744510671439389003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22130881985361790505037341 8299080744510671439389003)
              ·
                refine ⟨12448621116766007159083505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8299080744510671439389003 12448621116766007159083505)
                ·
                  refine ⟨9336465837574505369312629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12448621116766007159083505 9336465837574505369312629)
                  ·
                    refine ⟨875293672272609878373059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9336465837574505369312629 875293672272609878373059)
                    ·
                      rfl

theorem cell23_5113885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_5113885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113885 prefixEnd_5113885 := by exact prefixLift 5113885
  have htrace : WordTrace (prefixWord ++ tailWord_5113885) baseStart_5113885 baseEnd_5113885 := by
    simpa [prefixWord, tailWord_5113885, baseEnd_5113885] using wordTrace_append hprefix tailTrace_5113885
  have hstable : (prefixWord ++ tailWord_5113885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113885).length < 2 ^ (prefixWord ++ tailWord_5113885).sum := by decide
  have hdescent : baseEnd_5113885 < baseStart_5113885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113905 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 2, 4, 2]
def baseStart_5113905 : Nat := 118140960795 + 5113905 * 2 ^ 59
def prefixEnd_5113905 : Nat := 4983230072969 + 3 ^ 40 * 5113905 * 2
def baseEnd_5113905 : Nat := 2625891286430919556869085

theorem tailTrace_5113905 : CollatzResearch.WordTrace tailWord_5113905 prefixEnd_5113905 2625891286430919556869085 := by
  unfold tailWord_5113905
  simp only [CollatzResearch.WordTrace]
  refine ⟨186519438538203045285343169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124346292358802030190228779 186519438538203045285343169)
  ·
    refine ⟨139889578903652283964007377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186519438538203045285343169 139889578903652283964007377)
    ·
      refine ⟨104917184177739212973005533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139889578903652283964007377 104917184177739212973005533)
      ·
        refine ⟨39343944066652204864877075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104917184177739212973005533 39343944066652204864877075)
        ·
          refine ⟨59015916099978307297315613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39343944066652204864877075 59015916099978307297315613)
          ·
            refine ⟨22130968537491865236493355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59015916099978307297315613 22130968537491865236493355)
            ·
              refine ⟨33196452806237797854740033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22130968537491865236493355 33196452806237797854740033)
              ·
                refine ⟨24897339604678348391055025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33196452806237797854740033 24897339604678348391055025)
                ·
                  refine ⟨18673004703508761293291269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24897339604678348391055025 18673004703508761293291269)
                  ·
                    refine ⟨3501188381907892742492113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18673004703508761293291269 3501188381907892742492113)
                    ·
                      refine ⟨2625891286430919556869085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3501188381907892742492113 2625891286430919556869085)
                      ·
                        rfl

theorem cell23_5113905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_5113905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113905 prefixEnd_5113905 := by exact prefixLift 5113905
  have htrace : WordTrace (prefixWord ++ tailWord_5113905) baseStart_5113905 baseEnd_5113905 := by
    simpa [prefixWord, tailWord_5113905, baseEnd_5113905] using wordTrace_append hprefix tailTrace_5113905
  have hstable : (prefixWord ++ tailWord_5113905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113905).length < 2 ^ (prefixWord ++ tailWord_5113905).sum := by decide
  have hdescent : baseEnd_5113905 < baseStart_5113905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113955 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 5, 1, 3]
def baseStart_5113955 : Nat := 118140960795 + 5113955 * 2 ^ 59
def prefixEnd_5113955 : Nat := 4983230072969 + 3 ^ 40 * 5113955 * 2
def baseEnd_5113955 : Nat := 2625916960463644361243855

theorem tailTrace_5113955 : CollatzResearch.WordTrace tailWord_5113955 prefixEnd_5113955 2625916960463644361243855 := by
  unfold tailWord_5113955
  simp only [CollatzResearch.WordTrace]
  refine ⟨186521262188021903824663319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124347508125347935883108879 186521262188021903824663319)
  ·
    refine ⟨279781893282032855736994979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186521262188021903824663319 279781893282032855736994979)
    ·
      refine ⟨419672839923049283605492469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279781893282032855736994979 419672839923049283605492469)
      ·
        refine ⟨39344328742785870338014919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 419672839923049283605492469 39344328742785870338014919)
        ·
          refine ⟨59016493114178805507022379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39344328742785870338014919 59016493114178805507022379)
          ·
            refine ⟨88524739671268208260533569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59016493114178805507022379 88524739671268208260533569)
            ·
              refine ⟨66393554753451156195400177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88524739671268208260533569 66393554753451156195400177)
              ·
                refine ⟨49795166065088367146550133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66393554753451156195400177 49795166065088367146550133)
                ·
                  refine ⟨4668296818602034419989075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49795166065088367146550133 4668296818602034419989075)
                  ·
                    refine ⟨7002445227903051629983613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4668296818602034419989075 7002445227903051629983613)
                    ·
                      refine ⟨2625916960463644361243855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7002445227903051629983613 2625916960463644361243855)
                      ·
                        rfl

theorem cell23_5113955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_5113955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113955 prefixEnd_5113955 := by exact prefixLift 5113955
  have htrace : WordTrace (prefixWord ++ tailWord_5113955) baseStart_5113955 baseEnd_5113955 := by
    simpa [prefixWord, tailWord_5113955, baseEnd_5113955] using wordTrace_append hprefix tailTrace_5113955
  have hstable : (prefixWord ++ tailWord_5113955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113955).length < 2 ^ (prefixWord ++ tailWord_5113955).sum := by decide
  have hdescent : baseEnd_5113955 < baseStart_5113955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5113992 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 1, 5]
def baseStart_5113992 : Nat := 118140960795 + 5113992 * 2 ^ 59
def prefixEnd_5113992 : Nat := 4983230072969 + 3 ^ 40 * 5113992 * 2
def baseEnd_5113992 : Nat := 875311986415953572160395

theorem tailTrace_5113992 : CollatzResearch.WordTrace tailWord_5113992 prefixEnd_5113992 875311986415953572160395 := by
  unfold tailWord_5113992
  simp only [CollatzResearch.WordTrace]
  refine ⟨93261305844443929571880115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124348407792591906095840153 93261305844443929571880115)
  ·
    refine ⟨139891958766665894357820173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93261305844443929571880115 139891958766665894357820173)
    ·
      refine ⟨52459484537499710384182565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139891958766665894357820173 52459484537499710384182565)
      ·
        refine ⟨9836153350781195697034231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52459484537499710384182565 9836153350781195697034231)
        ·
          refine ⟨14754230026171793545551347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9836153350781195697034231 14754230026171793545551347)
          ·
            refine ⟨22131345039257690318327021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14754230026171793545551347 22131345039257690318327021)
            ·
              refine ⟨8299254389721633869372633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22131345039257690318327021 8299254389721633869372633)
              ·
                refine ⟨6224440792291225402029475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8299254389721633869372633 6224440792291225402029475)
                ·
                  refine ⟨9336661188436838103044213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224440792291225402029475 9336661188436838103044213)
                  ·
                    refine ⟨875311986415953572160395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9336661188436838103044213 875311986415953572160395)
                    ·
                      rfl

theorem cell23_5113992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_5113992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5113992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5113992 prefixEnd_5113992 := by exact prefixLift 5113992
  have htrace : WordTrace (prefixWord ++ tailWord_5113992) baseStart_5113992 baseEnd_5113992 := by
    simpa [prefixWord, tailWord_5113992, baseEnd_5113992] using wordTrace_append hprefix tailTrace_5113992
  have hstable : (prefixWord ++ tailWord_5113992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5113992).length < 2 ^ (prefixWord ++ tailWord_5113992).sum := by decide
  have hdescent : baseEnd_5113992 < baseStart_5113992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5113992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114046 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_5114046 : Nat := 118140960795 + 5114046 * 2 ^ 59
def prefixEnd_5114046 : Nat := 4983230072969 + 3 ^ 40 * 5114046 * 2
def baseEnd_5114046 : Nat := 2625963687203203505205937

theorem tailTrace_5114046 : CollatzResearch.WordTrace tailWord_5114046 prefixEnd_5114046 2625963687203203505205937 := by
  unfold tailWord_5114046
  simp only [CollatzResearch.WordTrace]
  refine ⟨23315572653836528295778249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124349720820461484244150661 23315572653836528295778249)
  ·
    refine ⟨17486679490377396221833687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23315572653836528295778249 17486679490377396221833687)
    ·
      refine ⟨26230019235566094332750531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17486679490377396221833687 26230019235566094332750531)
      ·
        refine ⟨39345028853349141499125797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26230019235566094332750531 39345028853349141499125797)
        ·
          refine ⟨7377192910002964031086087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39345028853349141499125797 7377192910002964031086087)
          ·
            refine ⟨11065789365004446046629131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7377192910002964031086087 11065789365004446046629131)
            ·
              refine ⟨16598684047506669069943697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11065789365004446046629131 16598684047506669069943697)
              ·
                refine ⟨12449013035630001802457773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16598684047506669069943697 12449013035630001802457773)
                ·
                  refine ⟨4668379888361250675921665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12449013035630001802457773 4668379888361250675921665)
                  ·
                    refine ⟨3501284916270938006941249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4668379888361250675921665 3501284916270938006941249)
                    ·
                      refine ⟨2625963687203203505205937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3501284916270938006941249 2625963687203203505205937)
                      ·
                        rfl

theorem cell23_5114046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_5114046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114046 prefixEnd_5114046 := by exact prefixLift 5114046
  have htrace : WordTrace (prefixWord ++ tailWord_5114046) baseStart_5114046 baseEnd_5114046 := by
    simpa [prefixWord, tailWord_5114046, baseEnd_5114046] using wordTrace_append hprefix tailTrace_5114046
  have hstable : (prefixWord ++ tailWord_5114046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114046).length < 2 ^ (prefixWord ++ tailWord_5114046).sum := by decide
  have hdescent : baseEnd_5114046 < baseStart_5114046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114052 : List Nat := [2, 3, 3, 1, 2, 2, 3, 7]
def baseStart_5114052 : Nat := 118140960795 + 5114052 * 2 ^ 59
def prefixEnd_5114052 : Nat := 4983230072969 + 3 ^ 40 * 5114052 * 2
def baseEnd_5114052 : Nat := 97258028447671499323367

theorem tailTrace_5114052 : CollatzResearch.WordTrace tailWord_5114052 prefixEnd_5114052 97258028447671499323367 := by
  unfold tailWord_5114052
  simp only [CollatzResearch.WordTrace]
  refine ⟨93262400034335244695472205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124349866712446992927296273 93262400034335244695472205)
  ·
    refine ⟨34973400012875716760802077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93262400034335244695472205 34973400012875716760802077)
    ·
      refine ⟨13115025004828393785300779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34973400012875716760802077 13115025004828393785300779)
      ·
        refine ⟨19672537507242590677951169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13115025004828393785300779 19672537507242590677951169)
        ·
          refine ⟨14754403130431943008463377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19672537507242590677951169 14754403130431943008463377)
          ·
            refine ⟨11065802347823957256347533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14754403130431943008463377 11065802347823957256347533)
            ·
              refine ⟨4149675880433983971130325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11065802347823957256347533 4149675880433983971130325)
              ·
                refine ⟨97258028447671499323367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4149675880433983971130325 97258028447671499323367)
                ·
                  rfl

theorem cell23_5114052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 7].length) (baseStart_5114052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114052 prefixEnd_5114052 := by exact prefixLift 5114052
  have htrace : WordTrace (prefixWord ++ tailWord_5114052) baseStart_5114052 baseEnd_5114052 := by
    simpa [prefixWord, tailWord_5114052, baseEnd_5114052] using wordTrace_append hprefix tailTrace_5114052
  have hstable : (prefixWord ++ tailWord_5114052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114052).length < 2 ^ (prefixWord ++ tailWord_5114052).sum := by decide
  have hdescent : baseEnd_5114052 < baseStart_5114052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114062 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_5114062 : Nat := 118140960795 + 5114062 * 2 ^ 59
def prefixEnd_5114062 : Nat := 4983230072969 + 3 ^ 40 * 5114062 * 2
def baseEnd_5114062 : Nat := 2625971902893675442605863

theorem tailTrace_5114062 : CollatzResearch.WordTrace tailWord_5114062 prefixEnd_5114062 2625971902893675442605863 := by
  unfold tailWord_5114062
  simp only [CollatzResearch.WordTrace]
  refine ⟨23315645599829282637351055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124350109865756174065872293 23315645599829282637351055)
  ·
    refine ⟨34973468399743923956026583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23315645599829282637351055 34973468399743923956026583)
    ·
      refine ⟨52460202599615885934039875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34973468399743923956026583 52460202599615885934039875)
      ·
        refine ⟨78690303899423828901059813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52460202599615885934039875 78690303899423828901059813)
        ·
          refine ⟨14754431981141967918948715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78690303899423828901059813 14754431981141967918948715)
          ·
            refine ⟨22131647971712951878423073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14754431981141967918948715 22131647971712951878423073)
            ·
              refine ⟨16598735978784713908817305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22131647971712951878423073 16598735978784713908817305)
              ·
                refine ⟨12449051984088535431612979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16598735978784713908817305 12449051984088535431612979)
                ·
                  refine ⟨18673577976132803147419469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12449051984088535431612979 18673577976132803147419469)
                  ·
                    refine ⟨7002591741049801180282301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18673577976132803147419469 7002591741049801180282301)
                    ·
                      refine ⟨2625971902893675442605863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7002591741049801180282301 2625971902893675442605863)
                      ·
                        rfl

theorem cell23_5114062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_5114062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114062 prefixEnd_5114062 := by exact prefixLift 5114062
  have htrace : WordTrace (prefixWord ++ tailWord_5114062) baseStart_5114062 baseEnd_5114062 := by
    simpa [prefixWord, tailWord_5114062, baseEnd_5114062] using wordTrace_append hprefix tailTrace_5114062
  have hstable : (prefixWord ++ tailWord_5114062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114062).length < 2 ^ (prefixWord ++ tailWord_5114062).sum := by decide
  have hdescent : baseEnd_5114062 < baseStart_5114062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114066 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_5114066 : Nat := 118140960795 + 5114066 * 2 ^ 59
def prefixEnd_5114066 : Nat := 4983230072969 + 3 ^ 40 * 5114066 * 2
def baseEnd_5114066 : Nat := 2625973956816293426955845

theorem tailTrace_5114066 : CollatzResearch.WordTrace tailWord_5114066 prefixEnd_5114066 2625973956816293426955845 := by
  unfold tailWord_5114066
  simp only [CollatzResearch.WordTrace]
  refine ⟨46631327672654942445488513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124350207127079846521302701 46631327672654942445488513)
  ·
    refine ⟨34973495754491206834116385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46631327672654942445488513 34973495754491206834116385)
    ·
      refine ⟨26230121815868405125587289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34973495754491206834116385 26230121815868405125587289)
      ·
        refine ⟨19672591361901303844190467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26230121815868405125587289 19672591361901303844190467)
        ·
          refine ⟨29508887042851955766285701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19672591361901303844190467 29508887042851955766285701)
          ·
            refine ⟨5532916320534741706178569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29508887042851955766285701 5532916320534741706178569)
            ·
              refine ⟨4149687240401056279633927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5532916320534741706178569 4149687240401056279633927)
              ·
                refine ⟨6224530860601584419450891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149687240401056279633927 6224530860601584419450891)
                ·
                  refine ⟨9336796290902376629176337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224530860601584419450891 9336796290902376629176337)
                  ·
                    refine ⟨7002597218176782471882253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9336796290902376629176337 7002597218176782471882253)
                    ·
                      refine ⟨2625973956816293426955845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7002597218176782471882253 2625973956816293426955845)
                      ·
                        rfl

theorem cell23_5114066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_5114066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114066 prefixEnd_5114066 := by exact prefixLift 5114066
  have htrace : WordTrace (prefixWord ++ tailWord_5114066) baseStart_5114066 baseEnd_5114066 := by
    simpa [prefixWord, tailWord_5114066, baseEnd_5114066] using wordTrace_append hprefix tailTrace_5114066
  have hstable : (prefixWord ++ tailWord_5114066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114066).length < 2 ^ (prefixWord ++ tailWord_5114066).sum := by decide
  have hdescent : baseEnd_5114066 < baseStart_5114066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114095 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 2, 6]
def baseStart_5114095 : Nat := 118140960795 + 5114095 * 2 ^ 59
def prefixEnd_5114095 : Nat := 4983230072969 + 3 ^ 40 * 5114095 * 2
def baseEnd_5114095 : Nat := 875329615918424604497737

theorem tailTrace_5114095 : CollatzResearch.WordTrace tailWord_5114095 prefixEnd_5114095 875329615918424604497737 := by
  unfold tailWord_5114095
  simp only [CollatzResearch.WordTrace]
  refine ⟨186526368407514707734759739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124350912271676471823173159 186526368407514707734759739)
  ·
    refine ⟨279789552611272061602139609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186526368407514707734759739 279789552611272061602139609)
    ·
      refine ⟨209842164458454046201604707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279789552611272061602139609 209842164458454046201604707)
      ·
        refine ⟨314763246687681069302407061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209842164458454046201604707 314763246687681069302407061)
        ·
          refine ⟨14754527188485050123550331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 314763246687681069302407061 14754527188485050123550331)
          ·
            refine ⟨22131790782727575185325497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14754527188485050123550331 22131790782727575185325497)
            ·
              refine ⟨16598843087045681388994123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22131790782727575185325497 16598843087045681388994123)
              ·
                refine ⟨24898264630568522083491185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16598843087045681388994123 24898264630568522083491185)
                ·
                  refine ⟨18673698472926391562618389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24898264630568522083491185 18673698472926391562618389)
                  ·
                    refine ⟨875329615918424604497737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18673698472926391562618389 875329615918424604497737)
                    ·
                      rfl

theorem cell23_5114095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 6].length) (baseStart_5114095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114095 prefixEnd_5114095 := by exact prefixLift 5114095
  have htrace : WordTrace (prefixWord ++ tailWord_5114095) baseStart_5114095 baseEnd_5114095 := by
    simpa [prefixWord, tailWord_5114095, baseEnd_5114095] using wordTrace_append hprefix tailTrace_5114095
  have hstable : (prefixWord ++ tailWord_5114095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114095).length < 2 ^ (prefixWord ++ tailWord_5114095).sum := by decide
  have hdescent : baseEnd_5114095 < baseStart_5114095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114165 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_5114165 : Nat := 118140960795 + 5114165 * 2 ^ 59
def prefixEnd_5114165 : Nat := 4983230072969 + 3 ^ 40 * 5114165 * 2
def baseEnd_5114165 : Nat := 2626024791401088539617889

theorem tailTrace_5114165 : CollatzResearch.WordTrace tailWord_5114165 prefixEnd_5114165 2626024791401088539617889 := by
  unfold tailWord_5114165
  simp only [CollatzResearch.WordTrace]
  refine ⟨186528921517261109689807949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124352614344840739793205299 186528921517261109689807949)
  ·
    refine ⟨69948345568972916133677981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186528921517261109689807949 69948345568972916133677981)
    ·
      refine ⟨26230629588364843550129243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69948345568972916133677981 26230629588364843550129243)
      ·
        refine ⟨39345944382547265325193865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26230629588364843550129243 39345944382547265325193865)
        ·
          refine ⟨29509458286910448993895399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39345944382547265325193865 29509458286910448993895399)
          ·
            refine ⟨44264187430365673490843099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29509458286910448993895399 44264187430365673490843099)
            ·
              refine ⟨66396281145548510236264649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44264187430365673490843099 66396281145548510236264649)
              ·
                refine ⟨49797210859161382677198487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66396281145548510236264649 49797210859161382677198487)
                ·
                  refine ⟨74695816288742074015797731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49797210859161382677198487 74695816288742074015797731)
                  ·
                    refine ⟨112043724433113111023696597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74695816288742074015797731 112043724433113111023696597)
                    ·
                      refine ⟨2626024791401088539617889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112043724433113111023696597 2626024791401088539617889)
                      ·
                        rfl

theorem cell23_5114165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_5114165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114165 prefixEnd_5114165 := by exact prefixLift 5114165
  have htrace : WordTrace (prefixWord ++ tailWord_5114165) baseStart_5114165 baseEnd_5114165 := by
    simpa [prefixWord, tailWord_5114165, baseEnd_5114165] using wordTrace_append hprefix tailTrace_5114165
  have hstable : (prefixWord ++ tailWord_5114165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114165).length < 2 ^ (prefixWord ++ tailWord_5114165).sum := by decide
  have hdescent : baseEnd_5114165 < baseStart_5114165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114172 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 2, 5]
def baseStart_5114172 : Nat := 118140960795 + 5114172 * 2 ^ 59
def prefixEnd_5114172 : Nat := 4983230072969 + 3 ^ 40 * 5114172 * 2
def baseEnd_5114172 : Nat := 875342795255223337410119

theorem tailTrace_5114172 : CollatzResearch.WordTrace tailWord_5114172 prefixEnd_5114172 875342795255223337410119 := by
  unfold tailWord_5114172
  simp only [CollatzResearch.WordTrace]
  refine ⟨93264588414117874942656385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124352784552157166590208513 93264588414117874942656385)
  ·
    refine ⟨69948441310588406206992289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93264588414117874942656385 69948441310588406206992289)
    ·
      refine ⟨52461330982941304655244217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69948441310588406206992289 52461330982941304655244217)
      ·
        refine ⟨39345998237205978491433163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52461330982941304655244217 39345998237205978491433163)
        ·
          refine ⟨59018997355808967737149745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39345998237205978491433163 59018997355808967737149745)
          ·
            refine ⟨44264248016856725802862309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59018997355808967737149745 44264248016856725802862309)
            ·
              refine ⟨8299546503160636088036683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44264248016856725802862309 8299546503160636088036683)
              ·
                refine ⟨12449319754740954132055025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8299546503160636088036683 12449319754740954132055025)
                ·
                  refine ⟨9336989816055715599041269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12449319754740954132055025 9336989816055715599041269)
                  ·
                    refine ⟨875342795255223337410119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9336989816055715599041269 875342795255223337410119)
                    ·
                      rfl

theorem cell23_5114172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_5114172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114172 prefixEnd_5114172 := by exact prefixLift 5114172
  have htrace : WordTrace (prefixWord ++ tailWord_5114172) baseStart_5114172 baseEnd_5114172 := by
    simpa [prefixWord, tailWord_5114172, baseEnd_5114172] using wordTrace_append hprefix tailTrace_5114172
  have hstable : (prefixWord ++ tailWord_5114172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114172).length < 2 ^ (prefixWord ++ tailWord_5114172).sum := by decide
  have hdescent : baseEnd_5114172 < baseStart_5114172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114192 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 4]
def baseStart_5114192 : Nat := 118140960795 + 5114192 * 2 ^ 59
def prefixEnd_5114192 : Nat := 4983230072969 + 3 ^ 40 * 5114192 * 2
def baseEnd_5114192 : Nat := 2626038655378759933980265

theorem tailTrace_5114192 : CollatzResearch.WordTrace tailWord_5114192 prefixEnd_5114192 2626038655378759933980265 := by
  unfold tailWord_5114192
  simp only [CollatzResearch.WordTrace]
  refine ⟨93264953144081646650520415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124353270858775528867360553 93264953144081646650520415)
  ·
    refine ⟨139897429716122469975780623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93264953144081646650520415 139897429716122469975780623)
    ·
      refine ⟨209846144574183704963670935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139897429716122469975780623 209846144574183704963670935)
      ·
        refine ⟨314769216861275557445506403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209846144574183704963670935 314769216861275557445506403)
        ·
          refine ⟨472153825291913336168259605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314769216861275557445506403 472153825291913336168259605)
          ·
            refine ⟨22132210560558437632887169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 472153825291913336168259605 22132210560558437632887169)
            ·
              refine ⟨16599157920418828224665377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22132210560558437632887169 16599157920418828224665377)
              ·
                refine ⟨12449368440314121168499033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16599157920418828224665377 12449368440314121168499033)
                ·
                  refine ⟨9337026330235590876374275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12449368440314121168499033 9337026330235590876374275)
                  ·
                    refine ⟨14005539495353386314561413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9337026330235590876374275 14005539495353386314561413)
                    ·
                      refine ⟨2626038655378759933980265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14005539495353386314561413 2626038655378759933980265)
                      ·
                        rfl

theorem cell23_5114192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_5114192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114192 prefixEnd_5114192 := by exact prefixLift 5114192
  have htrace : WordTrace (prefixWord ++ tailWord_5114192) baseStart_5114192 baseEnd_5114192 := by
    simpa [prefixWord, tailWord_5114192, baseEnd_5114192] using wordTrace_append hprefix tailTrace_5114192
  have hstable : (prefixWord ++ tailWord_5114192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114192).length < 2 ^ (prefixWord ++ tailWord_5114192).sum := by decide
  have hdescent : baseEnd_5114192 < baseStart_5114192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114202 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 3, 4]
def baseStart_5114202 : Nat := 118140960795 + 5114202 * 2 ^ 59
def prefixEnd_5114202 : Nat := 4983230072969 + 3 ^ 40 * 5114202 * 2
def baseEnd_5114202 : Nat := 875347930061768298285073

theorem tailTrace_5114202 : CollatzResearch.WordTrace tailWord_5114202 prefixEnd_5114202 875347930061768298285073 := by
  unfold tailWord_5114202
  simp only [CollatzResearch.WordTrace]
  refine ⟨46632567754531766252226215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124353514012084710005936573 46632567754531766252226215)
  ·
    refine ⟨69948851631797649378339323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46632567754531766252226215 69948851631797649378339323)
    ·
      refine ⟨104923277447696474067508985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69948851631797649378339323 104923277447696474067508985)
      ·
        refine ⟨78692458085772355550631739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104923277447696474067508985 78692458085772355550631739)
        ·
          refine ⟨118038687128658533325947609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78692458085772355550631739 118038687128658533325947609)
          ·
            refine ⟨88529015346493899994460707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118038687128658533325947609 88529015346493899994460707)
            ·
              refine ⟨132793523019740849991691061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88529015346493899994460707 132793523019740849991691061)
              ·
                refine ⟨12449392783100704686721037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132793523019740849991691061 12449392783100704686721037)
                ·
                  refine ⟨4668522293662764257520389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12449392783100704686721037 4668522293662764257520389)
                  ·
                    refine ⟨875347930061768298285073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4668522293662764257520389 875347930061768298285073)
                    ·
                      rfl

theorem cell23_5114202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_5114202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114202 prefixEnd_5114202 := by exact prefixLift 5114202
  have htrace : WordTrace (prefixWord ++ tailWord_5114202) baseStart_5114202 baseEnd_5114202 := by
    simpa [prefixWord, tailWord_5114202, baseEnd_5114202] using wordTrace_append hprefix tailTrace_5114202
  have hstable : (prefixWord ++ tailWord_5114202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114202).length < 2 ^ (prefixWord ++ tailWord_5114202).sum := by decide
  have hdescent : baseEnd_5114202 < baseStart_5114202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114212 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_5114212 : Nat := 118140960795 + 5114212 * 2 ^ 59
def prefixEnd_5114212 : Nat := 4983230072969 + 3 ^ 40 * 5114212 * 2
def baseEnd_5114212 : Nat := 2626048924991849855730173

theorem tailTrace_5114212 : CollatzResearch.WordTrace tailWord_5114212 prefixEnd_5114212 2626048924991849855730173 := by
  unfold tailWord_5114212
  simp only [CollatzResearch.WordTrace]
  refine ⟨93265317874045418358384445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124353757165393891144512593 93265317874045418358384445)
  ·
    refine ⟨34974494202767031884394167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93265317874045418358384445 34974494202767031884394167)
    ·
      refine ⟨52461741304150547826591251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34974494202767031884394167 52461741304150547826591251)
      ·
        refine ⟨78692611956225821739886877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52461741304150547826591251 78692611956225821739886877)
        ·
          refine ⟨29509729483584683152457579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78692611956225821739886877 29509729483584683152457579)
          ·
            refine ⟨44264594225377024728686369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29509729483584683152457579 44264594225377024728686369)
            ·
              refine ⟨33198445669032768546514777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44264594225377024728686369 33198445669032768546514777)
              ·
                refine ⟨24898834251774576409886083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33198445669032768546514777 24898834251774576409886083)
                ·
                  refine ⟨37348251377661864614829125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24898834251774576409886083 37348251377661864614829125)
                  ·
                    refine ⟨7002797133311599615280461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37348251377661864614829125 7002797133311599615280461)
                    ·
                      refine ⟨2626048924991849855730173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7002797133311599615280461 2626048924991849855730173)
                      ·
                        rfl

theorem cell23_5114212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_5114212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114212 prefixEnd_5114212 := by exact prefixLift 5114212
  have htrace : WordTrace (prefixWord ++ tailWord_5114212) baseStart_5114212 baseEnd_5114212 := by
    simpa [prefixWord, tailWord_5114212, baseEnd_5114212] using wordTrace_append hprefix tailTrace_5114212
  have hstable : (prefixWord ++ tailWord_5114212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114212).length < 2 ^ (prefixWord ++ tailWord_5114212).sum := by decide
  have hdescent : baseEnd_5114212 < baseStart_5114212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114229 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_5114229 : Nat := 118140960795 + 5114229 * 2 ^ 59
def prefixEnd_5114229 : Nat := 4983230072969 + 3 ^ 40 * 5114229 * 2
def baseEnd_5114229 : Nat := 2626057654162976289217595

theorem tailTrace_5114229 : CollatzResearch.WordTrace tailWord_5114229 prefixEnd_5114229 2626057654162976289217595 := by
  unfold tailWord_5114229
  simp only [CollatzResearch.WordTrace]
  refine ⟨186531255789029248620137741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124354170526019499080091827 186531255789029248620137741)
  ·
    refine ⟨69949220920885968232551653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186531255789029248620137741 69949220920885968232551653)
    ·
      refine ⟨13115478922666119043603435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69949220920885968232551653 13115478922666119043603435)
      ·
        refine ⟨19673218383999178565405153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13115478922666119043603435 19673218383999178565405153)
        ·
          refine ⟨14754913787999383924053865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19673218383999178565405153 14754913787999383924053865)
          ·
            refine ⟨11066185340999537943040399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14754913787999383924053865 11066185340999537943040399)
            ·
              refine ⟨16599278011499306914560599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11066185340999537943040399 16599278011499306914560599)
              ·
                refine ⟨24898917017248960371840899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16599278011499306914560599 24898917017248960371840899)
                ·
                  refine ⟨37348375525873440557761349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24898917017248960371840899 37348375525873440557761349)
                  ·
                    refine ⟨7002820411101270104580253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37348375525873440557761349 7002820411101270104580253)
                    ·
                      refine ⟨2626057654162976289217595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7002820411101270104580253 2626057654162976289217595)
                      ·
                        rfl

theorem cell23_5114229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_5114229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114229 prefixEnd_5114229 := by exact prefixLift 5114229
  have htrace : WordTrace (prefixWord ++ tailWord_5114229) baseStart_5114229 baseEnd_5114229 := by
    simpa [prefixWord, tailWord_5114229, baseEnd_5114229] using wordTrace_append hprefix tailTrace_5114229
  have hstable : (prefixWord ++ tailWord_5114229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114229).length < 2 ^ (prefixWord ++ tailWord_5114229).sum := by decide
  have hdescent : baseEnd_5114229 < baseStart_5114229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114249 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 6]
def baseStart_5114249 : Nat := 118140960795 + 5114249 * 2 ^ 59
def prefixEnd_5114249 : Nat := 4983230072969 + 3 ^ 40 * 5114249 * 2
def baseEnd_5114249 : Nat := 291785324864007356774167

theorem tailTrace_5114249 : CollatzResearch.WordTrace tailWord_5114249 prefixEnd_5114249 291785324864007356774167 := by
  unfold tailWord_5114249
  simp only [CollatzResearch.WordTrace]
  refine ⟨186531985248956792035865801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124354656832637861357243867 186531985248956792035865801)
  ·
    refine ⟨139898988936717594026899351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186531985248956792035865801 139898988936717594026899351)
    ·
      refine ⟨209848483405076391040349027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139898988936717594026899351 209848483405076391040349027)
      ·
        refine ⟨314772725107614586560523541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209848483405076391040349027 314772725107614586560523541)
        ·
          refine ⟨14754971489419433745024541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 314772725107614586560523541 14754971489419433745024541)
          ·
            refine ⟨5533114308532287654384203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14754971489419433745024541 5533114308532287654384203)
            ·
              refine ⟨8299671462798431481576305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5533114308532287654384203 8299671462798431481576305)
              ·
                refine ⟨6224753597098823611182229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8299671462798431481576305 6224753597098823611182229)
                ·
                  refine ⟨291785324864007356774167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6224753597098823611182229 291785324864007356774167)
                  ·
                    rfl

theorem cell23_5114249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 6].length) (baseStart_5114249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114249 prefixEnd_5114249 := by exact prefixLift 5114249
  have htrace : WordTrace (prefixWord ++ tailWord_5114249) baseStart_5114249 baseEnd_5114249 := by
    simpa [prefixWord, tailWord_5114249, baseEnd_5114249] using wordTrace_append hprefix tailTrace_5114249
  have hstable : (prefixWord ++ tailWord_5114249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114249).length < 2 ^ (prefixWord ++ tailWord_5114249).sum := by decide
  have hdescent : baseEnd_5114249 < baseStart_5114249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114279 : List Nat := [1, 1, 6, 1, 1, 2, 1, 4, 1, 5]
def baseStart_5114279 : Nat := 118140960795 + 5114279 * 2 ^ 59
def prefixEnd_5114279 : Nat := 4983230072969 + 3 ^ 40 * 5114279 * 2
def baseEnd_5114279 : Nat := 875361109398567031197455

theorem tailTrace_5114279 : CollatzResearch.WordTrace tailWord_5114279 prefixEnd_5114279 875361109398567031197455 := by
  unfold tailWord_5114279
  simp only [CollatzResearch.WordTrace]
  refine ⟨186533079438848107159457891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124355386292565404772971927 186533079438848107159457891)
  ·
    refine ⟨279799619158272160739186837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186533079438848107159457891 279799619158272160739186837)
    ·
      refine ⟨13115607148044007534649383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 279799619158272160739186837 13115607148044007534649383)
      ·
        refine ⟨19673410722066011301974075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13115607148044007534649383 19673410722066011301974075)
        ·
          refine ⟨29510116083099016952961113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19673410722066011301974075 29510116083099016952961113)
          ·
            refine ⟨22132587062324262714720835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29510116083099016952961113 22132587062324262714720835)
            ·
              refine ⟨33198880593486394072081253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22132587062324262714720835 33198880593486394072081253)
              ·
                refine ⟨6224790111278698888515235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33198880593486394072081253 6224790111278698888515235)
                ·
                  refine ⟨9337185166918048332772853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224790111278698888515235 9337185166918048332772853)
                  ·
                    refine ⟨875361109398567031197455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9337185166918048332772853 875361109398567031197455)
                    ·
                      rfl

theorem cell23_5114279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_5114279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114279 prefixEnd_5114279 := by exact prefixLift 5114279
  have htrace : WordTrace (prefixWord ++ tailWord_5114279) baseStart_5114279 baseEnd_5114279 := by
    simpa [prefixWord, tailWord_5114279, baseEnd_5114279] using wordTrace_append hprefix tailTrace_5114279
  have hstable : (prefixWord ++ tailWord_5114279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114279).length < 2 ^ (prefixWord ++ tailWord_5114279).sum := by decide
  have hdescent : baseEnd_5114279 < baseStart_5114279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114312 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_5114312 : Nat := 118140960795 + 5114312 * 2 ^ 59
def prefixEnd_5114312 : Nat := 4983230072969 + 3 ^ 40 * 5114312 * 2
def baseEnd_5114312 : Nat := 2626100273057299464479713

theorem tailTrace_5114312 : CollatzResearch.WordTrace tailWord_5114312 prefixEnd_5114312 2626100273057299464479713 := by
  unfold tailWord_5114312
  simp only [CollatzResearch.WordTrace]
  refine ⟨93267141523864276897704595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124356188698485702530272793 93267141523864276897704595)
  ·
    refine ⟨139900712285796415346556893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93267141523864276897704595 139900712285796415346556893)
    ·
      refine ⟨52462767107173655754958835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139900712285796415346556893 52462767107173655754958835)
      ·
        refine ⟨78694150660760483632438253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52462767107173655754958835 78694150660760483632438253)
        ·
          refine ⟨29510306497785181362164345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78694150660760483632438253 29510306497785181362164345)
          ·
            refine ⟨22132729873338886021623259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29510306497785181362164345 22132729873338886021623259)
            ·
              refine ⟨33199094810008329032434889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22132729873338886021623259 33199094810008329032434889)
              ·
                refine ⟨24899321107506246774326167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33199094810008329032434889 24899321107506246774326167)
                ·
                  refine ⟨37348981661259370161489251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24899321107506246774326167 37348981661259370161489251)
                  ·
                    refine ⟨56023472491889055242233877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37348981661259370161489251 56023472491889055242233877)
                    ·
                      refine ⟨2626100273057299464479713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56023472491889055242233877 2626100273057299464479713)
                      ·
                        rfl

theorem cell23_5114312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_5114312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114312 prefixEnd_5114312 := by exact prefixLift 5114312
  have htrace : WordTrace (prefixWord ++ tailWord_5114312) baseStart_5114312 baseEnd_5114312 := by
    simpa [prefixWord, tailWord_5114312, baseEnd_5114312] using wordTrace_append hprefix tailTrace_5114312
  have hstable : (prefixWord ++ tailWord_5114312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114312).length < 2 ^ (prefixWord ++ tailWord_5114312).sum := by decide
  have hdescent : baseEnd_5114312 < baseStart_5114312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114410 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_5114410 : Nat := 118140960795 + 5114410 * 2 ^ 59
def prefixEnd_5114410 : Nat := 4983230072969 + 3 ^ 40 * 5114410 * 2
def baseEnd_5114410 : Nat := 2626150594161440081054263

theorem tailTrace_5114410 : CollatzResearch.WordTrace tailWord_5114410 prefixEnd_5114410 2626150594161440081054263 := by
  unfold tailWord_5114410
  simp only [CollatzResearch.WordTrace]
  refine ⟨46634464350343379133119171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124358571600915677688317789 46634464350343379133119171)
  ·
    refine ⟨69951696525515068699678757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46634464350343379133119171 69951696525515068699678757)
    ·
      refine ⟨13115943098534075381189767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69951696525515068699678757 13115943098534075381189767)
      ·
        refine ⟨19673914647801113071784651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13115943098534075381189767 19673914647801113071784651)
        ·
          refine ⟨29510871971701669607676977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19673914647801113071784651 29510871971701669607676977)
          ·
            refine ⟨22133153978776252205757733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29510871971701669607676977 22133153978776252205757733)
            ·
              refine ⟨4149966371020547288579575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22133153978776252205757733 4149966371020547288579575)
              ·
                refine ⟨6224949556530820932869363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4149966371020547288579575 6224949556530820932869363)
                ·
                  refine ⟨9337424334796231399304045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6224949556530820932869363 9337424334796231399304045)
                  ·
                    refine ⟨3501534125548586774739017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9337424334796231399304045 3501534125548586774739017)
                    ·
                      refine ⟨2626150594161440081054263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3501534125548586774739017 2626150594161440081054263)
                      ·
                        rfl

theorem cell23_5114410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_5114410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114410 prefixEnd_5114410 := by exact prefixLift 5114410
  have htrace : WordTrace (prefixWord ++ tailWord_5114410) baseStart_5114410 baseEnd_5114410 := by
    simpa [prefixWord, tailWord_5114410, baseEnd_5114410] using wordTrace_append hprefix tailTrace_5114410
  have hstable : (prefixWord ++ tailWord_5114410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114410).length < 2 ^ (prefixWord ++ tailWord_5114410).sum := by decide
  have hdescent : baseEnd_5114410 < baseStart_5114410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114429 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 7]
def baseStart_5114429 : Nat := 118140960795 + 5114429 * 2 ^ 59
def prefixEnd_5114429 : Nat := 4983230072969 + 3 ^ 40 * 5114429 * 2
def baseEnd_5114429 : Nat := 291795594477097278524075

theorem tailTrace_5114429 : CollatzResearch.WordTrace tailWord_5114429 prefixEnd_5114429 291795594477097278524075 := by
  unfold tailWord_5114429
  simp only [CollatzResearch.WordTrace]
  refine ⟨186538550388304682777418341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124359033592203121851612227 186538550388304682777418341)
  ·
    refine ⟨34975978197807128020765939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186538550388304682777418341 34975978197807128020765939)
    ·
      refine ⟨52463967296710692031148909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34975978197807128020765939 52463967296710692031148909)
      ·
        refine ⟨19673987736266509511680841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52463967296710692031148909 19673987736266509511680841)
        ·
          refine ⟨14755490802199882133760631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19673987736266509511680841 14755490802199882133760631)
          ·
            refine ⟨22133236203299823200640947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14755490802199882133760631 22133236203299823200640947)
            ·
              refine ⟨33199854304949734800961421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22133236203299823200640947 33199854304949734800961421)
              ·
                refine ⟨12449945364356150550360533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33199854304949734800961421 12449945364356150550360533)
                ·
                  refine ⟨291795594477097278524075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12449945364356150550360533 291795594477097278524075)
                  ·
                    rfl

theorem cell23_5114429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_5114429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114429 prefixEnd_5114429 := by exact prefixLift 5114429
  have htrace : WordTrace (prefixWord ++ tailWord_5114429) baseStart_5114429 baseEnd_5114429 := by
    simpa [prefixWord, tailWord_5114429, baseEnd_5114429] using wordTrace_append hprefix tailTrace_5114429
  have hstable : (prefixWord ++ tailWord_5114429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114429).length < 2 ^ (prefixWord ++ tailWord_5114429).sum := by decide
  have hdescent : baseEnd_5114429 < baseStart_5114429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114479 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 4]
def baseStart_5114479 : Nat := 118140960795 + 5114479 * 2 ^ 59
def prefixEnd_5114479 : Nat := 4983230072969 + 3 ^ 40 * 5114479 * 2
def baseEnd_5114479 : Nat := 2626186024326600311091445

theorem tailTrace_5114479 : CollatzResearch.WordTrace tailWord_5114479 prefixEnd_5114479 2626186024326600311091445 := by
  unfold tailWord_5114479
  simp only [CollatzResearch.WordTrace]
  refine ⟨186540374038123541316738491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124360249358749027544492327 186540374038123541316738491)
  ·
    refine ⟨279810561057185311975107737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186540374038123541316738491 279810561057185311975107737)
    ·
      refine ⟨209857920792888983981330803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279810561057185311975107737 209857920792888983981330803)
      ·
        refine ⟨314786881189333475971996205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209857920792888983981330803 314786881189333475971996205)
        ·
          refine ⟨118045080446000053489498577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314786881189333475971996205 118045080446000053489498577)
          ·
            refine ⟨88533810334500040117123933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118045080446000053489498577 88533810334500040117123933)
            ·
              refine ⟨33200178875437515043921475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88533810334500040117123933 33200178875437515043921475)
              ·
                refine ⟨49800268313156272565882213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33200178875437515043921475 49800268313156272565882213)
                ·
                  refine ⟨9337550308716801106102915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49800268313156272565882213 9337550308716801106102915)
                  ·
                    refine ⟨14006325463075201659154373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9337550308716801106102915 14006325463075201659154373)
                    ·
                      refine ⟨2626186024326600311091445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14006325463075201659154373 2626186024326600311091445)
                      ·
                        rfl

theorem cell23_5114479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 4].length) (baseStart_5114479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114479 prefixEnd_5114479 := by exact prefixLift 5114479
  have htrace : WordTrace (prefixWord ++ tailWord_5114479) baseStart_5114479 baseEnd_5114479 := by
    simpa [prefixWord, tailWord_5114479, baseEnd_5114479] using wordTrace_append hprefix tailTrace_5114479
  have hstable : (prefixWord ++ tailWord_5114479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114479).length < 2 ^ (prefixWord ++ tailWord_5114479).sum := by decide
  have hdescent : baseEnd_5114479 < baseStart_5114479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114499 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 3]
def baseStart_5114499 : Nat := 118140960795 + 5114499 * 2 ^ 59
def prefixEnd_5114499 : Nat := 4983230072969 + 3 ^ 40 * 5114499 * 2
def baseEnd_5114499 : Nat := 2626196293939690232841353

theorem tailTrace_5114499 : CollatzResearch.WordTrace tailWord_5114499 prefixEnd_5114499 2626196293939690232841353 := by
  unfold tailWord_5114499
  simp only [CollatzResearch.WordTrace]
  refine ⟨186541103498051084732466551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124360735665367389821644367 186541103498051084732466551)
  ·
    refine ⟨279811655247076627098699827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186541103498051084732466551 279811655247076627098699827)
    ·
      refine ⟨419717482870614940648049741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279811655247076627098699827 419717482870614940648049741)
      ·
        refine ⟨157394056076480602743018653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419717482870614940648049741 157394056076480602743018653)
        ·
          refine ⟨59022771028680226028631995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157394056076480602743018653 59022771028680226028631995)
          ·
            refine ⟨88534156543020339042947993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59022771028680226028631995 88534156543020339042947993)
            ·
              refine ⟨66400617407265254282210995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88534156543020339042947993 66400617407265254282210995)
              ·
                refine ⟨99600926110897881423316493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66400617407265254282210995 99600926110897881423316493)
                ·
                  refine ⟨37350347291586705533743685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99600926110897881423316493 37350347291586705533743685)
                  ·
                    refine ⟨7003190117172507287576941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37350347291586705533743685 7003190117172507287576941)
                    ·
                      refine ⟨2626196293939690232841353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7003190117172507287576941 2626196293939690232841353)
                      ·
                        rfl

theorem cell23_5114499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_5114499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114499 prefixEnd_5114499 := by exact prefixLift 5114499
  have htrace : WordTrace (prefixWord ++ tailWord_5114499) baseStart_5114499 baseEnd_5114499 := by
    simpa [prefixWord, tailWord_5114499, baseEnd_5114499] using wordTrace_append hprefix tailTrace_5114499
  have hstable : (prefixWord ++ tailWord_5114499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114499).length < 2 ^ (prefixWord ++ tailWord_5114499).sum := by decide
  have hdescent : baseEnd_5114499 < baseStart_5114499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114526 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_5114526 : Nat := 118140960795 + 5114526 * 2 ^ 59
def prefixEnd_5114526 : Nat := 4983230072969 + 3 ^ 40 * 5114526 * 2
def baseEnd_5114526 : Nat := 2626210157917361627203729

theorem tailTrace_5114526 : CollatzResearch.WordTrace tailWord_5114526 prefixEnd_5114526 2626210157917361627203729 := by
  unfold tailWord_5114526
  simp only [CollatzResearch.WordTrace]
  refine ⟨23317761033619158542962429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124361392179302178895799621 23317761033619158542962429)
  ·
    refine ⟨8744160387607184453610911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23317761033619158542962429 8744160387607184453610911)
    ·
      refine ⟨13116240581410776680416367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8744160387607184453610911 13116240581410776680416367)
      ·
        refine ⟨19674360872116165020624551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13116240581410776680416367 19674360872116165020624551)
        ·
          refine ⟨29511541308174247530936827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19674360872116165020624551 29511541308174247530936827)
          ·
            refine ⟨44267311962261371296405241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29511541308174247530936827 44267311962261371296405241)
            ·
              refine ⟨33200483971696028472303931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44267311962261371296405241 33200483971696028472303931)
              ·
                refine ⟨49800725957544042708455897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33200483971696028472303931 49800725957544042708455897)
                ·
                  refine ⟨37350544468158032031341923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49800725957544042708455897 37350544468158032031341923)
                  ·
                    refine ⟨56025816702237048047012885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37350544468158032031341923 56025816702237048047012885)
                    ·
                      refine ⟨2626210157917361627203729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56025816702237048047012885 2626210157917361627203729)
                      ·
                        rfl

theorem cell23_5114526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_5114526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114526 prefixEnd_5114526 := by exact prefixLift 5114526
  have htrace : WordTrace (prefixWord ++ tailWord_5114526) baseStart_5114526 baseEnd_5114526 := by
    simpa [prefixWord, tailWord_5114526, baseEnd_5114526] using wordTrace_append hprefix tailTrace_5114526
  have hstable : (prefixWord ++ tailWord_5114526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114526).length < 2 ^ (prefixWord ++ tailWord_5114526).sum := by decide
  have hdescent : baseEnd_5114526 < baseStart_5114526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114583 : List Nat := [1, 1, 3, 2, 1, 4, 4, 1, 1, 5]
def baseStart_5114583 : Nat := 118140960795 + 5114583 * 2 ^ 59
def prefixEnd_5114583 : Nat := 4983230072969 + 3 ^ 40 * 5114583 * 2
def baseEnd_5114583 : Nat := 875413142104889301396989

theorem tailTrace_5114583 : CollatzResearch.WordTrace tailWord_5114583 prefixEnd_5114583 875413142104889301396989 := by
  unfold tailWord_5114583
  simp only [CollatzResearch.WordTrace]
  refine ⟨186544167229746767078524403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124362778153164511385682935 186544167229746767078524403)
  ·
    refine ⟨279816250844620150617786605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186544167229746767078524403 279816250844620150617786605)
    ·
      refine ⟨104931094066732556481669977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279816250844620150617786605 104931094066732556481669977)
      ·
        refine ⟨78698320550049417361252483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104931094066732556481669977 78698320550049417361252483)
        ·
          refine ⟨118047480825074126041878725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78698320550049417361252483 118047480825074126041878725)
          ·
            refine ⟨22133902654701398632852261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118047480825074126041878725 22133902654701398632852261)
            ·
              refine ⟨4150106747756512243659799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22133902654701398632852261 4150106747756512243659799)
              ·
                refine ⟨6225160121634768365489699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4150106747756512243659799 6225160121634768365489699)
                ·
                  refine ⟨9337740182452152548234549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6225160121634768365489699 9337740182452152548234549)
                  ·
                    refine ⟨875413142104889301396989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9337740182452152548234549 875413142104889301396989)
                    ·
                      rfl

theorem cell23_5114583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_5114583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114583 prefixEnd_5114583 := by exact prefixLift 5114583
  have htrace : WordTrace (prefixWord ++ tailWord_5114583) baseStart_5114583 baseEnd_5114583 := by
    simpa [prefixWord, tailWord_5114583, baseEnd_5114583] using wordTrace_append hprefix tailTrace_5114583
  have hstable : (prefixWord ++ tailWord_5114583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114583).length < 2 ^ (prefixWord ++ tailWord_5114583).sum := by decide
  have hdescent : baseEnd_5114583 < baseStart_5114583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114606 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_5114606 : Nat := 118140960795 + 5114606 * 2 ^ 59
def prefixEnd_5114606 : Nat := 4983230072969 + 3 ^ 40 * 5114606 * 2
def baseEnd_5114606 : Nat := 2626251236369721314203361

theorem tailTrace_5114606 : CollatzResearch.WordTrace tailWord_5114606 prefixEnd_5114606 2626251236369721314203361 := by
  unfold tailWord_5114606
  simp only [CollatzResearch.WordTrace]
  refine ⟨23318125763582930250826459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124363337405775628004407781 23318125763582930250826459)
  ·
    refine ⟨34977188645374395376239689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23318125763582930250826459 34977188645374395376239689)
    ·
      refine ⟨26232891484030796532179767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34977188645374395376239689 26232891484030796532179767)
      ·
        refine ⟨39349337226046194798269651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26232891484030796532179767 39349337226046194798269651)
        ·
          refine ⟨59024005839069292197404477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39349337226046194798269651 59024005839069292197404477)
          ·
            refine ⟨22134002189650984574026679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59024005839069292197404477 22134002189650984574026679)
            ·
              refine ⟨33201003284476476861040019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22134002189650984574026679 33201003284476476861040019)
              ·
                refine ⟨49801504926714715291560029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33201003284476476861040019 49801504926714715291560029)
                ·
                  refine ⟨18675564347518018234335011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49801504926714715291560029 18675564347518018234335011)
                  ·
                    refine ⟨28013346521277027351502517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18675564347518018234335011 28013346521277027351502517)
                    ·
                      refine ⟨2626251236369721314203361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28013346521277027351502517 2626251236369721314203361)
                      ·
                        rfl

theorem cell23_5114606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_5114606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114606 prefixEnd_5114606 := by exact prefixLift 5114606
  have htrace : WordTrace (prefixWord ++ tailWord_5114606) baseStart_5114606 baseEnd_5114606 := by
    simpa [prefixWord, tailWord_5114606, baseEnd_5114606] using wordTrace_append hprefix tailTrace_5114606
  have hstable : (prefixWord ++ tailWord_5114606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114606).length < 2 ^ (prefixWord ++ tailWord_5114606).sum := by decide
  have hdescent : baseEnd_5114606 < baseStart_5114606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114609 : List Nat := [1, 2, 2, 2, 2, 2, 2, 10]
def baseStart_5114609 : Nat := 118140960795 + 5114609 * 2 ^ 59
def prefixEnd_5114609 : Nat := 4983230072969 + 3 ^ 40 * 5114609 * 2
def baseEnd_5114609 : Nat := 97268621363395733424661

theorem tailTrace_5114609 : CollatzResearch.WordTrace tailWord_5114609 prefixEnd_5114609 97268621363395733424661 := by
  unfold tailWord_5114609
  simp only [CollatzResearch.WordTrace]
  refine ⟨186545115527652573518970881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124363410351768382345980587 186545115527652573518970881)
  ·
    refine ⟨139908836645739430139228161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186545115527652573518970881 139908836645739430139228161)
    ·
      refine ⟨104931627484304572604421121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139908836645739430139228161 104931627484304572604421121)
      ·
        refine ⟨78698720613228429453315841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104931627484304572604421121 78698720613228429453315841)
        ·
          refine ⟨59024040459921322089986881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78698720613228429453315841 59024040459921322089986881)
          ·
            refine ⟨44268030344940991567490161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59024040459921322089986881 44268030344940991567490161)
            ·
              refine ⟨33201022758705743675617621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44268030344940991567490161 33201022758705743675617621)
              ·
                refine ⟨97268621363395733424661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33201022758705743675617621 97268621363395733424661)
                ·
                  rfl

theorem cell23_5114609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 10].length) (baseStart_5114609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114609 prefixEnd_5114609 := by exact prefixLift 5114609
  have htrace : WordTrace (prefixWord ++ tailWord_5114609) baseStart_5114609 baseEnd_5114609 := by
    simpa [prefixWord, tailWord_5114609, baseEnd_5114609] using wordTrace_append hprefix tailTrace_5114609
  have hstable : (prefixWord ++ tailWord_5114609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114609).length < 2 ^ (prefixWord ++ tailWord_5114609).sum := by decide
  have hdescent : baseEnd_5114609 < baseStart_5114609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114620 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 3, 2, 2]
def baseStart_5114620 : Nat := 118140960795 + 5114620 * 2 ^ 59
def prefixEnd_5114620 : Nat := 4983230072969 + 3 ^ 40 * 5114620 * 2
def baseEnd_5114620 : Nat := 2626258425098884259428297

theorem tailTrace_5114620 : CollatzResearch.WordTrace tailWord_5114620 prefixEnd_5114620 2626258425098884259428297 := by
  unfold tailWord_5114620
  simp only [CollatzResearch.WordTrace]
  refine ⟨93272758365306361198810657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124363677820408481598414209 93272758365306361198810657)
  ·
    refine ⟨69954568773979770899107993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93272758365306361198810657 69954568773979770899107993)
    ·
      refine ⟨52465926580484828174330995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69954568773979770899107993 52465926580484828174330995)
      ·
        refine ⟨78698889870727242261496493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52465926580484828174330995 78698889870727242261496493)
        ·
          refine ⟨29512083701522715848061185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78698889870727242261496493 29512083701522715848061185)
          ·
            refine ⟨22134062776142036886045889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29512083701522715848061185 22134062776142036886045889)
            ·
              refine ⟨16600547082106527664534417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22134062776142036886045889 16600547082106527664534417)
              ·
                refine ⟨12450410311579895748400813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16600547082106527664534417 12450410311579895748400813)
                ·
                  refine ⟨4668903866842460905650305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12450410311579895748400813 4668903866842460905650305)
                  ·
                    refine ⟨3501677900131845679237729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4668903866842460905650305 3501677900131845679237729)
                    ·
                      refine ⟨2626258425098884259428297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3501677900131845679237729 2626258425098884259428297)
                      ·
                        rfl

theorem cell23_5114620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_5114620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114620 prefixEnd_5114620 := by exact prefixLift 5114620
  have htrace : WordTrace (prefixWord ++ tailWord_5114620) baseStart_5114620 baseEnd_5114620 := by
    simpa [prefixWord, tailWord_5114620, baseEnd_5114620] using wordTrace_append hprefix tailTrace_5114620
  have hstable : (prefixWord ++ tailWord_5114620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114620).length < 2 ^ (prefixWord ++ tailWord_5114620).sum := by decide
  have hdescent : baseEnd_5114620 < baseStart_5114620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114629 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_5114629 : Nat := 118140960795 + 5114629 * 2 ^ 59
def prefixEnd_5114629 : Nat := 4983230072969 + 3 ^ 40 * 5114629 * 2
def baseEnd_5114629 : Nat := 2626263046424774724215755

theorem tailTrace_5114629 : CollatzResearch.WordTrace tailWord_5114629 prefixEnd_5114629 2626263046424774724215755 := by
  unfold tailWord_5114629
  simp only [CollatzResearch.WordTrace]
  refine ⟨186545844987580116934698941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124363896658386744623132627 186545844987580116934698941)
  ·
    refine ⟨69954691870342543850512103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186545844987580116934698941 69954691870342543850512103)
    ·
      refine ⟨104932037805513815775768155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69954691870342543850512103 104932037805513815775768155)
      ·
        refine ⟨157398056708270723663652233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104932037805513815775768155 157398056708270723663652233)
        ·
          refine ⟨118048542531203042747739175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157398056708270723663652233 118048542531203042747739175)
          ·
            refine ⟨177072813796804564121608763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118048542531203042747739175 177072813796804564121608763)
            ·
              refine ⟨265609220695206846182413145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177072813796804564121608763 265609220695206846182413145)
              ·
                refine ⟨199206915521405134636809859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265609220695206846182413145 199206915521405134636809859)
                ·
                  refine ⟨298810373282107701955214789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 199206915521405134636809859 298810373282107701955214789)
                  ·
                    refine ⟨56026944990395194116602773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 298810373282107701955214789 56026944990395194116602773)
                    ·
                      refine ⟨2626263046424774724215755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56026944990395194116602773 2626263046424774724215755)
                      ·
                        rfl

theorem cell23_5114629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_5114629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114629 prefixEnd_5114629 := by exact prefixLift 5114629
  have htrace : WordTrace (prefixWord ++ tailWord_5114629) baseStart_5114629 baseEnd_5114629 := by
    simpa [prefixWord, tailWord_5114629, baseEnd_5114629] using wordTrace_append hprefix tailTrace_5114629
  have hstable : (prefixWord ++ tailWord_5114629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114629).length < 2 ^ (prefixWord ++ tailWord_5114629).sum := by decide
  have hdescent : baseEnd_5114629 < baseStart_5114629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114636 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 3, 3, 3]
def baseStart_5114636 : Nat := 118140960795 + 5114636 * 2 ^ 59
def prefixEnd_5114636 : Nat := 4983230072969 + 3 ^ 40 * 5114636 * 2
def baseEnd_5114636 : Nat := 2626266640789356196828223

theorem tailTrace_5114636 : CollatzResearch.WordTrace tailWord_5114636 prefixEnd_5114636 2626266640789356196828223 := by
  unfold tailWord_5114636
  simp only [CollatzResearch.WordTrace]
  refine ⟨93273050149277378565101881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124364066865703171420135841 93273050149277378565101881)
  ·
    refine ⟨69954787611958033923826411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93273050149277378565101881 69954787611958033923826411)
    ·
      refine ⟨104932181417937050885739617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69954787611958033923826411 104932181417937050885739617)
      ·
        refine ⟨78699136063452788164304713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104932181417937050885739617 78699136063452788164304713)
        ·
          refine ⟨59024352047589591123228535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78699136063452788164304713 59024352047589591123228535)
          ·
            refine ⟨88536528071384386684842803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59024352047589591123228535 88536528071384386684842803)
            ·
              refine ⟨132804792107076580027264205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88536528071384386684842803 132804792107076580027264205)
              ·
                refine ⟨49801797040153717510224077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132804792107076580027264205 49801797040153717510224077)
                ·
                  refine ⟨18675673890057644066334029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49801797040153717510224077 18675673890057644066334029)
                  ·
                    refine ⟨7003377708771616524875261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18675673890057644066334029 7003377708771616524875261)
                    ·
                      refine ⟨2626266640789356196828223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7003377708771616524875261 2626266640789356196828223)
                      ·
                        rfl

theorem cell23_5114636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_5114636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114636 prefixEnd_5114636 := by exact prefixLift 5114636
  have htrace : WordTrace (prefixWord ++ tailWord_5114636) baseStart_5114636 baseEnd_5114636 := by
    simpa [prefixWord, tailWord_5114636, baseEnd_5114636] using wordTrace_append hprefix tailTrace_5114636
  have hstable : (prefixWord ++ tailWord_5114636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114636).length < 2 ^ (prefixWord ++ tailWord_5114636).sum := by decide
  have hdescent : baseEnd_5114636 < baseStart_5114636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114696 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_5114696 : Nat := 118140960795 + 5114696 * 2 ^ 59
def prefixEnd_5114696 : Nat := 4983230072969 + 3 ^ 40 * 5114696 * 2
def baseEnd_5114696 : Nat := 2626297449628625962077947

theorem tailTrace_5114696 : CollatzResearch.WordTrace tailWord_5114696 prefixEnd_5114696 2626297449628625962077947 := by
  unfold tailWord_5114696
  simp only [CollatzResearch.WordTrace]
  refine ⟨93274144339168693688693971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124365525785558258251591961 93274144339168693688693971)
  ·
    refine ⟨139911216508753040533040957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93274144339168693688693971 139911216508753040533040957)
    ·
      refine ⟨52466706190782390199890359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139911216508753040533040957 52466706190782390199890359)
      ·
        refine ⟨78700059286173585299835539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52466706190782390199890359 78700059286173585299835539)
        ·
          refine ⟨118050088929260377949753309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78700059286173585299835539 118050088929260377949753309)
          ·
            refine ⟨44268783348472641731157491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118050088929260377949753309 44268783348472641731157491)
            ·
              refine ⟨66403175022708962596736237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44268783348472641731157491 66403175022708962596736237)
              ·
                refine ⟨24901190633515860973776089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66403175022708962596736237 24901190633515860973776089)
                ·
                  refine ⟨18675892975136895730332067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24901190633515860973776089 18675892975136895730332067)
                  ·
                    refine ⟨28013839462705343595498101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18675892975136895730332067 28013839462705343595498101)
                    ·
                      refine ⟨2626297449628625962077947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28013839462705343595498101 2626297449628625962077947)
                      ·
                        rfl

theorem cell23_5114696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_5114696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114696 prefixEnd_5114696 := by exact prefixLift 5114696
  have htrace : WordTrace (prefixWord ++ tailWord_5114696) baseStart_5114696 baseEnd_5114696 := by
    simpa [prefixWord, tailWord_5114696, baseEnd_5114696] using wordTrace_append hprefix tailTrace_5114696
  have hstable : (prefixWord ++ tailWord_5114696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114696).length < 2 ^ (prefixWord ++ tailWord_5114696).sum := by decide
  have hdescent : baseEnd_5114696 < baseStart_5114696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114697 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 1, 3, 2]
def baseStart_5114697 : Nat := 118140960795 + 5114697 * 2 ^ 59
def prefixEnd_5114697 : Nat := 4983230072969 + 3 ^ 40 * 5114697 * 2
def baseEnd_5114697 : Nat := 2626297963109280458165443

theorem tailTrace_5114697 : CollatzResearch.WordTrace tailWord_5114697 prefixEnd_5114697 2626297963109280458165443 := by
  unfold tailWord_5114697
  simp only [CollatzResearch.WordTrace]
  refine ⟨186548325151333764548174345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124365550100889176365449563 186548325151333764548174345)
  ·
    refine ⟨139911243863500323411130759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186548325151333764548174345 139911243863500323411130759)
    ·
      refine ⟨209866865795250485116696139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139911243863500323411130759 209866865795250485116696139)
      ·
        refine ⟨314800298692875727675044209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209866865795250485116696139 314800298692875727675044209)
        ·
          refine ⟨236100224019656795756283157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314800298692875727675044209 236100224019656795756283157)
          ·
            refine ⟨11067198000921412301075773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 236100224019656795756283157 11067198000921412301075773)
            ·
              refine ⟨4150199250345529612903415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11067198000921412301075773 4150199250345529612903415)
              ·
                refine ⟨6225298875518294419355123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4150199250345529612903415 6225298875518294419355123)
                ·
                  refine ⟨9337948313277441629032685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6225298875518294419355123 9337948313277441629032685)
                  ·
                    refine ⟨3501730617479040610887257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9337948313277441629032685 3501730617479040610887257)
                    ·
                      refine ⟨2626297963109280458165443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3501730617479040610887257 2626297963109280458165443)
                      ·
                        rfl

theorem cell23_5114697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 3, 2].length) (baseStart_5114697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114697 prefixEnd_5114697 := by exact prefixLift 5114697
  have htrace : WordTrace (prefixWord ++ tailWord_5114697) baseStart_5114697 baseEnd_5114697 := by
    simpa [prefixWord, tailWord_5114697, baseEnd_5114697] using wordTrace_append hprefix tailTrace_5114697
  have hstable : (prefixWord ++ tailWord_5114697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114697).length < 2 ^ (prefixWord ++ tailWord_5114697).sum := by decide
  have hdescent : baseEnd_5114697 < baseStart_5114697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114723 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 4]
def baseStart_5114723 : Nat := 118140960795 + 5114723 * 2 ^ 59
def prefixEnd_5114723 : Nat := 4983230072969 + 3 ^ 40 * 5114723 * 2
def baseEnd_5114723 : Nat := 2626311313606297356440323

theorem tailTrace_5114723 : CollatzResearch.WordTrace tailWord_5114723 prefixEnd_5114723 2626311313606297356440323 := by
  unfold tailWord_5114723
  simp only [CollatzResearch.WordTrace]
  refine ⟨186549273449239570988620823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124366182299493047325747215 186549273449239570988620823)
  ·
    refine ⟨279823910173859356482931235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186549273449239570988620823 279823910173859356482931235)
    ·
      refine ⟨419735865260789034724396853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279823910173859356482931235 419735865260789034724396853)
      ·
        refine ⟨39350237368198972005412205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 419735865260789034724396853 39350237368198972005412205)
        ·
          refine ⟨14756339013074614502029577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39350237368198972005412205 14756339013074614502029577)
          ·
            refine ⟨11067254259805960876522183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14756339013074614502029577 11067254259805960876522183)
            ·
              refine ⟨16600881389708941314783275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11067254259805960876522183 16600881389708941314783275)
              ·
                refine ⟨24901322084563411972174913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16600881389708941314783275 24901322084563411972174913)
                ·
                  refine ⟨18675991563422558979131185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24901322084563411972174913 18675991563422558979131185)
                  ·
                    refine ⟨14006993672566919234348389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18675991563422558979131185 14006993672566919234348389)
                    ·
                      refine ⟨2626311313606297356440323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14006993672566919234348389 2626311313606297356440323)
                      ·
                        rfl

theorem cell23_5114723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_5114723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114723 prefixEnd_5114723 := by exact prefixLift 5114723
  have htrace : WordTrace (prefixWord ++ tailWord_5114723) baseStart_5114723 baseEnd_5114723 := by
    simpa [prefixWord, tailWord_5114723, baseEnd_5114723] using wordTrace_append hprefix tailTrace_5114723
  have hstable : (prefixWord ++ tailWord_5114723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114723).length < 2 ^ (prefixWord ++ tailWord_5114723).sum := by decide
  have hdescent : baseEnd_5114723 < baseStart_5114723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114727 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 2, 2, 2]
def baseStart_5114727 : Nat := 118140960795 + 5114727 * 2 ^ 59
def prefixEnd_5114727 : Nat := 4983230072969 + 3 ^ 40 * 5114727 * 2
def baseEnd_5114727 : Nat := 2626313367528915340790305

theorem tailTrace_5114727 : CollatzResearch.WordTrace tailWord_5114727 prefixEnd_5114727 2626313367528915340790305 := by
  unfold tailWord_5114727
  simp only [CollatzResearch.WordTrace]
  refine ⟨186549419341225079671766435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124366279560816719781177623 186549419341225079671766435)
  ·
    refine ⟨279824129011837619507649653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186549419341225079671766435 279824129011837619507649653)
    ·
      refine ⟨26233512094859776828842155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 279824129011837619507649653 26233512094859776828842155)
      ·
        refine ⟨39350268142289665243263233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26233512094859776828842155 39350268142289665243263233)
        ·
          refine ⟨29512701106717248932447425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39350268142289665243263233 29512701106717248932447425)
          ·
            refine ⟨22134525830037936699335569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29512701106717248932447425 22134525830037936699335569)
            ·
              refine ⟨16600894372528452524501677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22134525830037936699335569 16600894372528452524501677)
              ·
                refine ⟨6225335389698169696688129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16600894372528452524501677 6225335389698169696688129)
                ·
                  refine ⟨4669001542273627272516097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6225335389698169696688129 4669001542273627272516097)
                  ·
                    refine ⟨3501751156705220454387073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4669001542273627272516097 3501751156705220454387073)
                    ·
                      refine ⟨2626313367528915340790305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3501751156705220454387073 2626313367528915340790305)
                      ·
                        rfl

theorem cell23_5114727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_5114727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114727 prefixEnd_5114727 := by exact prefixLift 5114727
  have htrace : WordTrace (prefixWord ++ tailWord_5114727) baseStart_5114727 baseEnd_5114727 := by
    simpa [prefixWord, tailWord_5114727, baseEnd_5114727] using wordTrace_append hprefix tailTrace_5114727
  have hstable : (prefixWord ++ tailWord_5114727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114727).length < 2 ^ (prefixWord ++ tailWord_5114727).sum := by decide
  have hdescent : baseEnd_5114727 < baseStart_5114727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114783 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5114783 : Nat := 118140960795 + 5114783 * 2 ^ 59
def prefixEnd_5114783 : Nat := 4983230072969 + 3 ^ 40 * 5114783 * 2
def baseEnd_5114783 : Nat := 2626342122445567121690047

theorem tailTrace_5114783 : CollatzResearch.WordTrace tailWord_5114783 prefixEnd_5114783 2626342122445567121690047 := by
  unfold tailWord_5114783
  simp only [CollatzResearch.WordTrace]
  refine ⟨186551461829022201235805003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124367641219348134157203335 186551461829022201235805003)
  ·
    refine ⟨279827192743533301853707505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186551461829022201235805003 279827192743533301853707505)
    ·
      refine ⟨209870394557649976390280629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279827192743533301853707505 209870394557649976390280629)
      ·
        refine ⟨19675349489779685286588809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 209870394557649976390280629 19675349489779685286588809)
        ·
          refine ⟨14756512117334763964941607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19675349489779685286588809 14756512117334763964941607)
          ·
            refine ⟨22134768176002145947412411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14756512117334763964941607 22134768176002145947412411)
            ·
              refine ⟨33202152264003218921118617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22134768176002145947412411 33202152264003218921118617)
              ·
                refine ⟨24901614198002414190838963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33202152264003218921118617 24901614198002414190838963)
                ·
                  refine ⟨37352421297003621286258445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24901614198002414190838963 37352421297003621286258445)
                  ·
                    refine ⟨14007157986376357982346917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37352421297003621286258445 14007157986376357982346917)
                    ·
                      refine ⟨2626342122445567121690047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14007157986376357982346917 2626342122445567121690047)
                      ·
                        rfl

theorem cell23_5114783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5114783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114783 prefixEnd_5114783 := by exact prefixLift 5114783
  have htrace : WordTrace (prefixWord ++ tailWord_5114783) baseStart_5114783 baseEnd_5114783 := by
    simpa [prefixWord, tailWord_5114783, baseEnd_5114783] using wordTrace_append hprefix tailTrace_5114783
  have hstable : (prefixWord ++ tailWord_5114783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114783).length < 2 ^ (prefixWord ++ tailWord_5114783).sum := by decide
  have hdescent : baseEnd_5114783 < baseStart_5114783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114793 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 3, 4]
def baseStart_5114793 : Nat := 118140960795 + 5114793 * 2 ^ 59
def prefixEnd_5114793 : Nat := 4983230072969 + 3 ^ 40 * 5114793 * 2
def baseEnd_5114793 : Nat := 875449085750704027521667

theorem tailTrace_5114793 : CollatzResearch.WordTrace tailWord_5114793 prefixEnd_5114793 875449085750704027521667 := by
  unfold tailWord_5114793
  simp only [CollatzResearch.WordTrace]
  refine ⟨186551826558985972943669033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124367884372657315295779355 186551826558985972943669033)
  ·
    refine ⟨139913869919239479707751775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186551826558985972943669033 139913869919239479707751775)
    ·
      refine ⟨209870804878859219561627663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139913869919239479707751775 209870804878859219561627663)
      ·
        refine ⟨314806207318288829342441495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209870804878859219561627663 314806207318288829342441495)
        ·
          refine ⟨472209310977433244013662243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314806207318288829342441495 472209310977433244013662243)
          ·
            refine ⟨708313966466149866020493365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472209310977433244013662243 708313966466149866020493365)
            ·
              refine ⟨66404434356201549939421253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 708313966466149866020493365 66404434356201549939421253)
              ·
                refine ⟨12450831441787790613641485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66404434356201549939421253 12450831441787790613641485)
                ·
                  refine ⟨4669061790670421480115557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12450831441787790613641485 4669061790670421480115557)
                  ·
                    refine ⟨875449085750704027521667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4669061790670421480115557 875449085750704027521667)
                    ·
                      rfl

theorem cell23_5114793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 4].length) (baseStart_5114793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114793 prefixEnd_5114793 := by exact prefixLift 5114793
  have htrace : WordTrace (prefixWord ++ tailWord_5114793) baseStart_5114793 baseEnd_5114793 := by
    simpa [prefixWord, tailWord_5114793, baseEnd_5114793] using wordTrace_append hprefix tailTrace_5114793
  have hstable : (prefixWord ++ tailWord_5114793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114793).length < 2 ^ (prefixWord ++ tailWord_5114793).sum := by decide
  have hdescent : baseEnd_5114793 < baseStart_5114793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114796 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_5114796 : Nat := 118140960795 + 5114796 * 2 ^ 59
def prefixEnd_5114796 : Nat := 4983230072969 + 3 ^ 40 * 5114796 * 2
def baseEnd_5114796 : Nat := 2626348797694075570827487

theorem tailTrace_5114796 : CollatzResearch.WordTrace tailWord_5114796 prefixEnd_5114796 2626348797694075570827487 := by
  unfold tailWord_5114796
  simp only [CollatzResearch.WordTrace]
  refine ⟨93275967988987552228014121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124367957318650069637352161 93275967988987552228014121)
  ·
    refine ⟨69956975991740664171010591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93275967988987552228014121 69956975991740664171010591)
    ·
      refine ⟨104935463987610996256515887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69956975991740664171010591 104935463987610996256515887)
      ·
        refine ⟨157403195981416494384773831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104935463987610996256515887 157403195981416494384773831)
        ·
          refine ⟨236104793972124741577160747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157403195981416494384773831 236104793972124741577160747)
          ·
            refine ⟨354157190958187112365741121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236104793972124741577160747 354157190958187112365741121)
            ·
              refine ⟨265617893218640334274305841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354157190958187112365741121 265617893218640334274305841)
              ·
                refine ⟨199213419913980250705729381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265617893218640334274305841 199213419913980250705729381)
                ·
                  refine ⟨37352516233871297007324259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199213419913980250705729381 37352516233871297007324259)
                  ·
                    refine ⟨56028774350806945510986389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37352516233871297007324259 56028774350806945510986389)
                    ·
                      refine ⟨2626348797694075570827487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56028774350806945510986389 2626348797694075570827487)
                      ·
                        rfl

theorem cell23_5114796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_5114796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114796 prefixEnd_5114796 := by exact prefixLift 5114796
  have htrace : WordTrace (prefixWord ++ tailWord_5114796) baseStart_5114796 baseEnd_5114796 := by
    simpa [prefixWord, tailWord_5114796, baseEnd_5114796] using wordTrace_append hprefix tailTrace_5114796
  have hstable : (prefixWord ++ tailWord_5114796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114796).length < 2 ^ (prefixWord ++ tailWord_5114796).sum := by decide
  have hdescent : baseEnd_5114796 < baseStart_5114796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114840 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 6]
def baseStart_5114840 : Nat := 118140960795 + 5114840 * 2 ^ 59
def prefixEnd_5114840 : Nat := 4983230072969 + 3 ^ 40 * 5114840 * 2
def baseEnd_5114840 : Nat := 291819043426985933186365

theorem tailTrace_5114840 : CollatzResearch.WordTrace tailWord_5114840 prefixEnd_5114840 291819043426985933186365 := by
  unfold tailWord_5114840
  simp only [CollatzResearch.WordTrace]
  refine ⟨93276770394907849985314987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124369027193210466647086649 93276770394907849985314987)
  ·
    refine ⟨139915155592361774977972481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93276770394907849985314987 139915155592361774977972481)
    ·
      refine ⟨104936366694271331233479361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139915155592361774977972481 104936366694271331233479361)
      ·
        refine ⟨78702275020703498425109521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104936366694271331233479361 78702275020703498425109521)
        ·
          refine ⟨59026706265527623818832141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78702275020703498425109521 59026706265527623818832141)
          ·
            refine ⟨22135014849572858932062053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59026706265527623818832141 22135014849572858932062053)
            ·
              refine ⟨4150315284294911049761635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22135014849572858932062053 4150315284294911049761635)
              ·
                refine ⟨6225472926442366574642453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4150315284294911049761635 6225472926442366574642453)
                ·
                  refine ⟨291819043426985933186365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6225472926442366574642453 291819043426985933186365)
                  ·
                    rfl

theorem cell23_5114840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 6].length) (baseStart_5114840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114840 prefixEnd_5114840 := by exact prefixLift 5114840
  have htrace : WordTrace (prefixWord ++ tailWord_5114840) baseStart_5114840 baseEnd_5114840 := by
    simpa [prefixWord, tailWord_5114840, baseEnd_5114840] using wordTrace_append hprefix tailTrace_5114840
  have hstable : (prefixWord ++ tailWord_5114840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114840).length < 2 ^ (prefixWord ++ tailWord_5114840).sum := by decide
  have hdescent : baseEnd_5114840 < baseStart_5114840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114878 : List Nat := [4, 2, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_5114878 : Nat := 118140960795 + 5114878 * 2 ^ 59
def prefixEnd_5114878 : Nat := 4983230072969 + 3 ^ 40 * 5114878 * 2
def baseEnd_5114878 : Nat := 875463634369248083334037

theorem tailTrace_5114878 : CollatzResearch.WordTrace tailWord_5114878 prefixEnd_5114878 875463634369248083334037 := by
  unfold tailWord_5114878
  simp only [CollatzResearch.WordTrace]
  refine ⟨23319365845459754057564161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124369951175785354973675525 23319365845459754057564161)
  ·
    refine ⟨17489524384094815543173121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23319365845459754057564161 17489524384094815543173121)
    ·
      refine ⟨13117143288071111657379841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17489524384094815543173121 13117143288071111657379841)
      ·
        refine ⟨9837857466053333743034881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13117143288071111657379841 9837857466053333743034881)
        ·
          refine ⟨7378393099540000307276161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9837857466053333743034881 7378393099540000307276161)
          ·
            refine ⟨5533794824655000230457121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7378393099540000307276161 5533794824655000230457121)
            ·
              refine ⟨4150346118491250172842841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5533794824655000230457121 4150346118491250172842841)
              ·
                refine ⟨3112759588868437629632131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4150346118491250172842841 3112759588868437629632131)
                ·
                  refine ⟨4669139383302656444448197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3112759588868437629632131 4669139383302656444448197)
                  ·
                    refine ⟨875463634369248083334037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4669139383302656444448197 875463634369248083334037)
                    ·
                      rfl

theorem cell23_5114878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_5114878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114878 prefixEnd_5114878 := by exact prefixLift 5114878
  have htrace : WordTrace (prefixWord ++ tailWord_5114878) baseStart_5114878 baseEnd_5114878 := by
    simpa [prefixWord, tailWord_5114878, baseEnd_5114878] using wordTrace_append hprefix tailTrace_5114878
  have hstable : (prefixWord ++ tailWord_5114878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114878).length < 2 ^ (prefixWord ++ tailWord_5114878).sum := by decide
  have hdescent : baseEnd_5114878 < baseStart_5114878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114890 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_5114890 : Nat := 118140960795 + 5114890 * 2 ^ 59
def prefixEnd_5114890 : Nat := 4983230072969 + 3 ^ 40 * 5114890 * 2
def baseEnd_5114890 : Nat := 2626397064875598203052055

theorem tailTrace_5114890 : CollatzResearch.WordTrace tailWord_5114890 prefixEnd_5114890 2626397064875598203052055 := by
  unfold tailWord_5114890
  simp only [CollatzResearch.WordTrace]
  refine ⟨46638841109908639627487531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124370242959756372339966749 46638841109908639627487531)
  ·
    refine ⟨69958261664862959441231297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46638841109908639627487531 69958261664862959441231297)
    ·
      refine ⟨52468696248647219580923473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69958261664862959441231297 52468696248647219580923473)
      ·
        refine ⟨39351522186485414685692605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52468696248647219580923473 39351522186485414685692605)
        ·
          refine ⟨14756820819932030507134727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39351522186485414685692605 14756820819932030507134727)
          ·
            refine ⟨22135231229898045760702091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14756820819932030507134727 22135231229898045760702091)
            ·
              refine ⟨33202846844847068641053137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22135231229898045760702091 33202846844847068641053137)
              ·
                refine ⟨24902135133635301480789853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33202846844847068641053137 24902135133635301480789853)
                ·
                  refine ⟨9338300675113238055296195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24902135133635301480789853 9338300675113238055296195)
                  ·
                    refine ⟨14007451012669857082944293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9338300675113238055296195 14007451012669857082944293)
                    ·
                      refine ⟨2626397064875598203052055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14007451012669857082944293 2626397064875598203052055)
                      ·
                        rfl

theorem cell23_5114890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_5114890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114890 prefixEnd_5114890 := by exact prefixLift 5114890
  have htrace : WordTrace (prefixWord ++ tailWord_5114890) baseStart_5114890 baseEnd_5114890 := by
    simpa [prefixWord, tailWord_5114890, baseEnd_5114890] using wordTrace_append hprefix tailTrace_5114890
  have hstable : (prefixWord ++ tailWord_5114890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114890).length < 2 ^ (prefixWord ++ tailWord_5114890).sum := by decide
  have hdescent : baseEnd_5114890 < baseStart_5114890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114933 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_5114933 : Nat := 118140960795 + 5114933 * 2 ^ 59
def prefixEnd_5114933 : Nat := 4983230072969 + 3 ^ 40 * 5114933 * 2
def baseEnd_5114933 : Nat := 2626419144543741534814357

theorem tailTrace_5114933 : CollatzResearch.WordTrace tailWord_5114933 prefixEnd_5114933 2626419144543741534814357 := by
  unfold tailWord_5114933
  simp only [CollatzResearch.WordTrace]
  refine ⟨186556932778478776853765453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124371288518985851235843635 186556932778478776853765453)
  ·
    refine ⟨69958849791929541320162045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186556932778478776853765453 69958849791929541320162045)
    ·
      refine ⟨26234568671973577995060767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69958849791929541320162045 26234568671973577995060767)
      ·
        refine ⟨39351853007960366992591151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26234568671973577995060767 39351853007960366992591151)
        ·
          refine ⟨59027779511940550488886727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39351853007960366992591151 59027779511940550488886727)
          ·
            refine ⟨88541669267910825733330091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59027779511940550488886727 88541669267910825733330091)
            ·
              refine ⟨132812503901866238599995137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88541669267910825733330091 132812503901866238599995137)
              ·
                refine ⟨99609377926399678949996353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132812503901866238599995137 99609377926399678949996353)
                ·
                  refine ⟨74707033444799759212497265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99609377926399678949996353 74707033444799759212497265)
                  ·
                    refine ⟨56030275083599819409372949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74707033444799759212497265 56030275083599819409372949)
                    ·
                      refine ⟨2626419144543741534814357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56030275083599819409372949 2626419144543741534814357)
                      ·
                        rfl

theorem cell23_5114933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_5114933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114933 prefixEnd_5114933 := by exact prefixLift 5114933
  have htrace : WordTrace (prefixWord ++ tailWord_5114933) baseStart_5114933 baseEnd_5114933 := by
    simpa [prefixWord, tailWord_5114933, baseEnd_5114933] using wordTrace_append hprefix tailTrace_5114933
  have hstable : (prefixWord ++ tailWord_5114933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114933).length < 2 ^ (prefixWord ++ tailWord_5114933).sum := by decide
  have hdescent : baseEnd_5114933 < baseStart_5114933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114934 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_5114934 : Nat := 118140960795 + 5114934 * 2 ^ 59
def prefixEnd_5114934 : Nat := 4983230072969 + 3 ^ 40 * 5114934 * 2
def baseEnd_5114934 : Nat := 875473219341465343633951

theorem tailTrace_5114934 : CollatzResearch.WordTrace tailWord_5114934 prefixEnd_5114934 875473219341465343633951 := by
  unfold tailWord_5114934
  simp only [CollatzResearch.WordTrace]
  refine ⟨11659810578217197126534491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124371312834316769349701237 11659810578217197126534491)
  ·
    refine ⟨17489715867325795689801737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11659810578217197126534491 17489715867325795689801737)
    ·
      refine ⟨13117286900494346767351303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17489715867325795689801737 13117286900494346767351303)
      ·
        refine ⟨19675930350741520151026955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13117286900494346767351303 19675930350741520151026955)
        ·
          refine ⟨29513895526112280226540433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19675930350741520151026955 29513895526112280226540433)
          ·
            refine ⟨22135421644584210169905325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29513895526112280226540433 22135421644584210169905325)
            ·
              refine ⟨8300783116719078813714497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22135421644584210169905325 8300783116719078813714497)
              ·
                refine ⟨6225587337539309110285873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8300783116719078813714497 6225587337539309110285873)
                ·
                  refine ⟨4669190503154481832714405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6225587337539309110285873 4669190503154481832714405)
                  ·
                    refine ⟨875473219341465343633951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4669190503154481832714405 875473219341465343633951)
                    ·
                      rfl

theorem cell23_5114934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_5114934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114934 prefixEnd_5114934 := by exact prefixLift 5114934
  have htrace : WordTrace (prefixWord ++ tailWord_5114934) baseStart_5114934 baseEnd_5114934 := by
    simpa [prefixWord, tailWord_5114934, baseEnd_5114934] using wordTrace_append hprefix tailTrace_5114934
  have hstable : (prefixWord ++ tailWord_5114934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114934).length < 2 ^ (prefixWord ++ tailWord_5114934).sum := by decide
  have hdescent : baseEnd_5114934 < baseStart_5114934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114941 : List Nat := [1, 4, 1, 3, 1, 2, 2, 4, 1, 2, 2]
def baseStart_5114941 : Nat := 118140960795 + 5114941 * 2 ^ 59
def prefixEnd_5114941 : Nat := 4983230072969 + 3 ^ 40 * 5114941 * 2
def baseEnd_5114941 : Nat := 2626423252388977503514321

theorem tailTrace_5114941 : CollatzResearch.WordTrace tailWord_5114941 prefixEnd_5114941 2626423252388977503514321 := by
  unfold tailWord_5114941
  simp only [CollatzResearch.WordTrace]
  refine ⟨186557224562449794220056677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124371483041633196146704451 186557224562449794220056677)
  ·
    refine ⟨34979479605459336416260627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186557224562449794220056677 34979479605459336416260627)
    ·
      refine ⟨52469219408189004624390941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34979479605459336416260627 52469219408189004624390941)
      ·
        refine ⟨19675957278070876734146603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52469219408189004624390941 19675957278070876734146603)
        ·
          refine ⟨29513935917106315101219905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19675957278070876734146603 29513935917106315101219905)
          ·
            refine ⟨22135451937829736325914929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29513935917106315101219905 22135451937829736325914929)
            ·
              refine ⟨16601588953372302244436197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22135451937829736325914929 16601588953372302244436197)
              ·
                refine ⟨3112797928757306670831787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16601588953372302244436197 3112797928757306670831787)
                ·
                  refine ⟨4669196893135960006247681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3112797928757306670831787 4669196893135960006247681)
                  ·
                    refine ⟨3501897669851970004685761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4669196893135960006247681 3501897669851970004685761)
                    ·
                      refine ⟨2626423252388977503514321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3501897669851970004685761 2626423252388977503514321)
                      ·
                        rfl

theorem cell23_5114941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_5114941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114941 prefixEnd_5114941 := by exact prefixLift 5114941
  have htrace : WordTrace (prefixWord ++ tailWord_5114941) baseStart_5114941 baseEnd_5114941 := by
    simpa [prefixWord, tailWord_5114941, baseEnd_5114941] using wordTrace_append hprefix tailTrace_5114941
  have hstable : (prefixWord ++ tailWord_5114941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114941).length < 2 ^ (prefixWord ++ tailWord_5114941).sum := by decide
  have hdescent : baseEnd_5114941 < baseStart_5114941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114963 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 4]
def baseStart_5114963 : Nat := 118140960795 + 5114963 * 2 ^ 59
def prefixEnd_5114963 : Nat := 4983230072969 + 3 ^ 40 * 5114963 * 2
def baseEnd_5114963 : Nat := 2626434548963376417439219

theorem tailTrace_5114963 : CollatzResearch.WordTrace tailWord_5114963 prefixEnd_5114963 2626434548963376417439219 := by
  unfold tailWord_5114963
  simp only [CollatzResearch.WordTrace]
  refine ⟨186558026968370091977357543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124372017978913394651571695 186558026968370091977357543)
  ·
    refine ⟨279837040452555137966036315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186558026968370091977357543 279837040452555137966036315)
    ·
      refine ⟨419755560678832706949054473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279837040452555137966036315 419755560678832706949054473)
      ·
        refine ⟨314816670509124530211790855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419755560678832706949054473 314816670509124530211790855)
        ·
          refine ⟨472225005763686795317686283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314816670509124530211790855 472225005763686795317686283)
          ·
            refine ⟨708337508645530192976529425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472225005763686795317686283 708337508645530192976529425)
            ·
              refine ⟨531253131484147644732397069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708337508645530192976529425 531253131484147644732397069)
              ·
                refine ⟨199219924306555366774648901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 531253131484147644732397069 199219924306555366774648901)
                ·
                  refine ⟨37353735807479131270246669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199219924306555366774648901 37353735807479131270246669)
                  ·
                    refine ⟨14007650927804674226342501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37353735807479131270246669 14007650927804674226342501)
                    ·
                      refine ⟨2626434548963376417439219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14007650927804674226342501 2626434548963376417439219)
                      ·
                        rfl

theorem cell23_5114963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_5114963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114963 prefixEnd_5114963 := by exact prefixLift 5114963
  have htrace : WordTrace (prefixWord ++ tailWord_5114963) baseStart_5114963 baseEnd_5114963 := by
    simpa [prefixWord, tailWord_5114963, baseEnd_5114963] using wordTrace_append hprefix tailTrace_5114963
  have hstable : (prefixWord ++ tailWord_5114963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114963).length < 2 ^ (prefixWord ++ tailWord_5114963).sum := by decide
  have hdescent : baseEnd_5114963 < baseStart_5114963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5114993 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 6]
def baseStart_5114993 : Nat := 118140960795 + 5114993 * 2 ^ 59
def prefixEnd_5114993 : Nat := 4983230072969 + 3 ^ 40 * 5114993 * 2
def baseEnd_5114993 : Nat := 2626449953383011300064081

theorem tailTrace_5114993 : CollatzResearch.WordTrace tailWord_5114993 prefixEnd_5114993 2626449953383011300064081 := by
  unfold tailWord_5114993
  simp only [CollatzResearch.WordTrace]
  refine ⟨186559121158261407100949633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124372747438840938067299755 186559121158261407100949633)
  ·
    refine ⟨139919340868696055325712225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186559121158261407100949633 139919340868696055325712225)
    ·
      refine ⟨104939505651522041494284169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139919340868696055325712225 104939505651522041494284169)
      ·
        refine ⟨78704629238641531120713127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104939505651522041494284169 78704629238641531120713127)
        ·
          refine ⟨118056943857962296681069691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78704629238641531120713127 118056943857962296681069691)
          ·
            refine ⟨177085415786943445021604537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118056943857962296681069691 177085415786943445021604537)
            ·
              refine ⟨132814061840207583766203403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177085415786943445021604537 132814061840207583766203403)
              ·
                refine ⟨199221092760311375649305105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132814061840207583766203403 199221092760311375649305105)
                ·
                  refine ⟨149415819570233531736978829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199221092760311375649305105 149415819570233531736978829)
                  ·
                    refine ⟨56030932338837574401367061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149415819570233531736978829 56030932338837574401367061)
                    ·
                      refine ⟨2626449953383011300064081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56030932338837574401367061 2626449953383011300064081)
                      ·
                        rfl

theorem cell23_5114993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_5114993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5114993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5114993 prefixEnd_5114993 := by exact prefixLift 5114993
  have htrace : WordTrace (prefixWord ++ tailWord_5114993) baseStart_5114993 baseEnd_5114993 := by
    simpa [prefixWord, tailWord_5114993, baseEnd_5114993] using wordTrace_append hprefix tailTrace_5114993
  have hstable : (prefixWord ++ tailWord_5114993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5114993).length < 2 ^ (prefixWord ++ tailWord_5114993).sum := by decide
  have hdescent : baseEnd_5114993 < baseStart_5114993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5114993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115037 : List Nat := [1, 4, 2, 1, 1, 2, 2, 5, 5]
def baseStart_5115037 : Nat := 118140960795 + 5115037 * 2 ^ 59
def prefixEnd_5115037 : Nat := 4983230072969 + 3 ^ 40 * 5115037 * 2
def baseEnd_5115037 : Nat := 291830282947978791990431

theorem tailTrace_5115037 : CollatzResearch.WordTrace tailWord_5115037 prefixEnd_5115037 291830282947978791990431 := by
  unfold tailWord_5115037
  simp only [CollatzResearch.WordTrace]
  refine ⟨186560725970102002615551365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124373817313401335077034243 186560725970102002615551365)
  ·
    refine ⟨34980136119394125490415881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186560725970102002615551365 34980136119394125490415881)
    ·
      refine ⟨26235102089545594117811911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34980136119394125490415881 26235102089545594117811911)
      ·
        refine ⟨39352653134318391176717867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26235102089545594117811911 39352653134318391176717867)
        ·
          refine ⟨59028979701477586765076801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39352653134318391176717867 59028979701477586765076801)
          ·
            refine ⟨44271734776108190073807601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59028979701477586765076801 44271734776108190073807601)
            ·
              refine ⟨33203801082081142555355701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44271734776108190073807601 33203801082081142555355701)
              ·
                refine ⟨3112856351445107114564597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33203801082081142555355701 3112856351445107114564597)
                ·
                  refine ⟨291830282947978791990431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3112856351445107114564597 291830282947978791990431)
                  ·
                    rfl

theorem cell23_5115037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_5115037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115037 prefixEnd_5115037 := by exact prefixLift 5115037
  have htrace : WordTrace (prefixWord ++ tailWord_5115037) baseStart_5115037 baseEnd_5115037 := by
    simpa [prefixWord, tailWord_5115037, baseEnd_5115037] using wordTrace_append hprefix tailTrace_5115037
  have hstable : (prefixWord ++ tailWord_5115037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115037).length < 2 ^ (prefixWord ++ tailWord_5115037).sum := by decide
  have hdescent : baseEnd_5115037 < baseStart_5115037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115114 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 3, 4]
def baseStart_5115114 : Nat := 118140960795 + 5115114 * 2 ^ 59
def prefixEnd_5115114 : Nat := 4983230072969 + 3 ^ 40 * 5115114 * 2
def baseEnd_5115114 : Nat := 875504028180735108883675

theorem tailTrace_5115114 : CollatzResearch.WordTrace tailWord_5115114 prefixEnd_5115114 875504028180735108883675 := by
  unfold tailWord_5115114
  simp only [CollatzResearch.WordTrace]
  refine ⟨46640883597705761191526099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124375689593882029844069597 46640883597705761191526099)
  ·
    refine ⟨69961325396558641787289149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46640883597705761191526099 69961325396558641787289149)
    ·
      refine ⟨26235497023709490670233431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69961325396558641787289149 26235497023709490670233431)
      ·
        refine ⟨39353245535564236005350147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26235497023709490670233431 39353245535564236005350147)
        ·
          refine ⟨59029868303346354008025221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39353245535564236005350147 59029868303346354008025221)
          ·
            refine ⟨11068100306877441376504729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59029868303346354008025221 11068100306877441376504729)
            ·
              refine ⟨8301075230158081032378547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11068100306877441376504729 8301075230158081032378547)
              ·
                refine ⟨12451612845237121548567821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8301075230158081032378547 12451612845237121548567821)
                ·
                  refine ⟨4669354816963920580712933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12451612845237121548567821 4669354816963920580712933)
                  ·
                    refine ⟨875504028180735108883675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4669354816963920580712933 875504028180735108883675)
                    ·
                      rfl

theorem cell23_5115114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_5115114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115114 prefixEnd_5115114 := by exact prefixLift 5115114
  have htrace : WordTrace (prefixWord ++ tailWord_5115114) baseStart_5115114 baseEnd_5115114 := by
    simpa [prefixWord, tailWord_5115114, baseEnd_5115114] using wordTrace_append hprefix tailTrace_5115114
  have hstable : (prefixWord ++ tailWord_5115114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115114).length < 2 ^ (prefixWord ++ tailWord_5115114).sum := by decide
  have hdescent : baseEnd_5115114 < baseStart_5115114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115130 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_5115130 : Nat := 118140960795 + 5115130 * 2 ^ 59
def prefixEnd_5115130 : Nat := 4983230072969 + 3 ^ 40 * 5115130 * 2
def baseEnd_5115130 : Nat := 2626520300232677264050951

theorem tailTrace_5115130 : CollatzResearch.WordTrace tailWord_5115130 prefixEnd_5115130 2626520300232677264050951 := by
  unfold tailWord_5115130
  simp only [CollatzResearch.WordTrace]
  refine ⟨46641029489691269874671711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124376078639176719665791229 46641029489691269874671711)
  ·
    refine ⟨69961544234536904812007567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46641029489691269874671711 69961544234536904812007567)
    ·
      refine ⟨104942316351805357218011351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69961544234536904812007567 104942316351805357218011351)
      ·
        refine ⟨157413474527708035827017027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104942316351805357218011351 157413474527708035827017027)
        ·
          refine ⟨236120211791562053740525541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157413474527708035827017027 236120211791562053740525541)
          ·
            refine ⟨44272539710917885076348539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236120211791562053740525541 44272539710917885076348539)
            ·
              refine ⟨66408809566376827614522809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44272539710917885076348539 66408809566376827614522809)
              ·
                refine ⟨49806607174782620710892107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66408809566376827614522809 49806607174782620710892107)
                ·
                  refine ⟨74709910762173931066338161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49806607174782620710892107 74709910762173931066338161)
                  ·
                    refine ⟨56032433071630448299753621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74709910762173931066338161 56032433071630448299753621)
                    ·
                      refine ⟨2626520300232677264050951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56032433071630448299753621 2626520300232677264050951)
                      ·
                        rfl

theorem cell23_5115130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_5115130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115130 prefixEnd_5115130 := by exact prefixLift 5115130
  have htrace : WordTrace (prefixWord ++ tailWord_5115130) baseStart_5115130 baseEnd_5115130 := by
    simpa [prefixWord, tailWord_5115130, baseEnd_5115130] using wordTrace_append hprefix tailTrace_5115130
  have hstable : (prefixWord ++ tailWord_5115130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115130).length < 2 ^ (prefixWord ++ tailWord_5115130).sum := by decide
  have hdescent : baseEnd_5115130 < baseStart_5115130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115164 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_5115164 : Nat := 118140960795 + 5115164 * 2 ^ 59
def prefixEnd_5115164 : Nat := 4983230072969 + 3 ^ 40 * 5115164 * 2
def baseEnd_5115164 : Nat := 2626537758574930131025795

theorem tailTrace_5115164 : CollatzResearch.WordTrace tailWord_5115164 prefixEnd_5115164 2626537758574930131025795 := by
  unfold tailWord_5115164
  simp only [CollatzResearch.WordTrace]
  refine ⟨93282679020320951652712273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124376905360427935536949697 93282679020320951652712273)
  ·
    refine ⟨69962009265240713739534205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93282679020320951652712273 69962009265240713739534205)
    ·
      refine ⟨26235753474465267652325327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69962009265240713739534205 26235753474465267652325327)
      ·
        refine ⟨39353630211697901478487991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26235753474465267652325327 39353630211697901478487991)
        ·
          refine ⟨59030445317546852217731987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39353630211697901478487991 59030445317546852217731987)
          ·
            refine ⟨88545667976320278326597981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59030445317546852217731987 88545667976320278326597981)
            ·
              refine ⟨33204625491120104372474243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88545667976320278326597981 33204625491120104372474243)
              ·
                refine ⟨49806938236680156558711365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33204625491120104372474243 49806938236680156558711365)
                ·
                  refine ⟨9338800919377529354758381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49806938236680156558711365 9338800919377529354758381)
                  ·
                    refine ⟨3502050344766573508034393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9338800919377529354758381 3502050344766573508034393)
                    ·
                      refine ⟨2626537758574930131025795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502050344766573508034393 2626537758574930131025795)
                      ·
                        rfl

theorem cell23_5115164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_5115164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115164 prefixEnd_5115164 := by exact prefixLift 5115164
  have htrace : WordTrace (prefixWord ++ tailWord_5115164) baseStart_5115164 baseEnd_5115164 := by
    simpa [prefixWord, tailWord_5115164, baseEnd_5115164] using wordTrace_append hprefix tailTrace_5115164
  have hstable : (prefixWord ++ tailWord_5115164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115164).length < 2 ^ (prefixWord ++ tailWord_5115164).sum := by decide
  have hdescent : baseEnd_5115164 < baseStart_5115164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115171 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 3, 1, 3]
def baseStart_5115171 : Nat := 118140960795 + 5115171 * 2 ^ 59
def prefixEnd_5115171 : Nat := 4983230072969 + 3 ^ 40 * 5115171 * 2
def baseEnd_5115171 : Nat := 2626541352939511603638263

theorem tailTrace_5115171 : CollatzResearch.WordTrace tailWord_5115171 prefixEnd_5115171 2626541352939511603638263 := by
  unfold tailWord_5115171
  simp only [CollatzResearch.WordTrace]
  refine ⟨186565613351616543500929367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124377075567744362333952911 186565613351616543500929367)
  ·
    refine ⟨279848420027424815251394051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186565613351616543500929367 279848420027424815251394051)
    ·
      refine ⟨419772630041137222877091077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279848420027424815251394051 419772630041137222877091077)
      ·
        refine ⟨78707368132713229289454577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 419772630041137222877091077 78707368132713229289454577)
        ·
          refine ⟨59030526099534921967090933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78707368132713229289454577 59030526099534921967090933)
          ·
            refine ⟨5534111821831398934414775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59030526099534921967090933 5534111821831398934414775)
            ·
              refine ⟨8301167732747098401622163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5534111821831398934414775 8301167732747098401622163)
              ·
                refine ⟨12451751599120647602433245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8301167732747098401622163 12451751599120647602433245)
                ·
                  refine ⟨4669406849670242850912467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12451751599120647602433245 4669406849670242850912467)
                  ·
                    refine ⟨7004110274505364276368701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4669406849670242850912467 7004110274505364276368701)
                    ·
                      refine ⟨2626541352939511603638263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004110274505364276368701 2626541352939511603638263)
                      ·
                        rfl

theorem cell23_5115171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_5115171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115171 prefixEnd_5115171 := by exact prefixLift 5115171
  have htrace : WordTrace (prefixWord ++ tailWord_5115171) baseStart_5115171 baseEnd_5115171 := by
    simpa [prefixWord, tailWord_5115171, baseEnd_5115171] using wordTrace_append hprefix tailTrace_5115171
  have hstable : (prefixWord ++ tailWord_5115171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115171).length < 2 ^ (prefixWord ++ tailWord_5115171).sum := by decide
  have hdescent : baseEnd_5115171 < baseStart_5115171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115177 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 3, 8, 2]
def baseStart_5115177 : Nat := 118140960795 + 5115177 * 2 ^ 59
def prefixEnd_5115177 : Nat := 4983230072969 + 3 ^ 40 * 5115177 * 2
def baseEnd_5115177 : Nat := 2626544433823438580163235

theorem tailTrace_5115177 : CollatzResearch.WordTrace tailWord_5115177 prefixEnd_5115177 2626544433823438580163235 := by
  unfold tailWord_5115177
  simp only [CollatzResearch.WordTrace]
  refine ⟨186565832189594806525647785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124377221459729871017098523 186565832189594806525647785)
  ·
    refine ⟨139924374142196104894235839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186565832189594806525647785 139924374142196104894235839)
    ·
      refine ⟨209886561213294157341353759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139924374142196104894235839 209886561213294157341353759)
      ·
        refine ⟨314829841819941236012030639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209886561213294157341353759 314829841819941236012030639)
        ·
          refine ⟨472244762729911854018045959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314829841819941236012030639 472244762729911854018045959)
          ·
            refine ⟨708367144094867781027068939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472244762729911854018045959 708367144094867781027068939)
            ·
              refine ⟨1062550716142301671540603409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708367144094867781027068939 1062550716142301671540603409)
              ·
                refine ⟨796913037106726253655452557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1062550716142301671540603409 796913037106726253655452557)
                ·
                  refine ⟨298842388915022345120794709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 796913037106726253655452557 298842388915022345120794709)
                  ·
                    refine ⟨3502059245097918106884313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 298842388915022345120794709 3502059245097918106884313)
                    ·
                      refine ⟨2626544433823438580163235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502059245097918106884313 2626544433823438580163235)
                      ·
                        rfl

theorem cell23_5115177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 8, 2].length) (baseStart_5115177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115177 prefixEnd_5115177 := by exact prefixLift 5115177
  have htrace : WordTrace (prefixWord ++ tailWord_5115177) baseStart_5115177 baseEnd_5115177 := by
    simpa [prefixWord, tailWord_5115177, baseEnd_5115177] using wordTrace_append hprefix tailTrace_5115177
  have hstable : (prefixWord ++ tailWord_5115177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115177).length < 2 ^ (prefixWord ++ tailWord_5115177).sum := by decide
  have hdescent : baseEnd_5115177 < baseStart_5115177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115200 : List Nat := [2, 1, 1, 2, 2, 1, 3, 11]
def baseStart_5115200 : Nat := 118140960795 + 5115200 * 2 ^ 59
def prefixEnd_5115200 : Nat := 4983230072969 + 3 ^ 40 * 5115200 * 2
def baseEnd_5115200 : Nat := 97279860884388592228727

theorem tailTrace_5115200 : CollatzResearch.WordTrace tailWord_5115200 prefixEnd_5115200 97279860884388592228727 := by
  unfold tailWord_5115200
  simp only [CollatzResearch.WordTrace]
  refine ⟨93283335534255740726867527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124377780712340987635823369 93283335534255740726867527)
  ·
    refine ⟨139925003301383611090301291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93283335534255740726867527 139925003301383611090301291)
    ·
      refine ⟨209887504952075416635451937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139925003301383611090301291 209887504952075416635451937)
      ·
        refine ⟨157415628714056562476588953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209887504952075416635451937 157415628714056562476588953)
        ·
          refine ⟨118061721535542421857441715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157415628714056562476588953 118061721535542421857441715)
          ·
            refine ⟨177092582303313632786162573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118061721535542421857441715 177092582303313632786162573)
            ·
              refine ⟨66409718363742612294810965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177092582303313632786162573 66409718363742612294810965)
              ·
                refine ⟨97279860884388592228727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 66409718363742612294810965 97279860884388592228727)
                ·
                  rfl

theorem cell23_5115200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 11].length) (baseStart_5115200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115200 prefixEnd_5115200 := by exact prefixLift 5115200
  have htrace : WordTrace (prefixWord ++ tailWord_5115200) baseStart_5115200 baseEnd_5115200 := by
    simpa [prefixWord, tailWord_5115200, baseEnd_5115200] using wordTrace_append hprefix tailTrace_5115200
  have hstable : (prefixWord ++ tailWord_5115200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115200).length < 2 ^ (prefixWord ++ tailWord_5115200).sum := by decide
  have hdescent : baseEnd_5115200 < baseStart_5115200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115204 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_5115204 : Nat := 118140960795 + 5115204 * 2 ^ 59
def prefixEnd_5115204 : Nat := 4983230072969 + 3 ^ 40 * 5115204 * 2
def baseEnd_5115204 : Nat := 875519432600369991508537

theorem tailTrace_5115204 : CollatzResearch.WordTrace tailWord_5115204 prefixEnd_5115204 875519432600369991508537 := by
  unfold tailWord_5115204
  simp only [CollatzResearch.WordTrace]
  refine ⟨93283408480248495068440333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124377877973664660091253777 93283408480248495068440333)
  ·
    refine ⟨34981278180093185650665125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93283408480248495068440333 34981278180093185650665125)
    ·
      refine ⟨6558989658767472309499711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34981278180093185650665125 6558989658767472309499711)
      ·
        refine ⟨9838484488151208464249567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6558989658767472309499711 9838484488151208464249567)
        ·
          refine ⟨14757726732226812696374351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9838484488151208464249567 14757726732226812696374351)
          ·
            refine ⟨22136590098340219044561527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14757726732226812696374351 22136590098340219044561527)
            ·
              refine ⟨33204885147510328566842291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22136590098340219044561527 33204885147510328566842291)
              ·
                refine ⟨49807327721265492850263437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33204885147510328566842291 49807327721265492850263437)
                ·
                  refine ⟨18677747895474559818848789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49807327721265492850263437 18677747895474559818848789)
                  ·
                    refine ⟨875519432600369991508537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18677747895474559818848789 875519432600369991508537)
                    ·
                      rfl

theorem cell23_5115204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_5115204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115204 prefixEnd_5115204 := by exact prefixLift 5115204
  have htrace : WordTrace (prefixWord ++ tailWord_5115204) baseStart_5115204 baseEnd_5115204 := by
    simpa [prefixWord, tailWord_5115204, baseEnd_5115204] using wordTrace_append hprefix tailTrace_5115204
  have hstable : (prefixWord ++ tailWord_5115204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115204).length < 2 ^ (prefixWord ++ tailWord_5115204).sum := by decide
  have hdescent : baseEnd_5115204 < baseStart_5115204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115207 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_5115207 : Nat := 118140960795 + 5115207 * 2 ^ 59
def prefixEnd_5115207 : Nat := 4983230072969 + 3 ^ 40 * 5115207 * 2
def baseEnd_5115207 : Nat := 2626559838243073462788097

theorem tailTrace_5115207 : CollatzResearch.WordTrace tailWord_5115207 prefixEnd_5115207 2626559838243073462788097 := by
  unfold tailWord_5115207
  simp only [CollatzResearch.WordTrace]
  refine ⟨186566926379486121649239875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124377950919657414432826583 186566926379486121649239875)
  ·
    refine ⟨279850389569229182473859813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186566926379486121649239875 279850389569229182473859813)
    ·
      refine ⟨52471948044230471713848715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279850389569229182473859813 52471948044230471713848715)
      ·
        refine ⟨78707922066345707570773073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52471948044230471713848715 78707922066345707570773073)
        ·
          refine ⟨59030941549759280678079805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78707922066345707570773073 59030941549759280678079805)
          ·
            refine ⟨22136603081159730254279927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59030941549759280678079805 22136603081159730254279927)
            ·
              refine ⟨33204904621739595381419891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22136603081159730254279927 33204904621739595381419891)
              ·
                refine ⟨49807356932609393072129837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33204904621739595381419891 49807356932609393072129837)
                ·
                  refine ⟨18677758849728522402048689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49807356932609393072129837 18677758849728522402048689)
                  ·
                    refine ⟨14008319137296391801536517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18677758849728522402048689 14008319137296391801536517)
                    ·
                      refine ⟨2626559838243073462788097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14008319137296391801536517 2626559838243073462788097)
                      ·
                        rfl

theorem cell23_5115207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_5115207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115207 prefixEnd_5115207 := by exact prefixLift 5115207
  have htrace : WordTrace (prefixWord ++ tailWord_5115207) baseStart_5115207 baseEnd_5115207 := by
    simpa [prefixWord, tailWord_5115207, baseEnd_5115207] using wordTrace_append hprefix tailTrace_5115207
  have hstable : (prefixWord ++ tailWord_5115207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115207).length < 2 ^ (prefixWord ++ tailWord_5115207).sum := by decide
  have hdescent : baseEnd_5115207 < baseStart_5115207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115221 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 2, 4]
def baseStart_5115221 : Nat := 118140960795 + 5115221 * 2 ^ 59
def prefixEnd_5115221 : Nat := 4983230072969 + 3 ^ 40 * 5115221 * 2
def baseEnd_5115221 : Nat := 875522342324078802671011

theorem tailTrace_5115221 : CollatzResearch.WordTrace tailWord_5115221 prefixEnd_5115221 875522342324078802671011 := by
  unfold tailWord_5115221
  simp only [CollatzResearch.WordTrace]
  refine ⟨186567437001435402040249517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124378291334290268026833011 186567437001435402040249517)
  ·
    refine ⟨69962788875538275765093569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186567437001435402040249517 69962788875538275765093569)
    ·
      refine ⟨52472091656653706823820177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69962788875538275765093569 52472091656653706823820177)
      ·
        refine ⟨39354068742490280117865133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52472091656653706823820177 39354068742490280117865133)
        ·
          refine ⟨14757775778433855044199425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39354068742490280117865133 14757775778433855044199425)
          ·
            refine ⟨11068331833825391283149569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14757775778433855044199425 11068331833825391283149569)
            ·
              refine ⟨8301248875369043462362177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11068331833825391283149569 8301248875369043462362177)
              ·
                refine ⟨6225936656526782596771633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8301248875369043462362177 6225936656526782596771633)
                ·
                  refine ⟨4669452492395086947578725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6225936656526782596771633 4669452492395086947578725)
                  ·
                    refine ⟨875522342324078802671011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4669452492395086947578725 875522342324078802671011)
                    ·
                      rfl

theorem cell23_5115221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_5115221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115221 prefixEnd_5115221 := by exact prefixLift 5115221
  have htrace : WordTrace (prefixWord ++ tailWord_5115221) baseStart_5115221 baseEnd_5115221 := by
    simpa [prefixWord, tailWord_5115221, baseEnd_5115221] using wordTrace_append hprefix tailTrace_5115221
  have hstable : (prefixWord ++ tailWord_5115221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115221).length < 2 ^ (prefixWord ++ tailWord_5115221).sum := by decide
  have hdescent : baseEnd_5115221 < baseStart_5115221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115244 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 3]
def baseStart_5115244 : Nat := 118140960795 + 5115244 * 2 ^ 59
def prefixEnd_5115244 : Nat := 4983230072969 + 3 ^ 40 * 5115244 * 2
def baseEnd_5115244 : Nat := 2626578837027289818025427

theorem tailTrace_5115244 : CollatzResearch.WordTrace tailWord_5115244 prefixEnd_5115244 2626578837027289818025427 := by
  unfold tailWord_5115244
  simp only [CollatzResearch.WordTrace]
  refine ⟨93284137940176038484168393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124378850586901384645557857 93284137940176038484168393)
  ·
    refine ⟨69963103455132028863126295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93284137940176038484168393 69963103455132028863126295)
    ·
      refine ⟨104944655182698043294689443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69963103455132028863126295 104944655182698043294689443)
      ·
        refine ⟨157416982774047064942034165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104944655182698043294689443 157416982774047064942034165)
        ·
          refine ⟨14757842135066912338315703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157416982774047064942034165 14757842135066912338315703)
          ·
            refine ⟨22136763202600368507473555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14757842135066912338315703 22136763202600368507473555)
            ·
              refine ⟨33205144803900552761210333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22136763202600368507473555 33205144803900552761210333)
              ·
                refine ⟨12451929301462707285453875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33205144803900552761210333 12451929301462707285453875)
                ·
                  refine ⟨18677893952194060928180813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12451929301462707285453875 18677893952194060928180813)
                  ·
                    refine ⟨7004210232072772848067805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18677893952194060928180813 7004210232072772848067805)
                    ·
                      refine ⟨2626578837027289818025427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004210232072772848067805 2626578837027289818025427)
                      ·
                        rfl

theorem cell23_5115244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_5115244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115244 prefixEnd_5115244 := by exact prefixLift 5115244
  have htrace : WordTrace (prefixWord ++ tailWord_5115244) baseStart_5115244 baseEnd_5115244 := by
    simpa [prefixWord, tailWord_5115244, baseEnd_5115244] using wordTrace_append hprefix tailTrace_5115244
  have hstable : (prefixWord ++ tailWord_5115244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115244).length < 2 ^ (prefixWord ++ tailWord_5115244).sum := by decide
  have hdescent : baseEnd_5115244 < baseStart_5115244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115262 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5115262 : Nat := 118140960795 + 5115262 * 2 ^ 59
def prefixEnd_5115262 : Nat := 4983230072969 + 3 ^ 40 * 5115262 * 2
def baseEnd_5115262 : Nat := 2626588079679070747600345

theorem tailTrace_5115262 : CollatzResearch.WordTrace tailWord_5115262 prefixEnd_5115262 2626588079679070747600345 := by
  unfold tailWord_5115262
  simp only [CollatzResearch.WordTrace]
  refine ⟨23321116549285858255311505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124379288262857910694994693 23321116549285858255311505)
  ·
    refine ⟨17490837411964393691483629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23321116549285858255311505 17490837411964393691483629)
    ·
      refine ⟨6559064029486647634306361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17490837411964393691483629 6559064029486647634306361)
      ·
        refine ⟨4919298022114985725729771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6559064029486647634306361 4919298022114985725729771)
        ·
          refine ⟨7378947033172478588594657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4919298022114985725729771 7378947033172478588594657)
          ·
            refine ⟨5534210274879358941445993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7378947033172478588594657 5534210274879358941445993)
            ·
              refine ⟨4150657706159519206084495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5534210274879358941445993 4150657706159519206084495)
              ·
                refine ⟨6225986559239278809126743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4150657706159519206084495 6225986559239278809126743)
                ·
                  refine ⟨9338979838858918213690115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6225986559239278809126743 9338979838858918213690115)
                  ·
                    refine ⟨14008469758288377320535173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9338979838858918213690115 14008469758288377320535173)
                    ·
                      refine ⟨2626588079679070747600345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14008469758288377320535173 2626588079679070747600345)
                      ·
                        rfl

theorem cell23_5115262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5115262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115262 prefixEnd_5115262 := by exact prefixLift 5115262
  have htrace : WordTrace (prefixWord ++ tailWord_5115262) baseStart_5115262 baseEnd_5115262 := by
    simpa [prefixWord, tailWord_5115262, baseEnd_5115262] using wordTrace_append hprefix tailTrace_5115262
  have hstable : (prefixWord ++ tailWord_5115262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115262).length < 2 ^ (prefixWord ++ tailWord_5115262).sum := by decide
  have hdescent : baseEnd_5115262 < baseStart_5115262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115265 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_5115265 : Nat := 118140960795 + 5115265 * 2 ^ 59
def prefixEnd_5115265 : Nat := 4983230072969 + 3 ^ 40 * 5115265 * 2
def baseEnd_5115265 : Nat := 2626589620121034235862831

theorem tailTrace_5115265 : CollatzResearch.WordTrace tailWord_5115265 prefixEnd_5115265 2626589620121034235862831 := by
  unfold tailWord_5115265
  simp only [CollatzResearch.WordTrace]
  refine ⟨186569041813275997554851249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124379361208850665036567499 186569041813275997554851249)
  ·
    refine ⟨139926781359956998166138437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186569041813275997554851249 139926781359956998166138437)
    ·
      refine ⟨26236271504991937156150957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139926781359956998166138437 26236271504991937156150957)
      ·
        refine ⟨9838601814371976433556609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26236271504991937156150957 9838601814371976433556609)
        ·
          refine ⟨7378951360778982325167457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9838601814371976433556609 7378951360778982325167457)
          ·
            refine ⟨5534213520584236743875593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7378951360778982325167457 5534213520584236743875593)
            ·
              refine ⟨4150660140438177557906695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5534213520584236743875593 4150660140438177557906695)
              ·
                refine ⟨6225990210657266336860043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4150660140438177557906695 6225990210657266336860043)
                ·
                  refine ⟨9338985315985899505290065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6225990210657266336860043 9338985315985899505290065)
                  ·
                    refine ⟨7004238986989424628967549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9338985315985899505290065 7004238986989424628967549)
                    ·
                      refine ⟨2626589620121034235862831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004238986989424628967549 2626589620121034235862831)
                      ·
                        rfl

theorem cell23_5115265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_5115265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115265 prefixEnd_5115265 := by exact prefixLift 5115265
  have htrace : WordTrace (prefixWord ++ tailWord_5115265) baseStart_5115265 baseEnd_5115265 := by
    simpa [prefixWord, tailWord_5115265, baseEnd_5115265] using wordTrace_append hprefix tailTrace_5115265
  have hstable : (prefixWord ++ tailWord_5115265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115265).length < 2 ^ (prefixWord ++ tailWord_5115265).sum := by decide
  have hdescent : baseEnd_5115265 < baseStart_5115265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115278 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_5115278 : Nat := 118140960795 + 5115278 * 2 ^ 59
def prefixEnd_5115278 : Nat := 4983230072969 + 3 ^ 40 * 5115278 * 2
def baseEnd_5115278 : Nat := 2626596295369542685000271

theorem tailTrace_5115278 : CollatzResearch.WordTrace tailWord_5115278 prefixEnd_5115278 2626596295369542685000271 := by
  unfold tailWord_5115278
  simp only [CollatzResearch.WordTrace]
  refine ⟨23321189495278612596884311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124379677308152600516716325 23321189495278612596884311)
  ·
    refine ⟨34981784242917918895326467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23321189495278612596884311 34981784242917918895326467)
    ·
      refine ⟨52472676364376878342989701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34981784242917918895326467 52472676364376878342989701)
      ·
        refine ⟨9838626818320664689310569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52472676364376878342989701 9838626818320664689310569)
        ·
          refine ⟨7378970113740498516982927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9838626818320664689310569 7378970113740498516982927)
          ·
            refine ⟨11068455170610747775474391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7378970113740498516982927 11068455170610747775474391)
            ·
              refine ⟨16602682755916121663211587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11068455170610747775474391 16602682755916121663211587)
              ·
                refine ⟨24904024133874182494817381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16602682755916121663211587 24904024133874182494817381)
                ·
                  refine ⟨4669504525101409217778259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24904024133874182494817381 4669504525101409217778259)
                  ·
                    refine ⟨7004256787652113826667389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4669504525101409217778259 7004256787652113826667389)
                    ·
                      refine ⟨2626596295369542685000271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004256787652113826667389 2626596295369542685000271)
                      ·
                        rfl

theorem cell23_5115278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_5115278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115278 prefixEnd_5115278 := by exact prefixLift 5115278
  have htrace : WordTrace (prefixWord ++ tailWord_5115278) baseStart_5115278 baseEnd_5115278 := by
    simpa [prefixWord, tailWord_5115278, baseEnd_5115278] using wordTrace_append hprefix tailTrace_5115278
  have hstable : (prefixWord ++ tailWord_5115278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115278).length < 2 ^ (prefixWord ++ tailWord_5115278).sum := by decide
  have hdescent : baseEnd_5115278 < baseStart_5115278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115287 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_5115287 : Nat := 118140960795 + 5115287 * 2 ^ 59
def prefixEnd_5115287 : Nat := 4983230072969 + 3 ^ 40 * 5115287 * 2
def baseEnd_5115287 : Nat := 2626600916695433149787729

theorem tailTrace_5115287 : CollatzResearch.WordTrace tailWord_5115287 prefixEnd_5115287 2626600916695433149787729 := by
  unfold tailWord_5115287
  simp only [CollatzResearch.WordTrace]
  refine ⟨186569844219196295312152115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124379896146130863541434743 186569844219196295312152115)
  ·
    refine ⟨279854766328794442968228173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186569844219196295312152115 279854766328794442968228173)
    ·
      refine ⟨104945537373297916113085565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279854766328794442968228173 104945537373297916113085565)
      ·
        refine ⟨39354576514986718542407087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104945537373297916113085565 39354576514986718542407087)
        ·
          refine ⟨59031864772480077813610631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39354576514986718542407087 59031864772480077813610631)
          ·
            refine ⟨88547797158720116720415947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59031864772480077813610631 88547797158720116720415947)
            ·
              refine ⟨132821695738080175080623921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88547797158720116720415947 132821695738080175080623921)
              ·
                refine ⟨99616271803560131310467941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132821695738080175080623921 99616271803560131310467941)
                ·
                  refine ⟨18678050963167524620712739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99616271803560131310467941 18678050963167524620712739)
                  ·
                    refine ⟨28017076444751286931069109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18678050963167524620712739 28017076444751286931069109)
                    ·
                      refine ⟨2626600916695433149787729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28017076444751286931069109 2626600916695433149787729)
                      ·
                        rfl

theorem cell23_5115287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_5115287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115287 prefixEnd_5115287 := by exact prefixLift 5115287
  have htrace : WordTrace (prefixWord ++ tailWord_5115287) baseStart_5115287 baseEnd_5115287 := by
    simpa [prefixWord, tailWord_5115287, baseEnd_5115287] using wordTrace_append hprefix tailTrace_5115287
  have hstable : (prefixWord ++ tailWord_5115287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115287).length < 2 ^ (prefixWord ++ tailWord_5115287).sum := by decide
  have hdescent : baseEnd_5115287 < baseStart_5115287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115344 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 1, 7, 2]
def baseStart_5115344 : Nat := 118140960795 + 5115344 * 2 ^ 59
def prefixEnd_5115344 : Nat := 4983230072969 + 3 ^ 40 * 5115344 * 2
def baseEnd_5115344 : Nat := 2626630185092739426774967

theorem tailTrace_5115344 : CollatzResearch.WordTrace tailWord_5115344 prefixEnd_5115344 2626630185092739426774967 := by
  unfold tailWord_5115344
  simp only [CollatzResearch.WordTrace]
  refine ⟨93285961589994897023488543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124381282119993196031318057 93285961589994897023488543)
  ·
    refine ⟨139928942384992345535232815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93285961589994897023488543 139928942384992345535232815)
    ·
      refine ⟨209893413577488518302849223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139928942384992345535232815 209893413577488518302849223)
      ·
        refine ⟨314840120366232777454273835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209893413577488518302849223 314840120366232777454273835)
        ·
          refine ⟨472260180549349166181410753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314840120366232777454273835 472260180549349166181410753)
          ·
            refine ⟨354195135412011874636058065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 472260180549349166181410753 354195135412011874636058065)
            ·
              refine ⟨265646351559008905977043549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354195135412011874636058065 265646351559008905977043549)
              ·
                refine ⟨99617381834628339741391331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265646351559008905977043549 99617381834628339741391331)
                ·
                  refine ⟨149426072751942509612086997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99617381834628339741391331 149426072751942509612086997)
                  ·
                    refine ⟨3502173580123652569033289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 149426072751942509612086997 3502173580123652569033289)
                    ·
                      refine ⟨2626630185092739426774967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502173580123652569033289 2626630185092739426774967)
                      ·
                        rfl

theorem cell23_5115344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 7, 2].length) (baseStart_5115344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115344 prefixEnd_5115344 := by exact prefixLift 5115344
  have htrace : WordTrace (prefixWord ++ tailWord_5115344) baseStart_5115344 baseEnd_5115344 := by
    simpa [prefixWord, tailWord_5115344, baseEnd_5115344] using wordTrace_append hprefix tailTrace_5115344
  have hstable : (prefixWord ++ tailWord_5115344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115344).length < 2 ^ (prefixWord ++ tailWord_5115344).sum := by decide
  have hdescent : baseEnd_5115344 < baseStart_5115344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115381 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5115381 : Nat := 118140960795 + 5115381 * 2 ^ 59
def prefixEnd_5115381 : Nat := 4983230072969 + 3 ^ 40 * 5115381 * 2
def baseEnd_5115381 : Nat := 2626649183876955782012297

theorem tailTrace_5115381 : CollatzResearch.WordTrace tailWord_5115381 prefixEnd_5115381 2626649183876955782012297 := by
  unfold tailWord_5115381
  simp only [CollatzResearch.WordTrace]
  refine ⟨186573272680855749366073997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124382181787237166244049331 186573272680855749366073997)
  ·
    refine ⟨69964977255320906012277749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186573272680855749366073997 69964977255320906012277749)
    ·
      refine ⟨6559216617686334938651039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69964977255320906012277749 6559216617686334938651039)
      ·
        refine ⟨9838824926529502407976559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6559216617686334938651039 9838824926529502407976559)
        ·
          refine ⟨14758237389794253611964839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9838824926529502407976559 14758237389794253611964839)
          ·
            refine ⟨22137356084691380417947259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14758237389794253611964839 22137356084691380417947259)
            ·
              refine ⟨33206034127037070626920889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22137356084691380417947259 33206034127037070626920889)
              ·
                refine ⟨24904525595277802970190667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33206034127037070626920889 24904525595277802970190667)
                ·
                  refine ⟨37356788392916704455286001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24904525595277802970190667 37356788392916704455286001)
                  ·
                    refine ⟨28017591294687528341464501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37356788392916704455286001 28017591294687528341464501)
                    ·
                      refine ⟨2626649183876955782012297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28017591294687528341464501 2626649183876955782012297)
                      ·
                        rfl

theorem cell23_5115381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5115381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115381 prefixEnd_5115381 := by exact prefixLift 5115381
  have htrace : WordTrace (prefixWord ++ tailWord_5115381) baseStart_5115381 baseEnd_5115381 := by
    simpa [prefixWord, tailWord_5115381, baseEnd_5115381] using wordTrace_append hprefix tailTrace_5115381
  have hstable : (prefixWord ++ tailWord_5115381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115381).length < 2 ^ (prefixWord ++ tailWord_5115381).sum := by decide
  have hdescent : baseEnd_5115381 < baseStart_5115381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115387 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 6]
def baseStart_5115387 : Nat := 118140960795 + 5115387 * 2 ^ 59
def prefixEnd_5115387 : Nat := 4983230072969 + 3 ^ 40 * 5115387 * 2
def baseEnd_5115387 : Nat := 2626652264760882758537269

theorem tailTrace_5115387 : CollatzResearch.WordTrace tailWord_5115387 prefixEnd_5115387 2626652264760882758537269 := by
  unfold tailWord_5115387
  simp only [CollatzResearch.WordTrace]
  refine ⟨186573491518834012390792415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124382327679222674927194943 186573491518834012390792415)
  ·
    refine ⟨279860237278251018586188623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186573491518834012390792415 279860237278251018586188623)
    ·
      refine ⟨419790355917376527879282935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279860237278251018586188623 419790355917376527879282935)
      ·
        refine ⟨629685533876064791818924403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419790355917376527879282935 629685533876064791818924403)
        ·
          refine ⟨944528300814097187728386605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629685533876064791818924403 944528300814097187728386605)
          ·
            refine ⟨354198112805286445398144977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 944528300814097187728386605 354198112805286445398144977)
            ·
              refine ⟨265648584603964834048608733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354198112805286445398144977 265648584603964834048608733)
              ·
                refine ⟨99618219226486812768228275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265648584603964834048608733 99618219226486812768228275)
                ·
                  refine ⟨149427328839730219152342413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99618219226486812768228275 149427328839730219152342413)
                  ·
                    refine ⟨56035248314898832182128405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149427328839730219152342413 56035248314898832182128405)
                    ·
                      refine ⟨2626652264760882758537269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56035248314898832182128405 2626652264760882758537269)
                      ·
                        rfl

theorem cell23_5115387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_5115387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115387 prefixEnd_5115387 := by exact prefixLift 5115387
  have htrace : WordTrace (prefixWord ++ tailWord_5115387) baseStart_5115387 baseEnd_5115387 := by
    simpa [prefixWord, tailWord_5115387, baseEnd_5115387] using wordTrace_append hprefix tailTrace_5115387
  have hstable : (prefixWord ++ tailWord_5115387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115387).length < 2 ^ (prefixWord ++ tailWord_5115387).sum := by decide
  have hdescent : baseEnd_5115387 < baseStart_5115387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115407 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_5115407 : Nat := 118140960795 + 5115407 * 2 ^ 59
def prefixEnd_5115407 : Nat := 4983230072969 + 3 ^ 40 * 5115407 * 2
def baseEnd_5115407 : Nat := 2626662534373972680287177

theorem tailTrace_5115407 : CollatzResearch.WordTrace tailWord_5115407 prefixEnd_5115407 2626662534373972680287177 := by
  unfold tailWord_5115407
  simp only [CollatzResearch.WordTrace]
  refine ⟨186574220978761555806520475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124382813985841037204346983 186574220978761555806520475)
  ·
    refine ⟨279861331468142333709780713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186574220978761555806520475 279861331468142333709780713)
    ·
      refine ⟨209895998601106750282335535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279861331468142333709780713 209895998601106750282335535)
      ·
        refine ⟨314843997901660125423503303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209895998601106750282335535 314843997901660125423503303)
        ·
          refine ⟨472265996852490188135254955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314843997901660125423503303 472265996852490188135254955)
          ·
            refine ⟨708398995278735282202882433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472265996852490188135254955 708398995278735282202882433)
            ·
              refine ⟨531299246459051461652161825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708398995278735282202882433 531299246459051461652161825)
              ·
                refine ⟨398474434844288596239121369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531299246459051461652161825 398474434844288596239121369)
                ·
                  refine ⟨298855826133216447179341027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 398474434844288596239121369 298855826133216447179341027)
                  ·
                    refine ⟨448283739199824670769011541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 298855826133216447179341027 448283739199824670769011541)
                    ·
                      refine ⟨2626662534373972680287177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 448283739199824670769011541 2626662534373972680287177)
                      ·
                        rfl

theorem cell23_5115407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_5115407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115407 prefixEnd_5115407 := by exact prefixLift 5115407
  have htrace : WordTrace (prefixWord ++ tailWord_5115407) baseStart_5115407 baseEnd_5115407 := by
    simpa [prefixWord, tailWord_5115407, baseEnd_5115407] using wordTrace_append hprefix tailTrace_5115407
  have hstable : (prefixWord ++ tailWord_5115407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115407).length < 2 ^ (prefixWord ++ tailWord_5115407).sum := by decide
  have hdescent : baseEnd_5115407 < baseStart_5115407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115441 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 7, 1, 3]
def baseStart_5115441 : Nat := 118140960795 + 5115441 * 2 ^ 59
def prefixEnd_5115441 : Nat := 4983230072969 + 3 ^ 40 * 5115441 * 2
def baseEnd_5115441 : Nat := 2626679992716225547262021

theorem tailTrace_5115441 : CollatzResearch.WordTrace tailWord_5115441 prefixEnd_5115441 2626679992716225547262021 := by
  unfold tailWord_5115441
  simp only [CollatzResearch.WordTrace]
  refine ⟨186575461060638379613258177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124383640707092253075505451 186575461060638379613258177)
  ·
    refine ⟨139931595795478784709943633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186575461060638379613258177 139931595795478784709943633)
    ·
      refine ⟨104948696846609088532457725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139931595795478784709943633 104948696846609088532457725)
      ·
        refine ⟨39355761317478408199671647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104948696846609088532457725 39355761317478408199671647)
        ·
          refine ⟨59033641976217612299507471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39355761317478408199671647 59033641976217612299507471)
          ·
            refine ⟨88550462964326418449261207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59033641976217612299507471 88550462964326418449261207)
            ·
              refine ⟨132825694446489627673891811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88550462964326418449261207 132825694446489627673891811)
              ·
                refine ⟨199238541669734441510837717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132825694446489627673891811 199238541669734441510837717)
                ·
                  refine ⟨4669653320384400972910259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 199238541669734441510837717 4669653320384400972910259)
                  ·
                    refine ⟨7004479980576601459365389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4669653320384400972910259 7004479980576601459365389)
                    ·
                      refine ⟨2626679992716225547262021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004479980576601459365389 2626679992716225547262021)
                      ·
                        rfl

theorem cell23_5115441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_5115441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115441 prefixEnd_5115441 := by exact prefixLift 5115441
  have htrace : WordTrace (prefixWord ++ tailWord_5115441) baseStart_5115441 baseEnd_5115441 := by
    simpa [prefixWord, tailWord_5115441, baseEnd_5115441] using wordTrace_append hprefix tailTrace_5115441
  have hstable : (prefixWord ++ tailWord_5115441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115441).length < 2 ^ (prefixWord ++ tailWord_5115441).sum := by decide
  have hdescent : baseEnd_5115441 < baseStart_5115441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115491 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 4, 4]
def baseStart_5115491 : Nat := 118140960795 + 5115491 * 2 ^ 59
def prefixEnd_5115491 : Nat := 4983230072969 + 3 ^ 40 * 5115491 * 2
def baseEnd_5115491 : Nat := 875568555582983450545597

theorem tailTrace_5115491 : CollatzResearch.WordTrace tailWord_5115491 prefixEnd_5115491 875568555582983450545597 := by
  unfold tailWord_5115491
  simp only [CollatzResearch.WordTrace]
  refine ⟨186577284710457238152578327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124384856473638158768385551 186577284710457238152578327)
  ·
    refine ⟨279865927065685857228867491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186577284710457238152578327 279865927065685857228867491)
    ·
      refine ⟨419798890598528785843301237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279865927065685857228867491 419798890598528785843301237)
      ·
        refine ⟨39356145993612073672809491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 419798890598528785843301237 39356145993612073672809491)
        ·
          refine ⟨59034218990418110509214237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39356145993612073672809491 59034218990418110509214237)
          ·
            refine ⟨22137832121406791440955339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59034218990418110509214237 22137832121406791440955339)
            ·
              refine ⟨33206748182110187161433009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22137832121406791440955339 33206748182110187161433009)
              ·
                refine ⟨24905061136582640371074757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33206748182110187161433009 24905061136582640371074757)
                ·
                  refine ⟨4669698963109245069576517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24905061136582640371074757 4669698963109245069576517)
                  ·
                    refine ⟨875568555582983450545597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4669698963109245069576517 875568555582983450545597)
                    ·
                      rfl

theorem cell23_5115491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 4].length) (baseStart_5115491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115491 prefixEnd_5115491 := by exact prefixLift 5115491
  have htrace : WordTrace (prefixWord ++ tailWord_5115491) baseStart_5115491 baseEnd_5115491 := by
    simpa [prefixWord, tailWord_5115491, baseEnd_5115491] using wordTrace_append hprefix tailTrace_5115491
  have hstable : (prefixWord ++ tailWord_5115491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115491).length < 2 ^ (prefixWord ++ tailWord_5115491).sum := by decide
  have hdescent : baseEnd_5115491 < baseStart_5115491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115492 : List Nat := [2, 3, 1, 1, 2, 5, 1, 3, 1, 1, 3]
def baseStart_5115492 : Nat := 118140960795 + 5115492 * 2 ^ 59
def prefixEnd_5115492 : Nat := 4983230072969 + 3 ^ 40 * 5115492 * 2
def baseEnd_5115492 : Nat := 2626706180229604847724287

theorem tailTrace_5115492 : CollatzResearch.WordTrace tailWord_5115492 prefixEnd_5115492 2626706180229604847724287 := by
  unfold tailWord_5115492
  simp only [CollatzResearch.WordTrace]
  refine ⟨93288660591726807661682365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124384880788969076882243153 93288660591726807661682365)
  ·
    refine ⟨34983247721897552873130887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93288660591726807661682365 34983247721897552873130887)
    ·
      refine ⟨52474871582846329309696331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34983247721897552873130887 52474871582846329309696331)
      ·
        refine ⟨78712307374269493964544497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52474871582846329309696331 78712307374269493964544497)
        ·
          refine ⟨59034230530702120473408373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78712307374269493964544497 59034230530702120473408373)
          ·
            refine ⟨5534459112253323794382035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 59034230530702120473408373 5534459112253323794382035)
            ·
              refine ⟨8301688668379985691573053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5534459112253323794382035 8301688668379985691573053)
              ·
                refine ⟨3113133250642494634339895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8301688668379985691573053 3113133250642494634339895)
                ·
                  refine ⟨4669699875963741951509843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113133250642494634339895 4669699875963741951509843)
                  ·
                    refine ⟨7004549813945612927264765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4669699875963741951509843 7004549813945612927264765)
                    ·
                      refine ⟨2626706180229604847724287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004549813945612927264765 2626706180229604847724287)
                      ·
                        rfl

theorem cell23_5115492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_5115492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115492 prefixEnd_5115492 := by exact prefixLift 5115492
  have htrace : WordTrace (prefixWord ++ tailWord_5115492) baseStart_5115492 baseEnd_5115492 := by
    simpa [prefixWord, tailWord_5115492, baseEnd_5115492] using wordTrace_append hprefix tailTrace_5115492
  have hstable : (prefixWord ++ tailWord_5115492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115492).length < 2 ^ (prefixWord ++ tailWord_5115492).sum := by decide
  have hdescent : baseEnd_5115492 < baseStart_5115492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115498 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_5115498 : Nat := 118140960795 + 5115498 * 2 ^ 59
def prefixEnd_5115498 : Nat := 4983230072969 + 3 ^ 40 * 5115498 * 2
def baseEnd_5115498 : Nat := 2626709261113531824249259

theorem tailTrace_5115498 : CollatzResearch.WordTrace tailWord_5115498 prefixEnd_5115498 2626709261113531824249259 := by
  unfold tailWord_5115498
  simp only [CollatzResearch.WordTrace]
  refine ⟨46644385005357969587020787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124385026680954585565388765 46644385005357969587020787)
  ·
    refine ⟨69966577508036954380531181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46644385005357969587020787 69966577508036954380531181)
    ·
      refine ⟨26237466565513857892699193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69966577508036954380531181 26237466565513857892699193)
      ·
        refine ⟨19678099924135393419524395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26237466565513857892699193 19678099924135393419524395)
        ·
          refine ⟨29517149886203090129286593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19678099924135393419524395 29517149886203090129286593)
          ·
            refine ⟨22137862414652317596964945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29517149886203090129286593 22137862414652317596964945)
            ·
              refine ⟨16603396810989238197723709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22137862414652317596964945 16603396810989238197723709)
              ·
                refine ⟨6226273804120964324146391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16603396810989238197723709 6226273804120964324146391)
                ·
                  refine ⟨9339410706181446486219587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6226273804120964324146391 9339410706181446486219587)
                  ·
                    refine ⟨14009116059272169729329381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9339410706181446486219587 14009116059272169729329381)
                    ·
                      refine ⟨2626709261113531824249259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14009116059272169729329381 2626709261113531824249259)
                      ·
                        rfl

theorem cell23_5115498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_5115498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115498 prefixEnd_5115498 := by exact prefixLift 5115498
  have htrace : WordTrace (prefixWord ++ tailWord_5115498) baseStart_5115498 baseEnd_5115498 := by
    simpa [prefixWord, tailWord_5115498, baseEnd_5115498] using wordTrace_append hprefix tailTrace_5115498
  have hstable : (prefixWord ++ tailWord_5115498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115498).length < 2 ^ (prefixWord ++ tailWord_5115498).sum := by decide
  have hdescent : baseEnd_5115498 < baseStart_5115498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115504 : List Nat := [2, 1, 1, 1, 6, 1, 11]
def baseStart_5115504 : Nat := 118140960795 + 5115504 * 2 ^ 59
def prefixEnd_5115504 : Nat := 4983230072969 + 3 ^ 40 * 5115504 * 2
def baseEnd_5115504 : Nat := 32428547432067392602151

theorem tailTrace_5115504 : CollatzResearch.WordTrace tailWord_5115504 prefixEnd_5115504 32428547432067392602151 := by
  unfold tailWord_5115504
  simp only [CollatzResearch.WordTrace]
  refine ⟨93288879429705070686400783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124385172572940094248534377 93288879429705070686400783)
  ·
    refine ⟨139933319144557606029601175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93288879429705070686400783 139933319144557606029601175)
    ·
      refine ⟨209899978716836409044401763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139933319144557606029601175 209899978716836409044401763)
      ·
        refine ⟨314849968075254613566602645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209899978716836409044401763 314849968075254613566602645)
        ·
          refine ⟨14758592253527560010934499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 314849968075254613566602645 14758592253527560010934499)
          ·
            refine ⟨22137888380291340016401749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14758592253527560010934499 22137888380291340016401749)
            ·
              refine ⟨32428547432067392602151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22137888380291340016401749 32428547432067392602151)
              ·
                rfl

theorem cell23_5115504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 11].length) (baseStart_5115504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115504 prefixEnd_5115504 := by exact prefixLift 5115504
  have htrace : WordTrace (prefixWord ++ tailWord_5115504) baseStart_5115504 baseEnd_5115504 := by
    simpa [prefixWord, tailWord_5115504, baseEnd_5115504] using wordTrace_append hprefix tailTrace_5115504
  have hstable : (prefixWord ++ tailWord_5115504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115504).length < 2 ^ (prefixWord ++ tailWord_5115504).sum := by decide
  have hdescent : baseEnd_5115504 < baseStart_5115504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115509 : List Nat := [1, 3, 4, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_5115509 : Nat := 118140960795 + 5115509 * 2 ^ 59
def prefixEnd_5115509 : Nat := 4983230072969 + 3 ^ 40 * 5115509 * 2
def baseEnd_5115509 : Nat := 2626714909400731281211709

theorem tailTrace_5115509 : CollatzResearch.WordTrace tailWord_5115509 prefixEnd_5115509 2626714909400731281211709 := by
  unfold tailWord_5115509
  simp only [CollatzResearch.WordTrace]
  refine ⟨186577941224392027226733581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124385294149594684817822387 186577941224392027226733581)
  ·
    refine ⟨69966727959147010210025093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186577941224392027226733581 69966727959147010210025093)
    ·
      refine ⟨13118761492340064414379705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69966727959147010210025093 13118761492340064414379705)
      ·
        refine ⟨9839071119255048310784779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13118761492340064414379705 9839071119255048310784779)
        ·
          refine ⟨14758606678882572466177169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9839071119255048310784779 14758606678882572466177169)
          ·
            refine ⟨11068955009161929349632877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14758606678882572466177169 11068955009161929349632877)
            ·
              refine ⟨4150858128435723506112329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11068955009161929349632877 4150858128435723506112329)
              ·
                refine ⟨3113143596326792629584247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4150858128435723506112329 3113143596326792629584247)
                ·
                  refine ⟨4669715394490188944376371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113143596326792629584247 4669715394490188944376371)
                  ·
                    refine ⟨7004573091735283416564557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4669715394490188944376371 7004573091735283416564557)
                    ·
                      refine ⟨2626714909400731281211709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004573091735283416564557 2626714909400731281211709)
                      ·
                        rfl

theorem cell23_5115509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_5115509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115509 prefixEnd_5115509 := by exact prefixLift 5115509
  have htrace : WordTrace (prefixWord ++ tailWord_5115509) baseStart_5115509 baseEnd_5115509 := by
    simpa [prefixWord, tailWord_5115509, baseEnd_5115509] using wordTrace_append hprefix tailTrace_5115509
  have hstable : (prefixWord ++ tailWord_5115509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115509).length < 2 ^ (prefixWord ++ tailWord_5115509).sum := by decide
  have hdescent : baseEnd_5115509 < baseStart_5115509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115521 : List Nat := [1, 2, 4, 2, 1, 3, 2, 8]
def baseStart_5115521 : Nat := 118140960795 + 5115521 * 2 ^ 59
def prefixEnd_5115521 : Nat := 4983230072969 + 3 ^ 40 * 5115521 * 2
def baseEnd_5115521 : Nat := 97285965598836490157839

theorem tailTrace_5115521 : CollatzResearch.WordTrace tailWord_5115521 prefixEnd_5115521 97285965598836490157839 := by
  unfold tailWord_5115521
  simp only [CollatzResearch.WordTrace]
  refine ⟨186578378900348553276170417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124385585933565702184113611 186578378900348553276170417)
  ·
    refine ⟨139933784175261414957127813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186578378900348553276170417 139933784175261414957127813)
    ·
      refine ⟨26237584532861515304461465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139933784175261414957127813 26237584532861515304461465)
      ·
        refine ⟨19678188399646136478346099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26237584532861515304461465 19678188399646136478346099)
        ·
          refine ⟨29517282599469204717519149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19678188399646136478346099 29517282599469204717519149)
          ·
            refine ⟨11068980974800951769069681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29517282599469204717519149 11068980974800951769069681)
            ·
              refine ⟨8301735731100713826802261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11068980974800951769069681 8301735731100713826802261)
              ·
                refine ⟨97285965598836490157839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8301735731100713826802261 97285965598836490157839)
                ·
                  rfl

theorem cell23_5115521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 8].length) (baseStart_5115521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115521 prefixEnd_5115521 := by exact prefixLift 5115521
  have htrace : WordTrace (prefixWord ++ tailWord_5115521) baseStart_5115521 baseEnd_5115521 := by
    simpa [prefixWord, tailWord_5115521, baseEnd_5115521] using wordTrace_append hprefix tailTrace_5115521
  have hstable : (prefixWord ++ tailWord_5115521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115521).length < 2 ^ (prefixWord ++ tailWord_5115521).sum := by decide
  have hdescent : baseEnd_5115521 < baseStart_5115521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115531 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 3]
def baseStart_5115531 : Nat := 118140960795 + 5115531 * 2 ^ 59
def prefixEnd_5115531 : Nat := 4983230072969 + 3 ^ 40 * 5115531 * 2
def baseEnd_5115531 : Nat := 2626726205975130195136607

theorem tailTrace_5115531 : CollatzResearch.WordTrace tailWord_5115531 prefixEnd_5115531 2626726205975130195136607 := by
  unfold tailWord_5115531
  simp only [CollatzResearch.WordTrace]
  refine ⟨186578743630312324984034447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124385829086874883322689631 186578743630312324984034447)
  ·
    refine ⟨279868115445468487476051671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186578743630312324984034447 279868115445468487476051671)
    ·
      refine ⟨419802173168202731214077507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279868115445468487476051671 419802173168202731214077507)
      ·
        refine ⟨629703259752304096821116261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419802173168202731214077507 629703259752304096821116261)
        ·
          refine ⟨118069361203557018153959299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 629703259752304096821116261 118069361203557018153959299)
          ·
            refine ⟨177104041805335527230938949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118069361203557018153959299 177104041805335527230938949)
            ·
              refine ⟨33207007838500411355801053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177104041805335527230938949 33207007838500411355801053)
              ·
                refine ⟨12452627939437654258425395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33207007838500411355801053 12452627939437654258425395)
                ·
                  refine ⟨18678941909156481387638093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12452627939437654258425395 18678941909156481387638093)
                  ·
                    refine ⟨7004603215933680520364285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18678941909156481387638093 7004603215933680520364285)
                    ·
                      refine ⟨2626726205975130195136607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004603215933680520364285 2626726205975130195136607)
                      ·
                        rfl

theorem cell23_5115531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 3].length) (baseStart_5115531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115531 prefixEnd_5115531 := by exact prefixLift 5115531
  have htrace : WordTrace (prefixWord ++ tailWord_5115531) baseStart_5115531 baseEnd_5115531 := by
    simpa [prefixWord, tailWord_5115531, baseEnd_5115531] using wordTrace_append hprefix tailTrace_5115531
  have hstable : (prefixWord ++ tailWord_5115531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115531).length < 2 ^ (prefixWord ++ tailWord_5115531).sum := by decide
  have hdescent : baseEnd_5115531 < baseStart_5115531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115560 : List Nat := [2, 1, 7, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_5115560 : Nat := 118140960795 + 5115560 * 2 ^ 59
def prefixEnd_5115560 : Nat := 4983230072969 + 3 ^ 40 * 5115560 * 2
def baseEnd_5115560 : Nat := 2626741096914110581673975

theorem tailTrace_5115560 : CollatzResearch.WordTrace tailWord_5115560 prefixEnd_5115560 2626741096914110581673975 := by
  unfold tailWord_5115560
  simp only [CollatzResearch.WordTrace]
  refine ⟨93289900673603631468420067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124386534231471508624560089 93289900673603631468420067)
  ·
    refine ⟨139934851010405447202630101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93289900673603631468420067 139934851010405447202630101)
    ·
      refine ⟨3279723070556377668811643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 139934851010405447202630101 3279723070556377668811643)
      ·
        refine ⟨4919584605834566503217465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3279723070556377668811643 4919584605834566503217465)
        ·
          refine ⟨3689688454375924877413099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4919584605834566503217465 3689688454375924877413099)
          ·
            refine ⟨5534532681563887316119649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3689688454375924877413099 5534532681563887316119649)
            ·
              refine ⟨4150899511172915487089737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5534532681563887316119649 4150899511172915487089737)
              ·
                refine ⟨3113174633379686615317303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4150899511172915487089737 3113174633379686615317303)
                ·
                  refine ⟨4669761950069529922975955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113174633379686615317303 4669761950069529922975955)
                  ·
                    refine ⟨7004642925104294884463933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4669761950069529922975955 7004642925104294884463933)
                    ·
                      refine ⟨2626741096914110581673975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004642925104294884463933 2626741096914110581673975)
                      ·
                        rfl

theorem cell23_5115560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_5115560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115560 prefixEnd_5115560 := by exact prefixLift 5115560
  have htrace : WordTrace (prefixWord ++ tailWord_5115560) baseStart_5115560 baseEnd_5115560 := by
    simpa [prefixWord, tailWord_5115560, baseEnd_5115560] using wordTrace_append hprefix tailTrace_5115560
  have hstable : (prefixWord ++ tailWord_5115560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115560).length < 2 ^ (prefixWord ++ tailWord_5115560).sum := by decide
  have hdescent : baseEnd_5115560 < baseStart_5115560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115564 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_5115564 : Nat := 118140960795 + 5115564 * 2 ^ 59
def prefixEnd_5115564 : Nat := 4983230072969 + 3 ^ 40 * 5115564 * 2
def baseEnd_5115564 : Nat := 875581050278909522007985

theorem tailTrace_5115564 : CollatzResearch.WordTrace tailWord_5115564 prefixEnd_5115564 875581050278909522007985 := by
  unfold tailWord_5115564
  simp only [CollatzResearch.WordTrace]
  refine ⟨93289973619596385809992873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124386631492795181079990497 93289973619596385809992873)
  ·
    refine ⟨69967480214697289357494655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93289973619596385809992873 69967480214697289357494655)
    ·
      refine ⟨104951220322045934036241983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69967480214697289357494655 104951220322045934036241983)
      ·
        refine ⟨157426830483068901054362975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104951220322045934036241983 157426830483068901054362975)
        ·
          refine ⟨236140245724603351581544463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157426830483068901054362975 236140245724603351581544463)
          ·
            refine ⟨354210368586905027372316695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236140245724603351581544463 354210368586905027372316695)
            ·
              refine ⟨531315552880357541058475043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354210368586905027372316695 531315552880357541058475043)
              ·
                refine ⟨796973329320536311587712565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531315552880357541058475043 796973329320536311587712565)
                ·
                  refine ⟨74716249623800279211348053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 796973329320536311587712565 74716249623800279211348053)
                  ·
                    refine ⟨875581050278909522007985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74716249623800279211348053 875581050278909522007985)
                    ·
                      rfl

theorem cell23_5115564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_5115564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115564 prefixEnd_5115564 := by exact prefixLift 5115564
  have htrace : WordTrace (prefixWord ++ tailWord_5115564) baseStart_5115564 baseEnd_5115564 := by
    simpa [prefixWord, tailWord_5115564, baseEnd_5115564] using wordTrace_append hprefix tailTrace_5115564
  have hstable : (prefixWord ++ tailWord_5115564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115564).length < 2 ^ (prefixWord ++ tailWord_5115564).sum := by decide
  have hdescent : baseEnd_5115564 < baseStart_5115564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115566 : List Nat := [4, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_5115566 : Nat := 118140960795 + 5115566 * 2 ^ 59
def prefixEnd_5115566 : Nat := 4983230072969 + 3 ^ 40 * 5115566 * 2
def baseEnd_5115566 : Nat := 2626744177798037558198947

theorem tailTrace_5115566 : CollatzResearch.WordTrace tailWord_5115566 prefixEnd_5115566 2626744177798037558198947 := by
  unfold tailWord_5115566
  simp only [CollatzResearch.WordTrace]
  refine ⟨23322502523148190745194819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124386680123457017307705701 23322502523148190745194819)
  ·
    refine ⟨34983753784722286117792229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23322502523148190745194819 34983753784722286117792229)
    ·
      refine ⟨6559453834635428647086043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34983753784722286117792229 6559453834635428647086043)
      ·
        refine ⟨9839180751953142970629065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6559453834635428647086043 9839180751953142970629065)
        ·
          refine ⟨7379385563964857227971799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9839180751953142970629065 7379385563964857227971799)
          ·
            refine ⟨11069078345947285841957699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7379385563964857227971799 11069078345947285841957699)
            ·
              refine ⟨16603617518920928762936549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11069078345947285841957699 16603617518920928762936549)
              ·
                refine ⟨3113178284797674143050603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16603617518920928762936549 3113178284797674143050603)
                ·
                  refine ⟨4669767427196511214575905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113178284797674143050603 4669767427196511214575905)
                  ·
                    refine ⟨3502325570397383410931929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4669767427196511214575905 3502325570397383410931929)
                    ·
                      refine ⟨2626744177798037558198947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502325570397383410931929 2626744177798037558198947)
                      ·
                        rfl

theorem cell23_5115566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_5115566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115566 prefixEnd_5115566 := by exact prefixLift 5115566
  have htrace : WordTrace (prefixWord ++ tailWord_5115566) baseStart_5115566 baseEnd_5115566 := by
    simpa [prefixWord, tailWord_5115566, baseEnd_5115566] using wordTrace_append hprefix tailTrace_5115566
  have hstable : (prefixWord ++ tailWord_5115566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115566).length < 2 ^ (prefixWord ++ tailWord_5115566).sum := by decide
  have hdescent : baseEnd_5115566 < baseStart_5115566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115581 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_5115581 : Nat := 118140960795 + 5115581 * 2 ^ 59
def prefixEnd_5115581 : Nat := 4983230072969 + 3 ^ 40 * 5115581 * 2
def baseEnd_5115581 : Nat := 875583960002618333170459

theorem tailTrace_5115581 : CollatzResearch.WordTrace tailWord_5115581 prefixEnd_5115581 875583960002618333170459 := by
  unfold tailWord_5115581
  simp only [CollatzResearch.WordTrace]
  refine ⟨186580567280131183523354597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124387044853420789015569731 186580567280131183523354597)
  ·
    refine ⟨34983856365024596910628987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186580567280131183523354597 34983856365024596910628987)
    ·
      refine ⟨52475784547536895365943481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34983856365024596910628987 52475784547536895365943481)
      ·
        refine ⟨39356838410652671524457611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52475784547536895365943481 39356838410652671524457611)
        ·
          refine ⟨59035257615979007286686417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39356838410652671524457611 59035257615979007286686417)
          ·
            refine ⟨44276443211984255465014813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59035257615979007286686417 44276443211984255465014813)
            ·
              refine ⟨16603666204494095799380555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44276443211984255465014813 16603666204494095799380555)
              ·
                refine ⟨24905499306741143699070833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16603666204494095799380555 24905499306741143699070833)
                ·
                  refine ⟨18679124480055857774303125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24905499306741143699070833 18679124480055857774303125)
                  ·
                    refine ⟨875583960002618333170459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18679124480055857774303125 875583960002618333170459)
                    ·
                      rfl

theorem cell23_5115581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_5115581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115581 prefixEnd_5115581 := by exact prefixLift 5115581
  have htrace : WordTrace (prefixWord ++ tailWord_5115581) baseStart_5115581 baseEnd_5115581 := by
    simpa [prefixWord, tailWord_5115581, baseEnd_5115581] using wordTrace_append hprefix tailTrace_5115581
  have hstable : (prefixWord ++ tailWord_5115581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115581).length < 2 ^ (prefixWord ++ tailWord_5115581).sum := by decide
  have hdescent : baseEnd_5115581 < baseStart_5115581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115591 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 3]
def baseStart_5115591 : Nat := 118140960795 + 5115591 * 2 ^ 59
def prefixEnd_5115591 : Nat := 4983230072969 + 3 ^ 40 * 5115591 * 2
def baseEnd_5115591 : Nat := 2626757014814399960386331

theorem tailTrace_5115591 : CollatzResearch.WordTrace tailWord_5115591 prefixEnd_5115591 2626757014814399960386331 := by
  unfold tailWord_5115591
  simp only [CollatzResearch.WordTrace]
  refine ⟨186580932010094955231218627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124387288006729970154145751 186580932010094955231218627)
  ·
    refine ⟨279871398015142432846827941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186580932010094955231218627 279871398015142432846827941)
    ·
      refine ⟨52475887127839206158780239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279871398015142432846827941 52475887127839206158780239)
      ·
        refine ⟨78713830691758809238170359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52475887127839206158780239 78713830691758809238170359)
        ·
          refine ⟨118070746037638213857255539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78713830691758809238170359 118070746037638213857255539)
          ·
            refine ⟨177106119056457320785883309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118070746037638213857255539 177106119056457320785883309)
            ·
              refine ⟨66414794646171495294706241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177106119056457320785883309 66414794646171495294706241)
              ·
                refine ⟨49811095984628621471029681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66414794646171495294706241 49811095984628621471029681)
                ·
                  refine ⟨37358321988471466103272261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49811095984628621471029681 37358321988471466103272261)
                  ·
                    refine ⟨7004685372838399894363549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37358321988471466103272261 7004685372838399894363549)
                    ·
                      refine ⟨2626757014814399960386331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004685372838399894363549 2626757014814399960386331)
                      ·
                        rfl

theorem cell23_5115591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_5115591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115591 prefixEnd_5115591 := by exact prefixLift 5115591
  have htrace : WordTrace (prefixWord ++ tailWord_5115591) baseStart_5115591 baseEnd_5115591 := by
    simpa [prefixWord, tailWord_5115591, baseEnd_5115591] using wordTrace_append hprefix tailTrace_5115591
  have hstable : (prefixWord ++ tailWord_5115591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115591).length < 2 ^ (prefixWord ++ tailWord_5115591).sum := by decide
  have hdescent : baseEnd_5115591 < baseStart_5115591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115628 : List Nat := [2, 2, 1, 1, 2, 2, 4, 4, 5]
def baseStart_5115628 : Nat := 118140960795 + 5115628 * 2 ^ 59
def prefixEnd_5115628 : Nat := 4983230072969 + 3 ^ 40 * 5115628 * 2
def baseEnd_5115628 : Nat := 291864001510957368402629

theorem tailTrace_5115628 : CollatzResearch.WordTrace tailWord_5115628 prefixEnd_5115628 291864001510957368402629 := by
  unfold tailWord_5115628
  simp only [CollatzResearch.WordTrace]
  refine ⟨93291140755480455275157769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124388187673973940366877025 93291140755480455275157769)
  ·
    refine ⟨69968355566610341456368327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93291140755480455275157769 69968355566610341456368327)
    ·
      refine ⟨104952533349915512184552491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69968355566610341456368327 104952533349915512184552491)
      ·
        refine ⟨157428800024873268276828737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104952533349915512184552491 157428800024873268276828737)
        ·
          refine ⟨118071600018654951207621553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157428800024873268276828737 118071600018654951207621553)
          ·
            refine ⟨88553700013991213405716165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118071600018654951207621553 88553700013991213405716165)
            ·
              refine ⟨16603818752623352513571781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88553700013991213405716165 16603818752623352513571781)
              ·
                refine ⟨3113216016116878596294709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16603818752623352513571781 3113216016116878596294709)
                ·
                  refine ⟨291864001510957368402629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3113216016116878596294709 291864001510957368402629)
                  ·
                    rfl

theorem cell23_5115628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_5115628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115628 prefixEnd_5115628 := by exact prefixLift 5115628
  have htrace : WordTrace (prefixWord ++ tailWord_5115628) baseStart_5115628 baseEnd_5115628 := by
    simpa [prefixWord, tailWord_5115628, baseEnd_5115628] using wordTrace_append hprefix tailTrace_5115628
  have hstable : (prefixWord ++ tailWord_5115628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115628).length < 2 ^ (prefixWord ++ tailWord_5115628).sum := by decide
  have hdescent : baseEnd_5115628 < baseStart_5115628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115715 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 3]
def baseStart_5115715 : Nat := 118140960795 + 5115715 * 2 ^ 59
def prefixEnd_5115715 : Nat := 4983230072969 + 3 ^ 40 * 5115715 * 2
def baseEnd_5115715 : Nat := 2626820686415557475235761

theorem tailTrace_5115715 : CollatzResearch.WordTrace tailWord_5115715 prefixEnd_5115715 2626820686415557475235761 := by
  unfold tailWord_5115715
  simp only [CollatzResearch.WordTrace]
  refine ⟨186585454661645724408732599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124390303107763816272488399 186585454661645724408732599)
  ·
    refine ⟨279878181992468586613098899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186585454661645724408732599 279878181992468586613098899)
    ·
      refine ⟨419817272988702879919648349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279878181992468586613098899 419817272988702879919648349)
      ·
        refine ⟨157431477370763579969868131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419817272988702879919648349 157431477370763579969868131)
        ·
          refine ⟨236147216056145369954802197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157431477370763579969868131 236147216056145369954802197)
          ·
            refine ⟨11069400752631814216631353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 236147216056145369954802197 11069400752631814216631353)
            ·
              refine ⟨8302050564473860662473515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11069400752631814216631353 8302050564473860662473515)
              ·
                refine ⟨12453075846710790993710273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8302050564473860662473515 12453075846710790993710273)
                ·
                  refine ⟨9339806885033093245282705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12453075846710790993710273 9339806885033093245282705)
                  ·
                    refine ⟨7004855163774819933962029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9339806885033093245282705 7004855163774819933962029)
                    ·
                      refine ⟨2626820686415557475235761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004855163774819933962029 2626820686415557475235761)
                      ·
                        rfl

theorem cell23_5115715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 3].length) (baseStart_5115715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115715 prefixEnd_5115715 := by exact prefixLift 5115715
  have htrace : WordTrace (prefixWord ++ tailWord_5115715) baseStart_5115715 baseEnd_5115715 := by
    simpa [prefixWord, tailWord_5115715, baseEnd_5115715] using wordTrace_append hprefix tailTrace_5115715
  have hstable : (prefixWord ++ tailWord_5115715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115715).length < 2 ^ (prefixWord ++ tailWord_5115715).sum := by decide
  have hdescent : baseEnd_5115715 < baseStart_5115715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115735 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 6]
def baseStart_5115735 : Nat := 118140960795 + 5115735 * 2 ^ 59
def prefixEnd_5115735 : Nat := 4983230072969 + 3 ^ 40 * 5115735 * 2
def baseEnd_5115735 : Nat := 291870106225405266331741

theorem tailTrace_5115735 : CollatzResearch.WordTrace tailWord_5115735 prefixEnd_5115735 291870106225405266331741 := by
  unfold tailWord_5115735
  simp only [CollatzResearch.WordTrace]
  refine ⟨186586184121573267824460659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124390789414382178549640439 186586184121573267824460659)
  ·
    refine ⟨279879276182359901736690989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186586184121573267824460659 279879276182359901736690989)
    ·
      refine ⟨104954728568384963151259121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279879276182359901736690989 104954728568384963151259121)
      ·
        refine ⟨78716046426288722363444341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104954728568384963151259121 78716046426288722363444341)
        ·
          refine ⟨7379629352464567721572907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78716046426288722363444341 7379629352464567721572907)
          ·
            refine ⟨11069444028696851582359361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7379629352464567721572907 11069444028696851582359361)
            ·
              refine ⟨8302083021522638686769521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11069444028696851582359361 8302083021522638686769521)
              ·
                refine ⟨6226562266141979015077141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8302083021522638686769521 6226562266141979015077141)
                ·
                  refine ⟨291870106225405266331741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6226562266141979015077141 291870106225405266331741)
                  ·
                    rfl

theorem cell23_5115735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 6].length) (baseStart_5115735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115735 prefixEnd_5115735 := by exact prefixLift 5115735
  have htrace : WordTrace (prefixWord ++ tailWord_5115735) baseStart_5115735 baseEnd_5115735 := by
    simpa [prefixWord, tailWord_5115735, baseEnd_5115735] using wordTrace_append hprefix tailTrace_5115735
  have hstable : (prefixWord ++ tailWord_5115735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115735).length < 2 ^ (prefixWord ++ tailWord_5115735).sum := by decide
  have hdescent : baseEnd_5115735 < baseStart_5115735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115745 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 3, 1, 3]
def baseStart_5115745 : Nat := 118140960795 + 5115745 * 2 ^ 59
def prefixEnd_5115745 : Nat := 4983230072969 + 3 ^ 40 * 5115745 * 2
def baseEnd_5115745 : Nat := 2626836090835192357860623

theorem tailTrace_5115745 : CollatzResearch.WordTrace tailWord_5115745 prefixEnd_5115745 2626836090835192357860623 := by
  unfold tailWord_5115745
  simp only [CollatzResearch.WordTrace]
  refine ⟨186586548851537039532324689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124391032567691359688216459 186586548851537039532324689)
  ·
    refine ⟨139939911638652779649243517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186586548851537039532324689 139939911638652779649243517)
    ·
      refine ⟨52477466864494792368466319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139939911638652779649243517 52477466864494792368466319)
      ·
        refine ⟨78716200296742188552699479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52477466864494792368466319 78716200296742188552699479)
        ·
          refine ⟨118074300445113282829049219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78716200296742188552699479 118074300445113282829049219)
          ·
            refine ⟨177111450667669924243573829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118074300445113282829049219 177111450667669924243573829)
            ·
              refine ⟨33208397000188110795670093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177111450667669924243573829 33208397000188110795670093)
              ·
                refine ⟨12453148875070541548376285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33208397000188110795670093 12453148875070541548376285)
                ·
                  refine ⟨4669930828151453080641107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12453148875070541548376285 4669930828151453080641107)
                  ·
                    refine ⟨7004896242227179620961661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4669930828151453080641107 7004896242227179620961661)
                    ·
                      refine ⟨2626836090835192357860623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004896242227179620961661 2626836090835192357860623)
                      ·
                        rfl

theorem cell23_5115745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_5115745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115745 prefixEnd_5115745 := by exact prefixLift 5115745
  have htrace : WordTrace (prefixWord ++ tailWord_5115745) baseStart_5115745 baseEnd_5115745 := by
    simpa [prefixWord, tailWord_5115745, baseEnd_5115745] using wordTrace_append hprefix tailTrace_5115745
  have hstable : (prefixWord ++ tailWord_5115745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115745).length < 2 ^ (prefixWord ++ tailWord_5115745).sum := by decide
  have hdescent : baseEnd_5115745 < baseStart_5115745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115765 : List Nat := [1, 3, 4, 1, 1, 1, 2, 4, 1, 5]
def baseStart_5115765 : Nat := 118140960795 + 5115765 * 2 ^ 59
def prefixEnd_5115765 : Nat := 4983230072969 + 3 ^ 40 * 5115765 * 2
def baseEnd_5115765 : Nat := 875615453482760759870177

theorem tailTrace_5115765 : CollatzResearch.WordTrace tailWord_5115765 prefixEnd_5115765 875615453482760759870177 := by
  unfold tailWord_5115765
  simp only [CollatzResearch.WordTrace]
  refine ⟨186587278311464582948052749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124391518874309721965368499 186587278311464582948052749)
  ·
    refine ⟨69970229366799218605519781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186587278311464582948052749 69970229366799218605519781)
    ·
      refine ⟨13119418006274853488534959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69970229366799218605519781 13119418006274853488534959)
      ·
        refine ⟨19679127009412280232802439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13119418006274853488534959 19679127009412280232802439)
        ·
          refine ⟨29518690514118420349203659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19679127009412280232802439 29518690514118420349203659)
          ·
            refine ⟨44278035771177630523805489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29518690514118420349203659 44278035771177630523805489)
            ·
              refine ⟨33208526828383222892854117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44278035771177630523805489 33208526828383222892854117)
              ·
                refine ⟨6226598780321854292410147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33208526828383222892854117 6226598780321854292410147)
                ·
                  refine ⟨9339898170482781438615221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6226598780321854292410147 9339898170482781438615221)
                  ·
                    refine ⟨875615453482760759870177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9339898170482781438615221 875615453482760759870177)
                    ·
                      rfl

theorem cell23_5115765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_5115765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115765 prefixEnd_5115765 := by exact prefixLift 5115765
  have htrace : WordTrace (prefixWord ++ tailWord_5115765) baseStart_5115765 baseEnd_5115765 := by
    simpa [prefixWord, tailWord_5115765, baseEnd_5115765] using wordTrace_append hprefix tailTrace_5115765
  have hstable : (prefixWord ++ tailWord_5115765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115765).length < 2 ^ (prefixWord ++ tailWord_5115765).sum := by decide
  have hdescent : baseEnd_5115765 < baseStart_5115765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115766 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5115766 : Nat := 118140960795 + 5115766 * 2 ^ 59
def prefixEnd_5115766 : Nat := 4983230072969 + 3 ^ 40 * 5115766 * 2
def baseEnd_5115766 : Nat := 2626846873928936775698027

theorem tailTrace_5115766 : CollatzResearch.WordTrace tailWord_5115766 prefixEnd_5115766 2626846873928936775698027 := by
  unfold tailWord_5115766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11661707174028810007427447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124391543189640640079226101 11661707174028810007427447)
  ·
    refine ⟨17492560761043215011141171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11661707174028810007427447 17492560761043215011141171)
    ·
      refine ⟨26238841141564822516711757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17492560761043215011141171 26238841141564822516711757)
      ·
        refine ⟨9839565428086808443766909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26238841141564822516711757 9839565428086808443766909)
        ·
          refine ⟨3689837035532553166412591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9839565428086808443766909 3689837035532553166412591)
          ·
            refine ⟨5534755553298829749618887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3689837035532553166412591 5534755553298829749618887)
            ·
              refine ⟨8302133329948244624428331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5534755553298829749618887 8302133329948244624428331)
              ·
                refine ⟨12453199994922366936642497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8302133329948244624428331 12453199994922366936642497)
                ·
                  refine ⟨9339899996191775202481873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12453199994922366936642497 9339899996191775202481873)
                  ·
                    refine ⟨7004924997143831401861405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9339899996191775202481873 7004924997143831401861405)
                    ·
                      refine ⟨2626846873928936775698027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004924997143831401861405 2626846873928936775698027)
                      ·
                        rfl

theorem cell23_5115766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5115766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115766 prefixEnd_5115766 := by exact prefixLift 5115766
  have htrace : WordTrace (prefixWord ++ tailWord_5115766) baseStart_5115766 baseEnd_5115766 := by
    simpa [prefixWord, tailWord_5115766, baseEnd_5115766] using wordTrace_append hprefix tailTrace_5115766
  have hstable : (prefixWord ++ tailWord_5115766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115766).length < 2 ^ (prefixWord ++ tailWord_5115766).sum := by decide
  have hdescent : baseEnd_5115766 < baseStart_5115766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115779 : List Nat := [1, 1, 1, 3, 4, 3, 2, 3, 1, 1, 3]
def baseStart_5115779 : Nat := 118140960795 + 5115779 * 2 ^ 59
def prefixEnd_5115779 : Nat := 4983230072969 + 3 ^ 40 * 5115779 * 2
def baseEnd_5115779 : Nat := 2626853549177445224835467

theorem tailTrace_5115779 : CollatzResearch.WordTrace tailWord_5115779 prefixEnd_5115779 2626853549177445224835467 := by
  unfold tailWord_5115779
  simp only [CollatzResearch.WordTrace]
  refine ⟨186587788933413863339062391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124391859288942575559374927 186587788933413863339062391)
  ·
    refine ⟨279881683400120795008593587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186587788933413863339062391 279881683400120795008593587)
    ·
      refine ⟨419822525100181192512890381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279881683400120795008593587 419822525100181192512890381)
      ·
        refine ⟨157433446912567947192333893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419822525100181192512890381 157433446912567947192333893)
        ·
          refine ⟨29518771296106490098562605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157433446912567947192333893 29518771296106490098562605)
          ·
            refine ⟨11069539236039933786960977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29518771296106490098562605 11069539236039933786960977)
            ·
              refine ⟨8302154427029950340220733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11069539236039933786960977 8302154427029950340220733)
              ·
                refine ⟨3113307910136231377582775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8302154427029950340220733 3113307910136231377582775)
                ·
                  refine ⟨4669961865204347066374163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113307910136231377582775 4669961865204347066374163)
                  ·
                    refine ⟨7004942797806520599561245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4669961865204347066374163 7004942797806520599561245)
                    ·
                      refine ⟨2626853549177445224835467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7004942797806520599561245 2626853549177445224835467)
                      ·
                        rfl

theorem cell23_5115779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 3, 1, 1, 3].length) (baseStart_5115779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115779 prefixEnd_5115779 := by exact prefixLift 5115779
  have htrace : WordTrace (prefixWord ++ tailWord_5115779) baseStart_5115779 baseEnd_5115779 := by
    simpa [prefixWord, tailWord_5115779, baseEnd_5115779] using wordTrace_append hprefix tailTrace_5115779
  have hstable : (prefixWord ++ tailWord_5115779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115779).length < 2 ^ (prefixWord ++ tailWord_5115779).sum := by decide
  have hdescent : baseEnd_5115779 < baseStart_5115779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115785 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 4]
def baseStart_5115785 : Nat := 118140960795 + 5115785 * 2 ^ 59
def prefixEnd_5115785 : Nat := 4983230072969 + 3 ^ 40 * 5115785 * 2
def baseEnd_5115785 : Nat := 2626856630061372201360439

theorem tailTrace_5115785 : CollatzResearch.WordTrace tailWord_5115785 prefixEnd_5115785 2626856630061372201360439 := by
  unfold tailWord_5115785
  simp only [CollatzResearch.WordTrace]
  refine ⟨186588007771392126363780809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124392005180928084242520539 186588007771392126363780809)
  ·
    refine ⟨139941005828544094772835607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186588007771392126363780809 139941005828544094772835607)
    ·
      refine ⟨209911508742816142159253411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139941005828544094772835607 209911508742816142159253411)
      ·
        refine ⟨314867263114224213238880117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209911508742816142159253411 314867263114224213238880117)
        ·
          refine ⟨29518805916958519991145011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 314867263114224213238880117 29518805916958519991145011)
          ·
            refine ⟨44278208875437779986717517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29518805916958519991145011 44278208875437779986717517)
            ·
              refine ⟨16604328328289167495019069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44278208875437779986717517 16604328328289167495019069)
              ·
                refine ⟨6226623123108437810632151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16604328328289167495019069 6226623123108437810632151)
                ·
                  refine ⟨9339934684662656715948227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6226623123108437810632151 9339934684662656715948227)
                  ·
                    refine ⟨14009902026993985073922341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9339934684662656715948227 14009902026993985073922341)
                    ·
                      refine ⟨2626856630061372201360439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14009902026993985073922341 2626856630061372201360439)
                      ·
                        rfl

theorem cell23_5115785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 4].length) (baseStart_5115785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115785 prefixEnd_5115785 := by exact prefixLift 5115785
  have htrace : WordTrace (prefixWord ++ tailWord_5115785) baseStart_5115785 baseEnd_5115785 := by
    simpa [prefixWord, tailWord_5115785, baseEnd_5115785] using wordTrace_append hprefix tailTrace_5115785
  have hstable : (prefixWord ++ tailWord_5115785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115785).length < 2 ^ (prefixWord ++ tailWord_5115785).sum := by decide
  have hdescent : baseEnd_5115785 < baseStart_5115785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115788 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_5115788 : Nat := 118140960795 + 5115788 * 2 ^ 59
def prefixEnd_5115788 : Nat := 4983230072969 + 3 ^ 40 * 5115788 * 2
def baseEnd_5115788 : Nat := 2626858170503335689622925

theorem tailTrace_5115788 : CollatzResearch.WordTrace tailWord_5115788 prefixEnd_5115788 2626858170503335689622925 := by
  unfold tailWord_5115788
  simp only [CollatzResearch.WordTrace]
  refine ⟨93294058595190628938070009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124392078126920838584093345 93294058595190628938070009)
  ·
    refine ⟨69970543946392971703552507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93294058595190628938070009 69970543946392971703552507)
    ·
      refine ⟨104955815919589457555328761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69970543946392971703552507 104955815919589457555328761)
      ·
        refine ⟨78716861939692093166496571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104955815919589457555328761 78716861939692093166496571)
        ·
          refine ⟨118075292909538139749744857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78716861939692093166496571 118075292909538139749744857)
          ·
            refine ⟨88556469682153604812308643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118075292909538139749744857 88556469682153604812308643)
            ·
              refine ⟨132834704523230407218462965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88556469682153604812308643 132834704523230407218462965)
              ·
                refine ⟨12453253549052850676730903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132834704523230407218462965 12453253549052850676730903)
                ·
                  refine ⟨18679880323579276015096355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12453253549052850676730903 18679880323579276015096355)
                  ·
                    refine ⟨28019820485368914022644533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18679880323579276015096355 28019820485368914022644533)
                    ·
                      refine ⟨2626858170503335689622925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28019820485368914022644533 2626858170503335689622925)
                      ·
                        rfl

theorem cell23_5115788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_5115788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115788 prefixEnd_5115788 := by exact prefixLift 5115788
  have htrace : WordTrace (prefixWord ++ tailWord_5115788) baseStart_5115788 baseEnd_5115788 := by
    simpa [prefixWord, tailWord_5115788, baseEnd_5115788] using wordTrace_append hprefix tailTrace_5115788
  have hstable : (prefixWord ++ tailWord_5115788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115788).length < 2 ^ (prefixWord ++ tailWord_5115788).sum := by decide
  have hdescent : baseEnd_5115788 < baseStart_5115788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115805 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_5115805 : Nat := 118140960795 + 5115805 * 2 ^ 59
def prefixEnd_5115805 : Nat := 4983230072969 + 3 ^ 40 * 5115805 * 2
def baseEnd_5115805 : Nat := 2626866899674462123110347

theorem tailTrace_5115805 : CollatzResearch.WordTrace tailWord_5115805 prefixEnd_5115805 2626866899674462123110347 := by
  unfold tailWord_5115805
  simp only [CollatzResearch.WordTrace]
  refine ⟨186588737231319669779508869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124392491487546446519672579 186588737231319669779508869)
  ·
    refine ⟨34985388230872438083657913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186588737231319669779508869 34985388230872438083657913)
    ·
      refine ⟨26239041173154328562743435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34985388230872438083657913 26239041173154328562743435)
      ·
        refine ⟨39358561759731492844115153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26239041173154328562743435 39358561759731492844115153)
        ·
          refine ⟨29518921319798619633086365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39358561759731492844115153 29518921319798619633086365)
          ·
            refine ⟨11069595494924482362407387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29518921319798619633086365 11069595494924482362407387)
            ·
              refine ⟨16604393242386723543611081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11069595494924482362407387 16604393242386723543611081)
              ·
                refine ⟨12453294931790042657708311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16604393242386723543611081 12453294931790042657708311)
                ·
                  refine ⟨18679942397685063986562467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12453294931790042657708311 18679942397685063986562467)
                  ·
                    refine ⟨28019913596527595979843701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18679942397685063986562467 28019913596527595979843701)
                    ·
                      refine ⟨2626866899674462123110347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28019913596527595979843701 2626866899674462123110347)
                      ·
                        rfl

theorem cell23_5115805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_5115805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115805 prefixEnd_5115805 := by exact prefixLift 5115805
  have htrace : WordTrace (prefixWord ++ tailWord_5115805) baseStart_5115805 baseEnd_5115805 := by
    simpa [prefixWord, tailWord_5115805, baseEnd_5115805] using wordTrace_append hprefix tailTrace_5115805
  have hstable : (prefixWord ++ tailWord_5115805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115805).length < 2 ^ (prefixWord ++ tailWord_5115805).sum := by decide
  have hdescent : baseEnd_5115805 < baseStart_5115805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115815 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 6]
def baseStart_5115815 : Nat := 118140960795 + 5115815 * 2 ^ 59
def prefixEnd_5115815 : Nat := 4983230072969 + 3 ^ 40 * 5115815 * 2
def baseEnd_5115815 : Nat := 2626872034481007083985301

theorem tailTrace_5115815 : CollatzResearch.WordTrace tailWord_5115815 prefixEnd_5115815 2626872034481007083985301 := by
  unfold tailWord_5115815
  simp only [CollatzResearch.WordTrace]
  refine ⟨186589101961283441487372899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124392734640855627658248599 186589101961283441487372899)
  ·
    refine ⟨279883652941925162231059349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186589101961283441487372899 279883652941925162231059349)
    ·
      refine ⟨13119546231652741979580907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 279883652941925162231059349 13119546231652741979580907)
      ·
        refine ⟨19679319347479112969371361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13119546231652741979580907 19679319347479112969371361)
        ·
          refine ⟨14759489510609334727028521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19679319347479112969371361 14759489510609334727028521)
          ·
            refine ⟨11069617132957001045271391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14759489510609334727028521 11069617132957001045271391)
            ·
              refine ⟨16604425699435501567907087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11069617132957001045271391 16604425699435501567907087)
              ·
                refine ⟨24906638549153252351860631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16604425699435501567907087 24906638549153252351860631)
                ·
                  refine ⟨37359957823729878527790947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24906638549153252351860631 37359957823729878527790947)
                  ·
                    refine ⟨56039936735594817791686421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37359957823729878527790947 56039936735594817791686421)
                    ·
                      refine ⟨2626872034481007083985301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56039936735594817791686421 2626872034481007083985301)
                      ·
                        rfl

theorem cell23_5115815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_5115815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115815 prefixEnd_5115815 := by exact prefixLift 5115815
  have htrace : WordTrace (prefixWord ++ tailWord_5115815) baseStart_5115815 baseEnd_5115815 := by
    simpa [prefixWord, tailWord_5115815, baseEnd_5115815] using wordTrace_append hprefix tailTrace_5115815
  have hstable : (prefixWord ++ tailWord_5115815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115815).length < 2 ^ (prefixWord ++ tailWord_5115815).sum := by decide
  have hdescent : baseEnd_5115815 < baseStart_5115815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115825 : List Nat := [1, 2, 2, 4, 2, 1, 4, 7]
def baseStart_5115825 : Nat := 118140960795 + 5115825 * 2 ^ 59
def prefixEnd_5115825 : Nat := 4983230072969 + 3 ^ 40 * 5115825 * 2
def baseEnd_5115825 : Nat := 97291747010650075735565

theorem tailTrace_5115825 : CollatzResearch.WordTrace tailWord_5115825 prefixEnd_5115825 97291747010650075735565 := by
  unfold tailWord_5115825
  simp only [CollatzResearch.WordTrace]
  refine ⟨186589466691247213195236929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124392977794164808796824619 186589466691247213195236929)
  ·
    refine ⟨139942100018435409896427697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186589466691247213195236929 139942100018435409896427697)
    ·
      refine ⟨104956575013826557422320773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139942100018435409896427697 104956575013826557422320773)
      ·
        refine ⟨19679357815092479516685145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104956575013826557422320773 19679357815092479516685145)
        ·
          refine ⟨14759518361319359637513859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19679357815092479516685145 14759518361319359637513859)
          ·
            refine ⟨22139277541979039456270789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14759518361319359637513859 22139277541979039456270789)
            ·
              refine ⟨4151114539121069898050773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22139277541979039456270789 4151114539121069898050773)
              ·
                refine ⟨97291747010650075735565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4151114539121069898050773 97291747010650075735565)
                ·
                  rfl

theorem cell23_5115825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 7].length) (baseStart_5115825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115825 prefixEnd_5115825 := by exact prefixLift 5115825
  have htrace : WordTrace (prefixWord ++ tailWord_5115825) baseStart_5115825 baseEnd_5115825 := by
    simpa [prefixWord, tailWord_5115825, baseEnd_5115825] using wordTrace_append hprefix tailTrace_5115825
  have hstable : (prefixWord ++ tailWord_5115825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115825).length < 2 ^ (prefixWord ++ tailWord_5115825).sum := by decide
  have hdescent : baseEnd_5115825 < baseStart_5115825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115835 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 4, 1, 3]
def baseStart_5115835 : Nat := 118140960795 + 5115835 * 2 ^ 59
def prefixEnd_5115835 : Nat := 4983230072969 + 3 ^ 40 * 5115835 * 2
def baseEnd_5115835 : Nat := 2626882304094097005735209

theorem tailTrace_5115835 : CollatzResearch.WordTrace tailWord_5115835 prefixEnd_5115835 2626882304094097005735209 := by
  unfold tailWord_5115835
  simp only [CollatzResearch.WordTrace]
  refine ⟨186589831421210984903100959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124393220947473989935400639 186589831421210984903100959)
  ·
    refine ⟨279884747131816477354651439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186589831421210984903100959 279884747131816477354651439)
    ·
      refine ⟨419827120697724716031977159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279884747131816477354651439 419827120697724716031977159)
      ·
        refine ⟨629740681046587074047965739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419827120697724716031977159 629740681046587074047965739)
        ·
          refine ⟨944611021569880611071948609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629740681046587074047965739 944611021569880611071948609)
          ·
            refine ⟨708458266177410458303961457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 944611021569880611071948609 708458266177410458303961457)
            ·
              refine ⟨531343699633057843727971093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708458266177410458303961457 531343699633057843727971093)
              ·
                refine ⟨24906735920299586424748645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 531343699633057843727971093 24906735920299586424748645)
                ·
                  refine ⟨4670012985056172454640371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24906735920299586424748645 4670012985056172454640371)
                  ·
                    refine ⟨7005019477584258681960557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4670012985056172454640371 7005019477584258681960557)
                    ·
                      refine ⟨2626882304094097005735209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7005019477584258681960557 2626882304094097005735209)
                      ·
                        rfl

theorem cell23_5115835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 1, 3].length) (baseStart_5115835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115835 prefixEnd_5115835 := by exact prefixLift 5115835
  have htrace : WordTrace (prefixWord ++ tailWord_5115835) baseStart_5115835 baseEnd_5115835 := by
    simpa [prefixWord, tailWord_5115835, baseEnd_5115835] using wordTrace_append hprefix tailTrace_5115835
  have hstable : (prefixWord ++ tailWord_5115835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115835).length < 2 ^ (prefixWord ++ tailWord_5115835).sum := by decide
  have hdescent : baseEnd_5115835 < baseStart_5115835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115852 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 4, 1, 3]
def baseStart_5115852 : Nat := 118140960795 + 5115852 * 2 ^ 59
def prefixEnd_5115852 : Nat := 4983230072969 + 3 ^ 40 * 5115852 * 2
def baseEnd_5115852 : Nat := 2626891033265223439222631

theorem tailTrace_5115852 : CollatzResearch.WordTrace tailWord_5115852 prefixEnd_5115852 2626891033265223439222631 := by
  unfold tailWord_5115852
  simp only [CollatzResearch.WordTrace]
  refine ⟨93295225731074698403234905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124393634308099597870979873 93295225731074698403234905)
  ·
    refine ⟨69971419298306023802426179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93295225731074698403234905 69971419298306023802426179)
    ·
      refine ⟨104957128947459035703639269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69971419298306023802426179 104957128947459035703639269)
      ·
        refine ⟨19679461677648569194432363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104957128947459035703639269 19679461677648569194432363)
        ·
          refine ⟨29519192516472853791648545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19679461677648569194432363 29519192516472853791648545)
          ·
            refine ⟨22139394387354640343736409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29519192516472853791648545 22139394387354640343736409)
            ·
              refine ⟨16604545790515980257802307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22139394387354640343736409 16604545790515980257802307)
              ·
                refine ⟨24906818685773970386703461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16604545790515980257802307 24906818685773970386703461)
                ·
                  refine ⟨4670028503582619447506899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24906818685773970386703461 4670028503582619447506899)
                  ·
                    refine ⟨7005042755373929171260349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4670028503582619447506899 7005042755373929171260349)
                    ·
                      refine ⟨2626891033265223439222631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7005042755373929171260349 2626891033265223439222631)
                      ·
                        rfl

theorem cell23_5115852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_5115852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115852 prefixEnd_5115852 := by exact prefixLift 5115852
  have htrace : WordTrace (prefixWord ++ tailWord_5115852) baseStart_5115852 baseEnd_5115852 := by
    simpa [prefixWord, tailWord_5115852, baseEnd_5115852] using wordTrace_append hprefix tailTrace_5115852
  have hstable : (prefixWord ++ tailWord_5115852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115852).length < 2 ^ (prefixWord ++ tailWord_5115852).sum := by decide
  have hdescent : baseEnd_5115852 < baseStart_5115852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115879 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 3, 3, 2]
def baseStart_5115879 : Nat := 118140960795 + 5115879 * 2 ^ 59
def prefixEnd_5115879 : Nat := 4983230072969 + 3 ^ 40 * 5115879 * 2
def baseEnd_5115879 : Nat := 2626904897242894833585007

theorem tailTrace_5115879 : CollatzResearch.WordTrace tailWord_5115879 prefixEnd_5115879 2626904897242894833585007 := by
  unfold tailWord_5115879
  simp only [CollatzResearch.WordTrace]
  refine ⟨186591436233051580417702691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124394290822034386945135127 186591436233051580417702691)
  ·
    refine ⟨279887154349577370626554037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186591436233051580417702691 279887154349577370626554037)
    ·
      refine ⟨26239420720272878496239441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 279887154349577370626554037 26239420720272878496239441)
      ·
        refine ⟨19679565540204658872179581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26239420720272878496239441 19679565540204658872179581)
        ·
          refine ⟨7379837077576747077067343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19679565540204658872179581 7379837077576747077067343)
          ·
            refine ⟨11069755616365120615601015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7379837077576747077067343 11069755616365120615601015)
            ·
              refine ⟨16604633424547680923401523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11069755616365120615601015 16604633424547680923401523)
              ·
                refine ⟨24906950136821521385102285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16604633424547680923401523 24906950136821521385102285)
                ·
                  refine ⟨9340106301308070519413357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24906950136821521385102285 9340106301308070519413357)
                  ·
                    refine ⟨3502539862990526444780009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9340106301308070519413357 3502539862990526444780009)
                    ·
                      refine ⟨2626904897242894833585007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502539862990526444780009 2626904897242894833585007)
                      ·
                        rfl

theorem cell23_5115879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_5115879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115879 prefixEnd_5115879 := by exact prefixLift 5115879
  have htrace : WordTrace (prefixWord ++ tailWord_5115879) baseStart_5115879 baseEnd_5115879 := by
    simpa [prefixWord, tailWord_5115879, baseEnd_5115879] using wordTrace_append hprefix tailTrace_5115879
  have hstable : (prefixWord ++ tailWord_5115879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115879).length < 2 ^ (prefixWord ++ tailWord_5115879).sum := by decide
  have hdescent : baseEnd_5115879 < baseStart_5115879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115905 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_5115905 : Nat := 118140960795 + 5115905 * 2 ^ 59
def prefixEnd_5115905 : Nat := 4983230072969 + 3 ^ 40 * 5115905 * 2
def baseEnd_5115905 : Nat := 2626918247739911731859887

theorem tailTrace_5115905 : CollatzResearch.WordTrace tailWord_5115905 prefixEnd_5115905 2626918247739911731859887 := by
  unfold tailWord_5115905
  simp only [CollatzResearch.WordTrace]
  refine ⟨186592384530957386858149169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124394923020638257905432779 186592384530957386858149169)
  ·
    refine ⟨139944288398218040143611877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186592384530957386858149169 139944288398218040143611877)
    ·
      refine ⟨26239554074665882526927227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139944288398218040143611877 26239554074665882526927227)
      ·
        refine ⟨39359331111998823790390841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26239554074665882526927227 39359331111998823790390841)
        ·
          refine ⟨29519498333999117842793131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39359331111998823790390841 29519498333999117842793131)
          ·
            refine ⟨44279247500998676764189697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29519498333999117842793131 44279247500998676764189697)
            ·
              refine ⟨33209435625749007573142273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44279247500998676764189697 33209435625749007573142273)
              ·
                refine ⟨24907076719311755679856705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33209435625749007573142273 24907076719311755679856705)
                ·
                  refine ⟨18680307539483816759892529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24907076719311755679856705 18680307539483816759892529)
                  ·
                    refine ⟨14010230654612862569919397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18680307539483816759892529 14010230654612862569919397)
                    ·
                      refine ⟨2626918247739911731859887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14010230654612862569919397 2626918247739911731859887)
                      ·
                        rfl

theorem cell23_5115905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_5115905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115905 prefixEnd_5115905 := by exact prefixLift 5115905
  have htrace : WordTrace (prefixWord ++ tailWord_5115905) baseStart_5115905 baseEnd_5115905 := by
    simpa [prefixWord, tailWord_5115905, baseEnd_5115905] using wordTrace_append hprefix tailTrace_5115905
  have hstable : (prefixWord ++ tailWord_5115905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115905).length < 2 ^ (prefixWord ++ tailWord_5115905).sum := by decide
  have hdescent : baseEnd_5115905 < baseStart_5115905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115909 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 2, 2, 2]
def baseStart_5115909 : Nat := 118140960795 + 5115909 * 2 ^ 59
def prefixEnd_5115909 : Nat := 4983230072969 + 3 ^ 40 * 5115909 * 2
def baseEnd_5115909 : Nat := 2626920301662529716209869

theorem tailTrace_5115909 : CollatzResearch.WordTrace tailWord_5115909 prefixEnd_5115909 2626920301662529716209869 := by
  unfold tailWord_5115909
  simp only [CollatzResearch.WordTrace]
  refine ⟨186592530422942895541294781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124395020281961930360863187 186592530422942895541294781)
  ·
    refine ⟨69972198908603585827985543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186592530422942895541294781 69972198908603585827985543)
    ·
      refine ⟨104958298362905378741978315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69972198908603585827985543 104958298362905378741978315)
      ·
        refine ⟨157437447544358068112967473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104958298362905378741978315 157437447544358068112967473)
        ·
          refine ⟨118078085658268551084725605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157437447544358068112967473 118078085658268551084725605)
          ·
            refine ⟨22139641060925353328386051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118078085658268551084725605 22139641060925353328386051)
            ·
              refine ⟨33209461591388029992579077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22139641060925353328386051 33209461591388029992579077)
              ·
                refine ⟨6226774048385255623608577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33209461591388029992579077 6226774048385255623608577)
                ·
                  refine ⟨4670080536288941717706433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6226774048385255623608577 4670080536288941717706433)
                  ·
                    refine ⟨3502560402216706288279825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4670080536288941717706433 3502560402216706288279825)
                    ·
                      refine ⟨2626920301662529716209869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502560402216706288279825 2626920301662529716209869)
                      ·
                        rfl

theorem cell23_5115909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 2, 2, 2].length) (baseStart_5115909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115909 prefixEnd_5115909 := by exact prefixLift 5115909
  have htrace : WordTrace (prefixWord ++ tailWord_5115909) baseStart_5115909 baseEnd_5115909 := by
    simpa [prefixWord, tailWord_5115909, baseEnd_5115909] using wordTrace_append hprefix tailTrace_5115909
  have hstable : (prefixWord ++ tailWord_5115909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115909).length < 2 ^ (prefixWord ++ tailWord_5115909).sum := by decide
  have hdescent : baseEnd_5115909 < baseStart_5115909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5115992 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 3, 4]
def baseStart_5115992 : Nat := 118140960795 + 5115992 * 2 ^ 59
def prefixEnd_5115992 : Nat := 4983230072969 + 3 ^ 40 * 5115992 * 2
def baseEnd_5115992 : Nat := 875654306852284297157329

theorem tailTrace_5115992 : CollatzResearch.WordTrace tailWord_5115992 prefixEnd_5115992 875654306852284297157329 := by
  unfold tailWord_5115992
  simp only [CollatzResearch.WordTrace]
  refine ⟨93297778840821100358283115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124397038454428133811044153 93297778840821100358283115)
  ·
    refine ⟨139946668261231650537424673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93297778840821100358283115 139946668261231650537424673)
    ·
      refine ⟨104960001195923737903068505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139946668261231650537424673 104960001195923737903068505)
      ·
        refine ⟨78720000896942803427301379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104960001195923737903068505 78720000896942803427301379)
        ·
          refine ⟨118080001345414205140952069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78720000896942803427301379 118080001345414205140952069)
          ·
            refine ⟨22140000252265163463928513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118080001345414205140952069 22140000252265163463928513)
            ·
              refine ⟨16605000189198872597946385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22140000252265163463928513 16605000189198872597946385)
              ·
                refine ⟨12453750141899154448459789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16605000189198872597946385 12453750141899154448459789)
                ·
                  refine ⟨4670156303212182918172421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12453750141899154448459789 4670156303212182918172421)
                  ·
                    refine ⟨875654306852284297157329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4670156303212182918172421 875654306852284297157329)
                    ·
                      rfl

theorem cell23_5115992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_5115992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5115992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5115992 prefixEnd_5115992 := by exact prefixLift 5115992
  have htrace : WordTrace (prefixWord ++ tailWord_5115992) baseStart_5115992 baseEnd_5115992 := by
    simpa [prefixWord, tailWord_5115992, baseEnd_5115992] using wordTrace_append hprefix tailTrace_5115992
  have hstable : (prefixWord ++ tailWord_5115992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5115992).length < 2 ^ (prefixWord ++ tailWord_5115992).sum := by decide
  have hdescent : baseEnd_5115992 < baseStart_5115992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5115992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116005 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 8]
def baseStart_5116005 : Nat := 118140960795 + 5116005 * 2 ^ 59
def prefixEnd_5116005 : Nat := 4983230072969 + 3 ^ 40 * 5116005 * 2
def baseEnd_5116005 : Nat := 291885510645040148956603

theorem tailTrace_5116005 : CollatzResearch.WordTrace tailWord_5116005 prefixEnd_5116005 291885510645040148956603 := by
  unfold tailWord_5116005
  simp only [CollatzResearch.WordTrace]
  refine ⟨186596031830595103936789469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124397354553730069291192979 186596031830595103936789469)
  ·
    refine ⟨69973511936473163976296051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186596031830595103936789469 69973511936473163976296051)
    ·
      refine ⟨104960267904709745964444077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69973511936473163976296051 104960267904709745964444077)
      ·
        refine ⟨39360100464266154736666529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104960267904709745964444077 39360100464266154736666529)
        ·
          refine ⟨29520075348199616052499897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39360100464266154736666529 29520075348199616052499897)
          ·
            refine ⟨22140056511149712039374923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29520075348199616052499897 22140056511149712039374923)
            ·
              refine ⟨33210084766724568059062385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22140056511149712039374923 33210084766724568059062385)
              ·
                refine ⟨24907563575043426044296789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33210084766724568059062385 24907563575043426044296789)
                ·
                  refine ⟨291885510645040148956603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24907563575043426044296789 291885510645040148956603)
                  ·
                    rfl

theorem cell23_5116005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_5116005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116005 prefixEnd_5116005 := by exact prefixLift 5116005
  have htrace : WordTrace (prefixWord ++ tailWord_5116005) baseStart_5116005 baseEnd_5116005 := by
    simpa [prefixWord, tailWord_5116005, baseEnd_5116005] using wordTrace_append hprefix tailTrace_5116005
  have hstable : (prefixWord ++ tailWord_5116005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116005).length < 2 ^ (prefixWord ++ tailWord_5116005).sum := by decide
  have hdescent : baseEnd_5116005 < baseStart_5116005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116022 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_5116022 : Nat := 118140960795 + 5116022 * 2 ^ 59
def prefixEnd_5116022 : Nat := 4983230072969 + 3 ^ 40 * 5116022 * 2
def baseEnd_5116022 : Nat := 291886480552943086010761

theorem tailTrace_5116022 : CollatzResearch.WordTrace tailWord_5116022 prefixEnd_5116022 291886480552943086010761 := by
  unfold tailWord_5116022
  simp only [CollatzResearch.WordTrace]
  refine ⟨11662290741970844740009895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124397767914355677226772213 11662290741970844740009895)
  ·
    refine ⟨17493436112956267110014843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11662290741970844740009895 17493436112956267110014843)
    ·
      refine ⟨26240154169434400665022265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17493436112956267110014843 26240154169434400665022265)
      ·
        refine ⟨19680115627075800498766699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26240154169434400665022265 19680115627075800498766699)
        ·
          refine ⟨29520173440613700748150049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19680115627075800498766699 29520173440613700748150049)
          ·
            refine ⟨22140130080460275561112537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29520173440613700748150049 22140130080460275561112537)
            ·
              refine ⟨16605097560345206670834403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22140130080460275561112537 16605097560345206670834403)
              ·
                refine ⟨24907646340517810006251605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16605097560345206670834403 24907646340517810006251605)
                ·
                  refine ⟨291886480552943086010761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24907646340517810006251605 291886480552943086010761)
                  ·
                    rfl

theorem cell23_5116022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_5116022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116022 prefixEnd_5116022 := by exact prefixLift 5116022
  have htrace : WordTrace (prefixWord ++ tailWord_5116022) baseStart_5116022 baseEnd_5116022 := by
    simpa [prefixWord, tailWord_5116022, baseEnd_5116022] using wordTrace_append hprefix tailTrace_5116022
  have hstable : (prefixWord ++ tailWord_5116022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116022).length < 2 ^ (prefixWord ++ tailWord_5116022).sum := by decide
  have hdescent : baseEnd_5116022 < baseStart_5116022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116069 : List Nat := [1, 3, 1, 2, 1, 3, 5, 1, 1, 5]
def baseStart_5116069 : Nat := 118140960795 + 5116069 * 2 ^ 59
def prefixEnd_5116069 : Nat := 4983230072969 + 3 ^ 40 * 5116069 * 2
def baseEnd_5116069 : Nat := 875667486189083030069711

theorem tailTrace_5116069 : CollatzResearch.WordTrace tailWord_5116069 prefixEnd_5116069 875667486189083030069711 := by
  unfold tailWord_5116069
  simp only [CollatzResearch.WordTrace]
  refine ⟨186598366102363242867119261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124398910734908828578079507 186598366102363242867119261)
  ·
    refine ⟨69974387288386216075169723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186598366102363242867119261 69974387288386216075169723)
    ·
      refine ⟨104961580932579324112754585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69974387288386216075169723 104961580932579324112754585)
      ·
        refine ⟨78721185699434493084565939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104961580932579324112754585 78721185699434493084565939)
        ·
          refine ⟨118081778549151739626848909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78721185699434493084565939 118081778549151739626848909)
          ·
            refine ⟨44280666955931902360068341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118081778549151739626848909 44280666955931902360068341)
            ·
              refine ⟨4151312527118615846256407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44280666955931902360068341 4151312527118615846256407)
              ·
                refine ⟨6226968790677923769384611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4151312527118615846256407 6226968790677923769384611)
                ·
                  refine ⟨9340453186016885654076917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6226968790677923769384611 9340453186016885654076917)
                  ·
                    refine ⟨875667486189083030069711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9340453186016885654076917 875667486189083030069711)
                    ·
                      rfl

theorem cell23_5116069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_5116069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116069 prefixEnd_5116069 := by exact prefixLift 5116069
  have htrace : WordTrace (prefixWord ++ tailWord_5116069) baseStart_5116069 baseEnd_5116069 := by
    simpa [prefixWord, tailWord_5116069, baseEnd_5116069] using wordTrace_append hprefix tailTrace_5116069
  have hstable : (prefixWord ++ tailWord_5116069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116069).length < 2 ^ (prefixWord ++ tailWord_5116069).sum := by decide
  have hdescent : baseEnd_5116069 < baseStart_5116069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116106 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2]
def baseStart_5116106 : Nat := 118140960795 + 5116106 * 2 ^ 59
def prefixEnd_5116106 : Nat := 4983230072969 + 3 ^ 40 * 5116106 * 2
def baseEnd_5116106 : Nat := 2627021457351465445446463

theorem tailTrace_5116106 : CollatzResearch.WordTrace tailWord_5116106 prefixEnd_5116106 2627021457351465445446463 := by
  unfold tailWord_5116106
  simp only [CollatzResearch.WordTrace]
  refine ⟨46649928900807299546554043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124399810402152798790810781 46649928900807299546554043)
  ·
    refine ⟨69974893351210949319831065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46649928900807299546554043 69974893351210949319831065)
    ·
      refine ⟨52481170013408211989873299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69974893351210949319831065 52481170013408211989873299)
      ·
        refine ⟨78721755020112317984809949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52481170013408211989873299 78721755020112317984809949)
        ·
          refine ⟨29520658132542119244303731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78721755020112317984809949 29520658132542119244303731)
          ·
            refine ⟨44280987198813178866455597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29520658132542119244303731 44280987198813178866455597)
            ·
              refine ⟨16605370199554942074920849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44280987198813178866455597 16605370199554942074920849)
              ·
                refine ⟨12454027649666206556190637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16605370199554942074920849 12454027649666206556190637)
                ·
                  refine ⟨4670260368624827458571489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12454027649666206556190637 4670260368624827458571489)
                  ·
                    refine ⟨3502695276468620593928617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4670260368624827458571489 3502695276468620593928617)
                    ·
                      refine ⟨2627021457351465445446463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502695276468620593928617 2627021457351465445446463)
                      ·
                        rfl

theorem cell23_5116106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_5116106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116106 prefixEnd_5116106 := by exact prefixLift 5116106
  have htrace : WordTrace (prefixWord ++ tailWord_5116106) baseStart_5116106 baseEnd_5116106 := by
    simpa [prefixWord, tailWord_5116106, baseEnd_5116106] using wordTrace_append hprefix tailTrace_5116106
  have hstable : (prefixWord ++ tailWord_5116106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116106).length < 2 ^ (prefixWord ++ tailWord_5116106).sum := by decide
  have hdescent : baseEnd_5116106 < baseStart_5116106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116139 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 4, 1, 3]
def baseStart_5116139 : Nat := 118140960795 + 5116139 * 2 ^ 59
def prefixEnd_5116139 : Nat := 4983230072969 + 3 ^ 40 * 5116139 * 2
def baseEnd_5116139 : Nat := 2627038402213063816333811

theorem tailTrace_5116139 : CollatzResearch.WordTrace tailWord_5116139 prefixEnd_5116139 2627038402213063816333811 := by
  unfold tailWord_5116139
  simp only [CollatzResearch.WordTrace]
  refine ⟨186600919212109644822167471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124400612808073096548111647 186600919212109644822167471)
  ·
    refine ⟨279901378818164467233251207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186600919212109644822167471 279901378818164467233251207)
    ·
      refine ⟨419852068227246700849876811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279901378818164467233251207 419852068227246700849876811)
      ·
        refine ⟨629778102340870051274815217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419852068227246700849876811 629778102340870051274815217)
        ·
          refine ⟨472333576755652538456111413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 629778102340870051274815217 472333576755652538456111413)
          ·
            refine ⟨44281272820842425480260445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 472333576755652538456111413 44281272820842425480260445)
            ·
              refine ⟨16605477307815909555097667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44281272820842425480260445 16605477307815909555097667)
              ·
                refine ⟨24908215961723864332646501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16605477307815909555097667 24908215961723864332646501)
                ·
                  refine ⟨4670290492823224562371219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24908215961723864332646501 4670290492823224562371219)
                  ·
                    refine ⟨7005435739234836843556829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4670290492823224562371219 7005435739234836843556829)
                    ·
                      refine ⟨2627038402213063816333811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7005435739234836843556829 2627038402213063816333811)
                      ·
                        rfl

theorem cell23_5116139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 1, 3].length) (baseStart_5116139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116139 prefixEnd_5116139 := by exact prefixLift 5116139
  have htrace : WordTrace (prefixWord ++ tailWord_5116139) baseStart_5116139 baseEnd_5116139 := by
    simpa [prefixWord, tailWord_5116139, baseEnd_5116139] using wordTrace_append hprefix tailTrace_5116139
  have hstable : (prefixWord ++ tailWord_5116139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116139).length < 2 ^ (prefixWord ++ tailWord_5116139).sum := by decide
  have hdescent : baseEnd_5116139 < baseStart_5116139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116156 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_5116156 : Nat := 118140960795 + 5116156 * 2 ^ 59
def prefixEnd_5116156 : Nat := 4983230072969 + 3 ^ 40 * 5116156 * 2
def baseEnd_5116156 : Nat := 2627047131384190249821233

theorem tailTrace_5116156 : CollatzResearch.WordTrace tailWord_5116156 prefixEnd_5116156 2627047131384190249821233 := by
  unfold tailWord_5116156
  simp only [CollatzResearch.WordTrace]
  refine ⟨93300769626524028362768161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124401026168698704483690881 93300769626524028362768161)
  ·
    refine ⟨69975577219893021272076121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93300769626524028362768161 69975577219893021272076121)
    ·
      refine ⟨52481682914919765954057091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69975577219893021272076121 52481682914919765954057091)
      ·
        refine ⟨78722524372379648931085637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52481682914919765954057091 78722524372379648931085637)
        ·
          refine ⟨14760473319821184174578557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78722524372379648931085637 14760473319821184174578557)
          ·
            refine ⟨5535177494932944065466959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14760473319821184174578557 5535177494932944065466959)
            ·
              refine ⟨8302766242399416098200439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5535177494932944065466959 8302766242399416098200439)
              ·
                refine ⟨12454149363599124147300659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8302766242399416098200439 12454149363599124147300659)
                ·
                  refine ⟨18681224045398686220950989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12454149363599124147300659 18681224045398686220950989)
                  ·
                    refine ⟨7005459017024507332856621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18681224045398686220950989 7005459017024507332856621)
                    ·
                      refine ⟨2627047131384190249821233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7005459017024507332856621 2627047131384190249821233)
                      ·
                        rfl

theorem cell23_5116156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_5116156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116156 prefixEnd_5116156 := by exact prefixLift 5116156
  have htrace : WordTrace (prefixWord ++ tailWord_5116156) baseStart_5116156 baseEnd_5116156 := by
    simpa [prefixWord, tailWord_5116156, baseEnd_5116156] using wordTrace_append hprefix tailTrace_5116156
  have hstable : (prefixWord ++ tailWord_5116156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116156).length < 2 ^ (prefixWord ++ tailWord_5116156).sum := by decide
  have hdescent : baseEnd_5116156 < baseStart_5116156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116179 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 1, 4, 2]
def baseStart_5116179 : Nat := 118140960795 + 5116179 * 2 ^ 59
def prefixEnd_5116179 : Nat := 4983230072969 + 3 ^ 40 * 5116179 * 2
def baseEnd_5116179 : Nat := 2627058941439243659833627

theorem tailTrace_5116179 : CollatzResearch.WordTrace tailWord_5116179 prefixEnd_5116179 2627058941439243659833627 := by
  unfold tailWord_5116179
  simp only [CollatzResearch.WordTrace]
  refine ⟨186602378131964731653623591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124401585421309821102415727 186602378131964731653623591)
  ·
    refine ⟨279903567197947097480435387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186602378131964731653623591 279903567197947097480435387)
    ·
      refine ⟨419855350796920646220653081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279903567197947097480435387 419855350796920646220653081)
      ·
        refine ⟨314891513097690484665489811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419855350796920646220653081 314891513097690484665489811)
        ·
          refine ⟨472337269646535726998234717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314891513097690484665489811 472337269646535726998234717)
          ·
            refine ⟨177126476117450897624338019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 472337269646535726998234717 177126476117450897624338019)
            ·
              refine ⟨265689714176176346436507029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177126476117450897624338019 265689714176176346436507029)
              ·
                refine ⟨12454205352008266239211267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 265689714176176346436507029 12454205352008266239211267)
                ·
                  refine ⟨18681308028012399358816901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12454205352008266239211267 18681308028012399358816901)
                  ·
                    refine ⟨3502745255252324879778169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18681308028012399358816901 3502745255252324879778169)
                    ·
                      refine ⟨2627058941439243659833627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502745255252324879778169 2627058941439243659833627)
                      ·
                        rfl

theorem cell23_5116179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 4, 2].length) (baseStart_5116179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116179 prefixEnd_5116179 := by exact prefixLift 5116179
  have htrace : WordTrace (prefixWord ++ tailWord_5116179) baseStart_5116179 baseEnd_5116179 := by
    simpa [prefixWord, tailWord_5116179, baseEnd_5116179] using wordTrace_append hprefix tailTrace_5116179
  have hstable : (prefixWord ++ tailWord_5116179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116179).length < 2 ^ (prefixWord ++ tailWord_5116179).sum := by decide
  have hdescent : baseEnd_5116179 < baseStart_5116179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116213 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_5116213 : Nat := 118140960795 + 5116213 * 2 ^ 59
def prefixEnd_5116213 : Nat := 4983230072969 + 3 ^ 40 * 5116213 * 2
def baseEnd_5116213 : Nat := 2627076399781496526808471

theorem tailTrace_5116213 : CollatzResearch.WordTrace tailWord_5116213 prefixEnd_5116213 2627076399781496526808471 := by
  unfold tailWord_5116213
  simp only [CollatzResearch.WordTrace]
  refine ⟨186603618213841555460361293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124402412142561036973574195 186603618213841555460361293)
  ·
    refine ⟨69976356830190583297635485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186603618213841555460361293 69976356830190583297635485)
    ·
      refine ⟨26241133811321468736613307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69976356830190583297635485 26241133811321468736613307)
      ·
        refine ⟨39361700716982203104919961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26241133811321468736613307 39361700716982203104919961)
        ·
          refine ⟨29521275537736652328689971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39361700716982203104919961 29521275537736652328689971)
          ·
            refine ⟨44281913306604978493034957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29521275537736652328689971 44281913306604978493034957)
            ·
              refine ⟨16605717489976866934888109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44281913306604978493034957 16605717489976866934888109)
              ·
                refine ⟨6227144058741325100583041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16605717489976866934888109 6227144058741325100583041)
                ·
                  refine ⟨4670358044055993825437281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6227144058741325100583041 4670358044055993825437281)
                  ·
                    refine ⟨3502768533041995369077961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4670358044055993825437281 3502768533041995369077961)
                    ·
                      refine ⟨2627076399781496526808471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502768533041995369077961 2627076399781496526808471)
                      ·
                        rfl

theorem cell23_5116213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_5116213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116213 prefixEnd_5116213 := by exact prefixLift 5116213
  have htrace : WordTrace (prefixWord ++ tailWord_5116213) baseStart_5116213 baseEnd_5116213 := by
    simpa [prefixWord, tailWord_5116213, baseEnd_5116213] using wordTrace_append hprefix tailTrace_5116213
  have hstable : (prefixWord ++ tailWord_5116213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116213).length < 2 ^ (prefixWord ++ tailWord_5116213).sum := by decide
  have hdescent : baseEnd_5116213 < baseStart_5116213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116232 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 1, 7]
def baseStart_5116232 : Nat := 118140960795 + 5116232 * 2 ^ 59
def prefixEnd_5116232 : Nat := 4983230072969 + 3 ^ 40 * 5116232 * 2
def baseEnd_5116232 : Nat := 875695385304643984156961

theorem tailTrace_5116232 : CollatzResearch.WordTrace tailWord_5116232 prefixEnd_5116232 875695385304643984156961 := by
  unfold tailWord_5116232
  simp only [CollatzResearch.WordTrace]
  refine ⟨93302155600386360852651475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124402874133848481136868633 93302155600386360852651475)
  ·
    refine ⟨139953233400579541278977213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93302155600386360852651475 139953233400579541278977213)
    ·
      refine ⟨52482462525217327979616455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139953233400579541278977213 52482462525217327979616455)
      ·
        refine ⟨78723693787825991969424683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52482462525217327979616455 78723693787825991969424683)
        ·
          refine ⟨118085540681738987954137025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78723693787825991969424683 118085540681738987954137025)
          ·
            refine ⟨88564155511304240965602769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118085540681738987954137025 88564155511304240965602769)
            ·
              refine ⟨66423116633478180724202077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88564155511304240965602769 66423116633478180724202077)
              ·
                refine ⟨24908668737554317771575779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66423116633478180724202077 24908668737554317771575779)
                ·
                  refine ⟨37363003106331476657363669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24908668737554317771575779 37363003106331476657363669)
                  ·
                    refine ⟨875695385304643984156961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37363003106331476657363669 875695385304643984156961)
                    ·
                      rfl

theorem cell23_5116232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_5116232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116232 prefixEnd_5116232 := by exact prefixLift 5116232
  have htrace : WordTrace (prefixWord ++ tailWord_5116232) baseStart_5116232 baseEnd_5116232 := by
    simpa [prefixWord, tailWord_5116232, baseEnd_5116232] using wordTrace_append hprefix tailTrace_5116232
  have hstable : (prefixWord ++ tailWord_5116232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116232).length < 2 ^ (prefixWord ++ tailWord_5116232).sum := by decide
  have hdescent : baseEnd_5116232 < baseStart_5116232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116269 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_5116269 : Nat := 118140960795 + 5116269 * 2 ^ 59
def prefixEnd_5116269 : Nat := 4983230072969 + 3 ^ 40 * 5116269 * 2
def baseEnd_5116269 : Nat := 2627105154698148307708213

theorem tailTrace_5116269 : CollatzResearch.WordTrace tailWord_5116269 prefixEnd_5116269 2627105154698148307708213 := by
  unfold tailWord_5116269
  simp only [CollatzResearch.WordTrace]
  refine ⟨186605660701638677024399861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124403773801092451349599907 186605660701638677024399861)
  ·
    refine ⟨17494280690778625971037487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186605660701638677024399861 17494280690778625971037487)
    ·
      refine ⟨26241421036167938956556231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17494280690778625971037487 26241421036167938956556231)
      ·
        refine ⟨39362131554251908434834347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26241421036167938956556231 39362131554251908434834347)
        ·
          refine ⟨59043197331377862652251521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39362131554251908434834347 59043197331377862652251521)
          ·
            refine ⟨44282397998533396989188641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59043197331377862652251521 44282397998533396989188641)
            ·
              refine ⟨33211798498900047741891481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44282397998533396989188641 33211798498900047741891481)
              ·
                refine ⟨24908848874175035806418611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33211798498900047741891481 24908848874175035806418611)
                ·
                  refine ⟨37363273311262553709627917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24908848874175035806418611 37363273311262553709627917)
                  ·
                    refine ⟨14011227491723457641110469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37363273311262553709627917 14011227491723457641110469)
                    ·
                      refine ⟨2627105154698148307708213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14011227491723457641110469 2627105154698148307708213)
                      ·
                        rfl

theorem cell23_5116269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_5116269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116269 prefixEnd_5116269 := by exact prefixLift 5116269
  have htrace : WordTrace (prefixWord ++ tailWord_5116269) baseStart_5116269 baseEnd_5116269 := by
    simpa [prefixWord, tailWord_5116269, baseEnd_5116269] using wordTrace_append hprefix tailTrace_5116269
  have hstable : (prefixWord ++ tailWord_5116269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116269).length < 2 ^ (prefixWord ++ tailWord_5116269).sum := by decide
  have hdescent : baseEnd_5116269 < baseStart_5116269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116282 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_5116282 : Nat := 118140960795 + 5116282 * 2 ^ 59
def prefixEnd_5116282 : Nat := 4983230072969 + 3 ^ 40 * 5116282 * 2
def baseEnd_5116282 : Nat := 2627111829946656756845653

theorem tailTrace_5116282 : CollatzResearch.WordTrace tailWord_5116282 prefixEnd_5116282 2627111829946656756845653 := by
  unfold tailWord_5116282
  simp only [CollatzResearch.WordTrace]
  refine ⟨46651533712647895061155775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124404089900394386829748733 46651533712647895061155775)
  ·
    refine ⟨69977300568971842591733663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46651533712647895061155775 69977300568971842591733663)
    ·
      refine ⟨104965950853457763887600495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69977300568971842591733663 104965950853457763887600495)
      ·
        refine ⟨157448926280186645831400743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104965950853457763887600495 157448926280186645831400743)
        ·
          refine ⟨236173389420279968747101115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157448926280186645831400743 236173389420279968747101115)
          ·
            refine ⟨354260084130419953120651673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236173389420279968747101115 354260084130419953120651673)
            ·
              refine ⟨265695063097814964840488755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354260084130419953120651673 265695063097814964840488755)
              ·
                refine ⟨398542594646722447260733133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265695063097814964840488755 398542594646722447260733133)
                ·
                  refine ⟨149453472992520917722774925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 398542594646722447260733133 149453472992520917722774925)
                  ·
                    refine ⟨56045052372195344146040597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 149453472992520917722774925 56045052372195344146040597)
                    ·
                      refine ⟨2627111829946656756845653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56045052372195344146040597 2627111829946656756845653)
                      ·
                        rfl

theorem cell23_5116282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_5116282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116282 prefixEnd_5116282 := by exact prefixLift 5116282
  have htrace : WordTrace (prefixWord ++ tailWord_5116282) baseStart_5116282 baseEnd_5116282 := by
    simpa [prefixWord, tailWord_5116282, baseEnd_5116282] using wordTrace_append hprefix tailTrace_5116282
  have hstable : (prefixWord ++ tailWord_5116282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116282).length < 2 ^ (prefixWord ++ tailWord_5116282).sum := by decide
  have hdescent : baseEnd_5116282 < baseStart_5116282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116346 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2]
def baseStart_5116346 : Nat := 118140960795 + 5116346 * 2 ^ 59
def prefixEnd_5116346 : Nat := 4983230072969 + 3 ^ 40 * 5116346 * 2
def baseEnd_5116346 : Nat := 2627144692708544506445359

theorem tailTrace_5116346 : CollatzResearch.WordTrace tailWord_5116346 prefixEnd_5116346 2627144692708544506445359 := by
  unfold tailWord_5116346
  simp only [CollatzResearch.WordTrace]
  refine ⟨46652117280589929793738223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124405646081573146116635261 46652117280589929793738223)
  ·
    refine ⟨69978175920884894690607335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46652117280589929793738223 69978175920884894690607335)
    ·
      refine ⟨104967263881327342035911003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69978175920884894690607335 104967263881327342035911003)
      ·
        refine ⟨157450895821991013053866505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104967263881327342035911003 157450895821991013053866505)
        ·
          refine ⟨118088171866493259790399879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157450895821991013053866505 118088171866493259790399879)
          ·
            refine ⟨177132257799739889685599819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118088171866493259790399879 177132257799739889685599819)
            ·
              refine ⟨265698386699609834528399729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177132257799739889685599819 265698386699609834528399729)
              ·
                refine ⟨199273790024707375896299797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265698386699609834528399729 199273790024707375896299797)
                ·
                  refine ⟨9340958907408158245139053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 199273790024707375896299797 9340958907408158245139053)
                  ·
                    refine ⟨3502859590278059341927145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9340958907408158245139053 3502859590278059341927145)
                    ·
                      refine ⟨2627144692708544506445359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502859590278059341927145 2627144692708544506445359)
                      ·
                        rfl

theorem cell23_5116346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2].length) (baseStart_5116346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116346 prefixEnd_5116346 := by exact prefixLift 5116346
  have htrace : WordTrace (prefixWord ++ tailWord_5116346) baseStart_5116346 baseEnd_5116346 := by
    simpa [prefixWord, tailWord_5116346, baseEnd_5116346] using wordTrace_append hprefix tailTrace_5116346
  have hstable : (prefixWord ++ tailWord_5116346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116346).length < 2 ^ (prefixWord ++ tailWord_5116346).sum := by decide
  have hdescent : baseEnd_5116346 < baseStart_5116346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116396 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 3]
def baseStart_5116396 : Nat := 118140960795 + 5116396 * 2 ^ 59
def prefixEnd_5116396 : Nat := 4983230072969 + 3 ^ 40 * 5116396 * 2
def baseEnd_5116396 : Nat := 2627170366741269310820129

theorem tailTrace_5116396 : CollatzResearch.WordTrace tailWord_5116396 prefixEnd_5116396 2627170366741269310820129 := by
  unfold tailWord_5116396
  simp only [CollatzResearch.WordTrace]
  refine ⟨93305146386089288857136521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124406861848119051809515361 93305146386089288857136521)
  ·
    refine ⟨69978859789566966642852391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93305146386089288857136521 69978859789566966642852391)
    ·
      refine ⟨104968289684350449964278587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69978859789566966642852391 104968289684350449964278587)
      ·
        refine ⟨157452434526525674946417881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104968289684350449964278587 157452434526525674946417881)
        ·
          refine ⟨118089325894894256209813411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157452434526525674946417881 118089325894894256209813411)
          ·
            refine ⟨177133988842341384314720117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118089325894894256209813411 177133988842341384314720117)
            ·
              refine ⟨16606311453969504779505011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177133988842341384314720117 16606311453969504779505011)
              ·
                refine ⟨24909467180954257169257517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16606311453969504779505011 24909467180954257169257517)
                ·
                  refine ⟨9341050192857846438471569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24909467180954257169257517 9341050192857846438471569)
                  ·
                    refine ⟨7005787644643384828853677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9341050192857846438471569 7005787644643384828853677)
                    ·
                      refine ⟨2627170366741269310820129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7005787644643384828853677 2627170366741269310820129)
                      ·
                        rfl

theorem cell23_5116396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_5116396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116396 prefixEnd_5116396 := by exact prefixLift 5116396
  have htrace : WordTrace (prefixWord ++ tailWord_5116396) baseStart_5116396 baseEnd_5116396 := by
    simpa [prefixWord, tailWord_5116396, baseEnd_5116396] using wordTrace_append hprefix tailTrace_5116396
  have hstable : (prefixWord ++ tailWord_5116396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116396).length < 2 ^ (prefixWord ++ tailWord_5116396).sum := by decide
  have hdescent : baseEnd_5116396 < baseStart_5116396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116420 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_5116420 : Nat := 118140960795 + 5116420 * 2 ^ 59
def prefixEnd_5116420 : Nat := 4983230072969 + 3 ^ 40 * 5116420 * 2
def baseEnd_5116420 : Nat := 875727563425659072306673

theorem tailTrace_5116420 : CollatzResearch.WordTrace tailWord_5116420 prefixEnd_5116420 875727563425659072306673 := by
  unfold tailWord_5116420
  simp only [CollatzResearch.WordTrace]
  refine ⟨93305584062045814906573357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124407445416061086542097809 93305584062045814906573357)
  ·
    refine ⟨34989594023267180589965009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93305584062045814906573357 34989594023267180589965009)
    ·
      refine ⟨26242195517450385442473757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34989594023267180589965009 26242195517450385442473757)
      ·
        refine ⟨9840823319043894540927659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26242195517450385442473757 9840823319043894540927659)
        ·
          refine ⟨14761234978565841811391489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9840823319043894540927659 14761234978565841811391489)
          ·
            refine ⟨11070926233924381358543617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14761234978565841811391489 11070926233924381358543617)
            ·
              refine ⟨8303194675443286018907713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11070926233924381358543617 8303194675443286018907713)
              ·
                refine ⟨6227396006582464514180785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8303194675443286018907713 6227396006582464514180785)
                ·
                  refine ⟨4670547004936848385635589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6227396006582464514180785 4670547004936848385635589)
                  ·
                    refine ⟨875727563425659072306673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4670547004936848385635589 875727563425659072306673)
                    ·
                      rfl

theorem cell23_5116420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_5116420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116420 prefixEnd_5116420 := by exact prefixLift 5116420
  have htrace : WordTrace (prefixWord ++ tailWord_5116420) baseStart_5116420 baseEnd_5116420 := by
    simpa [prefixWord, tailWord_5116420, baseEnd_5116420] using wordTrace_append hprefix tailTrace_5116420
  have hstable : (prefixWord ++ tailWord_5116420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116420).length < 2 ^ (prefixWord ++ tailWord_5116420).sum := by decide
  have hdescent : baseEnd_5116420 < baseStart_5116420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116426 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_5116426 : Nat := 118140960795 + 5116426 * 2 ^ 59
def prefixEnd_5116426 : Nat := 4983230072969 + 3 ^ 40 * 5116426 * 2
def baseEnd_5116426 : Nat := 2627185771160904193444991

theorem tailTrace_5116426 : CollatzResearch.WordTrace tailWord_5116426 prefixEnd_5116426 2627185771160904193444991 := by
  unfold tailWord_5116426
  simp only [CollatzResearch.WordTrace]
  refine ⟨46652846740517473209466283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124407591308046595225243421 46652846740517473209466283)
  ·
    refine ⟨69979270110776209814199425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46652846740517473209466283 69979270110776209814199425)
    ·
      refine ⟨52484452583082157360649569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69979270110776209814199425 52484452583082157360649569)
      ·
        refine ⟨39363339437311618020487177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52484452583082157360649569 39363339437311618020487177)
        ·
          refine ⟨29522504577983713515365383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39363339437311618020487177 29522504577983713515365383)
          ·
            refine ⟨44283756866975570273048075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29522504577983713515365383 44283756866975570273048075)
            ·
              refine ⟨66425635300463355409572113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44283756866975570273048075 66425635300463355409572113)
              ·
                refine ⟨49819226475347516557179085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66425635300463355409572113 49819226475347516557179085)
                ·
                  refine ⟨18682209928255318708942157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49819226475347516557179085 18682209928255318708942157)
                  ·
                    refine ⟨7005828723095744515853309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18682209928255318708942157 7005828723095744515853309)
                    ·
                      refine ⟨2627185771160904193444991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7005828723095744515853309 2627185771160904193444991)
                      ·
                        rfl

theorem cell23_5116426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_5116426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116426 prefixEnd_5116426 := by exact prefixLift 5116426
  have htrace : WordTrace (prefixWord ++ tailWord_5116426) baseStart_5116426 baseEnd_5116426 := by
    simpa [prefixWord, tailWord_5116426, baseEnd_5116426] using wordTrace_append hprefix tailTrace_5116426
  have hstable : (prefixWord ++ tailWord_5116426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116426).length < 2 ^ (prefixWord ++ tailWord_5116426).sum := by decide
  have hdescent : baseEnd_5116426 < baseStart_5116426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116427 : List Nat := [1, 1, 1, 1, 7, 2, 1, 4, 1, 2, 2]
def baseStart_5116427 : Nat := 118140960795 + 5116427 * 2 ^ 59
def prefixEnd_5116427 : Nat := 4983230072969 + 3 ^ 40 * 5116427 * 2
def baseEnd_5116427 : Nat := 2627186284641558689532487

theorem tailTrace_5116427 : CollatzResearch.WordTrace tailWord_5116427 prefixEnd_5116427 2627186284641558689532487 := by
  unfold tailWord_5116427
  simp only [CollatzResearch.WordTrace]
  refine ⟨186611423435066270008651535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124407615623377513339101023 186611423435066270008651535)
  ·
    refine ⟨279917135152599405012977303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186611423435066270008651535 279917135152599405012977303)
    ·
      refine ⟨419875702728899107519465955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279917135152599405012977303 419875702728899107519465955)
      ·
        refine ⟨629813554093348661279198933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419875702728899107519465955 629813554093348661279198933)
        ·
          refine ⟨14761255174062859248731225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 629813554093348661279198933 14761255174062859248731225)
          ·
            refine ⟨11070941380547144436548419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14761255174062859248731225 11070941380547144436548419)
            ·
              refine ⟨16606412070820716654822629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11070941380547144436548419 16606412070820716654822629)
              ·
                refine ⟨3113702263278884372779243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16606412070820716654822629 3113702263278884372779243)
                ·
                  refine ⟨4670553394918326559168865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113702263278884372779243 4670553394918326559168865)
                  ·
                    refine ⟨3502915046188744919376649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4670553394918326559168865 3502915046188744919376649)
                    ·
                      refine ⟨2627186284641558689532487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502915046188744919376649 2627186284641558689532487)
                      ·
                        rfl

theorem cell23_5116427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 1, 2, 2].length) (baseStart_5116427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116427 prefixEnd_5116427 := by exact prefixLift 5116427
  have htrace : WordTrace (prefixWord ++ tailWord_5116427) baseStart_5116427 baseEnd_5116427 := by
    simpa [prefixWord, tailWord_5116427, baseEnd_5116427] using wordTrace_append hprefix tailTrace_5116427
  have hstable : (prefixWord ++ tailWord_5116427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116427).length < 2 ^ (prefixWord ++ tailWord_5116427).sum := by decide
  have hdescent : baseEnd_5116427 < baseStart_5116427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116453 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 3, 3, 2]
def baseStart_5116453 : Nat := 118140960795 + 5116453 * 2 ^ 59
def prefixEnd_5116453 : Nat := 4983230072969 + 3 ^ 40 * 5116453 * 2
def baseEnd_5116453 : Nat := 2627199635138575587807367

theorem tailTrace_5116453 : CollatzResearch.WordTrace tailWord_5116453 prefixEnd_5116453 2627199635138575587807367 := by
  unfold tailWord_5116453
  simp only [CollatzResearch.WordTrace]
  refine ⟨186612371732972076449098013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124408247821981384299398675 186612371732972076449098013)
  ·
    refine ⟨69979639399864528668411755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186612371732972076449098013 69979639399864528668411755)
    ·
      refine ⟨104969459099796793002617633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69979639399864528668411755 104969459099796793002617633)
      ·
        refine ⟨78727094324847594751963225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104969459099796793002617633 78727094324847594751963225)
        ·
          refine ⟨59045320743635696063972419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78727094324847594751963225 59045320743635696063972419)
          ·
            refine ⟨88567981115453544095958629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59045320743635696063972419 88567981115453544095958629)
            ·
              refine ⟨16606496459147539517992243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88567981115453544095958629 16606496459147539517992243)
              ·
                refine ⟨24909744688721309276988365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16606496459147539517992243 24909744688721309276988365)
                ·
                  refine ⟨9341154258270490978870637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24909744688721309276988365 9341154258270490978870637)
                  ·
                    refine ⟨3502932846851434117076489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9341154258270490978870637 3502932846851434117076489)
                    ·
                      refine ⟨2627199635138575587807367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502932846851434117076489 2627199635138575587807367)
                      ·
                        rfl

theorem cell23_5116453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_5116453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116453 prefixEnd_5116453 := by exact prefixLift 5116453
  have htrace : WordTrace (prefixWord ++ tailWord_5116453) baseStart_5116453 baseEnd_5116453 := by
    simpa [prefixWord, tailWord_5116453, baseEnd_5116453] using wordTrace_append hprefix tailTrace_5116453
  have hstable : (prefixWord ++ tailWord_5116453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116453).length < 2 ^ (prefixWord ++ tailWord_5116453).sum := by decide
  have hdescent : baseEnd_5116453 < baseStart_5116453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116461 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5116461 : Nat := 118140960795 + 5116461 * 2 ^ 59
def prefixEnd_5116461 : Nat := 4983230072969 + 3 ^ 40 * 5116461 * 2
def baseEnd_5116461 : Nat := 2627203742983811556507331

theorem tailTrace_5116461 : CollatzResearch.WordTrace tailWord_5116461 prefixEnd_5116461 2627203742983811556507331 := by
  unfold tailWord_5116461
  simp only [CollatzResearch.WordTrace]
  refine ⟨186612663516943093815389237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124408442344628729210259491 186612663516943093815389237)
  ·
    refine ⟨17494937204713415045192741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186612663516943093815389237 17494937204713415045192741)
    ·
      refine ⟨3280300725883765320973639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17494937204713415045192741 3280300725883765320973639)
      ·
        refine ⟨4920451088825647981460459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3280300725883765320973639 4920451088825647981460459)
        ·
          refine ⟨7380676633238471972190689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4920451088825647981460459 7380676633238471972190689)
          ·
            refine ⟨5535507474928853979143017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7380676633238471972190689 5535507474928853979143017)
            ·
              refine ⟨4151630606196640484357263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5535507474928853979143017 4151630606196640484357263)
              ·
                refine ⟨6227445909294960726535895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4151630606196640484357263 6227445909294960726535895)
                ·
                  refine ⟨9341168863942441089803843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6227445909294960726535895 9341168863942441089803843)
                  ·
                    refine ⟨14011753295913661634705765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9341168863942441089803843 14011753295913661634705765)
                    ·
                      refine ⟨2627203742983811556507331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14011753295913661634705765 2627203742983811556507331)
                      ·
                        rfl

theorem cell23_5116461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5116461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116461 prefixEnd_5116461 := by exact prefixLift 5116461
  have htrace : WordTrace (prefixWord ++ tailWord_5116461) baseStart_5116461 baseEnd_5116461 := by
    simpa [prefixWord, tailWord_5116461, baseEnd_5116461] using wordTrace_append hprefix tailTrace_5116461
  have hstable : (prefixWord ++ tailWord_5116461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116461).length < 2 ^ (prefixWord ++ tailWord_5116461).sum := by decide
  have hdescent : baseEnd_5116461 < baseStart_5116461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116476 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_5116476 : Nat := 118140960795 + 5116476 * 2 ^ 59
def prefixEnd_5116476 : Nat := 4983230072969 + 3 ^ 40 * 5116476 * 2
def baseEnd_5116476 : Nat := 875737148397876332606587

theorem tailTrace_5116476 : CollatzResearch.WordTrace tailWord_5116476 prefixEnd_5116476 875737148397876332606587 := by
  unfold tailWord_5116476
  simp only [CollatzResearch.WordTrace]
  refine ⟨93306605305944375688592641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124408807074592500918123521 93306605305944375688592641)
  ·
    refine ⟨69979953979458281766444481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93306605305944375688592641 69979953979458281766444481)
    ·
      refine ⟨52484965484593711324833361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69979953979458281766444481 52484965484593711324833361)
      ·
        refine ⟨39363724113445283493625021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52484965484593711324833361 39363724113445283493625021)
        ·
          refine ⟨14761396542541981310109383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39363724113445283493625021 14761396542541981310109383)
          ·
            refine ⟨22142094813812971965164075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14761396542541981310109383 22142094813812971965164075)
            ·
              refine ⟨33213142220719457947746113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22142094813812971965164075 33213142220719457947746113)
              ·
                refine ⟨24909856665539593460809585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33213142220719457947746113 24909856665539593460809585)
                ·
                  refine ⟨18682392499154695095607189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24909856665539593460809585 18682392499154695095607189)
                  ·
                    refine ⟨875737148397876332606587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18682392499154695095607189 875737148397876332606587)
                    ·
                      rfl

theorem cell23_5116476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_5116476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116476 prefixEnd_5116476 := by exact prefixLift 5116476
  have htrace : WordTrace (prefixWord ++ tailWord_5116476) baseStart_5116476 baseEnd_5116476 := by
    simpa [prefixWord, tailWord_5116476, baseEnd_5116476] using wordTrace_append hprefix tailTrace_5116476
  have hstable : (prefixWord ++ tailWord_5116476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116476).length < 2 ^ (prefixWord ++ tailWord_5116476).sum := by decide
  have hdescent : baseEnd_5116476 < baseStart_5116476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116477 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 2, 1, 3]
def baseStart_5116477 : Nat := 118140960795 + 5116477 * 2 ^ 59
def prefixEnd_5116477 : Nat := 4983230072969 + 3 ^ 40 * 5116477 * 2
def baseEnd_5116477 : Nat := 2627211958674283493907257

theorem tailTrace_5116477 : CollatzResearch.WordTrace tailWord_5116477 prefixEnd_5116477 2627211958674283493907257 := by
  unfold tailWord_5116477
  simp only [CollatzResearch.WordTrace]
  refine ⟨186613247084885128547971685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124408831389923419031981123 186613247084885128547971685)
  ·
    refine ⟨34989983828415961602744691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186613247084885128547971685 34989983828415961602744691)
    ·
      refine ⟨52484975742623942404117037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34989983828415961602744691 52484975742623942404117037)
      ·
        refine ⟨19681865903483978401543889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52484975742623942404117037 19681865903483978401543889)
        ·
          refine ⟨14761399427612983801157917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19681865903483978401543889 14761399427612983801157917)
          ·
            refine ⟨5535524785354868925434219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14761399427612983801157917 5535524785354868925434219)
            ·
              refine ⟨8303287178032303388151329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5535524785354868925434219 8303287178032303388151329)
              ·
                refine ⟨6227465383524227541113497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8303287178032303388151329 6227465383524227541113497)
                ·
                  refine ⟨4670599037643170655835123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6227465383524227541113497 4670599037643170655835123)
                  ·
                    refine ⟨7005898556464755983752685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4670599037643170655835123 7005898556464755983752685)
                    ·
                      refine ⟨2627211958674283493907257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7005898556464755983752685 2627211958674283493907257)
                      ·
                        rfl

theorem cell23_5116477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_5116477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116477 prefixEnd_5116477 := by exact prefixLift 5116477
  have htrace : WordTrace (prefixWord ++ tailWord_5116477) baseStart_5116477 baseEnd_5116477 := by
    simpa [prefixWord, tailWord_5116477, baseEnd_5116477] using wordTrace_append hprefix tailTrace_5116477
  have hstable : (prefixWord ++ tailWord_5116477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116477).length < 2 ^ (prefixWord ++ tailWord_5116477).sum := by decide
  have hdescent : baseEnd_5116477 < baseStart_5116477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116493 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_5116493 : Nat := 118140960795 + 5116493 * 2 ^ 59
def prefixEnd_5116493 : Nat := 4983230072969 + 3 ^ 40 * 5116493 * 2
def baseEnd_5116493 : Nat := 875740058121585143769061

theorem tailTrace_5116493 : CollatzResearch.WordTrace tailWord_5116493 prefixEnd_5116493 875740058121585143769061 := by
  unfold tailWord_5116493
  simp only [CollatzResearch.WordTrace]
  refine ⟨186613830652827163280554133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124409220435218108853702755 186613830652827163280554133)
  ·
    refine ⟨8747523311851273278775975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 186613830652827163280554133 8747523311851273278775975)
    ·
      refine ⟨13121284967776909918163963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8747523311851273278775975 13121284967776909918163963)
      ·
        refine ⟨19681927451665364877245945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13121284967776909918163963 19681927451665364877245945)
        ·
          refine ⟨14761445588749023657934459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19681927451665364877245945 14761445588749023657934459)
          ·
            refine ⟨22142168383123535486901689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14761445588749023657934459 22142168383123535486901689)
            ·
              refine ⟨16606626287342651615176267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22142168383123535486901689 16606626287342651615176267)
              ·
                refine ⟨24909939431013977422764401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16606626287342651615176267 24909939431013977422764401)
                ·
                  refine ⟨18682454573260483067073301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24909939431013977422764401 18682454573260483067073301)
                  ·
                    refine ⟨875740058121585143769061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18682454573260483067073301 875740058121585143769061)
                    ·
                      rfl

theorem cell23_5116493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_5116493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116493 prefixEnd_5116493 := by exact prefixLift 5116493
  have htrace : WordTrace (prefixWord ++ tailWord_5116493) baseStart_5116493 baseEnd_5116493 := by
    simpa [prefixWord, tailWord_5116493, baseEnd_5116493] using wordTrace_append hprefix tailTrace_5116493
  have hstable : (prefixWord ++ tailWord_5116493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116493).length < 2 ^ (prefixWord ++ tailWord_5116493).sum := by decide
  have hdescent : baseEnd_5116493 < baseStart_5116493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116500 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_5116500 : Nat := 118140960795 + 5116500 * 2 ^ 59
def prefixEnd_5116500 : Nat := 4983230072969 + 3 ^ 40 * 5116500 * 2
def baseEnd_5116500 : Nat := 2627223768729336903919651

theorem tailTrace_5116500 : CollatzResearch.WordTrace tailWord_5116500 prefixEnd_5116500 2627223768729336903919651 := by
  unfold tailWord_5116500
  simp only [CollatzResearch.WordTrace]
  refine ⟨93307042981900901738029477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124409390642534535650705969 93307042981900901738029477)
  ·
    refine ⟨17495070559106419075880527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93307042981900901738029477 17495070559106419075880527)
    ·
      refine ⟨26242605838659628613820791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17495070559106419075880527 26242605838659628613820791)
      ·
        refine ⟨39363908757989442920731187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26242605838659628613820791 39363908757989442920731187)
        ·
          refine ⟨59045863136984164381096781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39363908757989442920731187 59045863136984164381096781)
          ·
            refine ⟨22142198676369061642911293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59045863136984164381096781 22142198676369061642911293)
            ·
              refine ⟨8303324503638398116091735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22142198676369061642911293 8303324503638398116091735)
              ·
                refine ⟨12454986755457597174137603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8303324503638398116091735 12454986755457597174137603)
                ·
                  refine ⟨18682480133186395761206405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12454986755457597174137603 18682480133186395761206405)
                  ·
                    refine ⟨3502965024972449205226201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18682480133186395761206405 3502965024972449205226201)
                    ·
                      refine ⟨2627223768729336903919651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3502965024972449205226201 2627223768729336903919651)
                      ·
                        rfl

theorem cell23_5116500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_5116500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116500 prefixEnd_5116500 := by exact prefixLift 5116500
  have htrace : WordTrace (prefixWord ++ tailWord_5116500) baseStart_5116500 baseEnd_5116500 := by
    simpa [prefixWord, tailWord_5116500, baseEnd_5116500] using wordTrace_append hprefix tailTrace_5116500
  have hstable : (prefixWord ++ tailWord_5116500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116500).length < 2 ^ (prefixWord ++ tailWord_5116500).sum := by decide
  have hdescent : baseEnd_5116500 < baseStart_5116500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116536 : List Nat := [2, 1, 2, 1, 1, 1, 2, 6, 2, 5]
def baseStart_5116536 : Nat := 118140960795 + 5116536 * 2 ^ 59
def prefixEnd_5116536 : Nat := 4983230072969 + 3 ^ 40 * 5116536 * 2
def baseEnd_5116536 : Nat := 875747418010966254356495

theorem tailTrace_5116536 : CollatzResearch.WordTrace tailWord_5116536 prefixEnd_5116536 875747418010966254356495 := by
  unfold tailWord_5116536
  simp only [CollatzResearch.WordTrace]
  refine ⟨93307699495835690812184731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124410265994447587749579641 93307699495835690812184731)
  ·
    refine ⟨139961549243753536218277097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93307699495835690812184731 139961549243753536218277097)
    ·
      refine ⟨104971161932815152163707823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139961549243753536218277097 104971161932815152163707823)
      ·
        refine ⟨157456742899222728245561735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104971161932815152163707823 157456742899222728245561735)
        ·
          refine ⟨236185114348834092368342603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157456742899222728245561735 236185114348834092368342603)
          ·
            refine ⟨354277671523251138552513905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236185114348834092368342603 354277671523251138552513905)
            ·
              refine ⟨265708253642438353914385429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354277671523251138552513905 265708253642438353914385429)
              ·
                refine ⟨12455074389489297839736817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 265708253642438353914385429 12455074389489297839736817)
                ·
                  refine ⟨9341305792116973379802613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12455074389489297839736817 9341305792116973379802613)
                  ·
                    refine ⟨875747418010966254356495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9341305792116973379802613 875747418010966254356495)
                    ·
                      rfl

theorem cell23_5116536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_5116536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116536 prefixEnd_5116536 := by exact prefixLift 5116536
  have htrace : WordTrace (prefixWord ++ tailWord_5116536) baseStart_5116536 baseEnd_5116536 := by
    simpa [prefixWord, tailWord_5116536, baseEnd_5116536] using wordTrace_append hprefix tailTrace_5116536
  have hstable : (prefixWord ++ tailWord_5116536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116536).length < 2 ^ (prefixWord ++ tailWord_5116536).sum := by decide
  have hdescent : baseEnd_5116536 < baseStart_5116536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116556 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_5116556 : Nat := 118140960795 + 5116556 * 2 ^ 59
def prefixEnd_5116556 : Nat := 4983230072969 + 3 ^ 40 * 5116556 * 2
def baseEnd_5116556 : Nat := 2627252523645988684819393

theorem tailTrace_5116556 : CollatzResearch.WordTrace tailWord_5116556 prefixEnd_5116556 2627252523645988684819393 := by
  unfold tailWord_5116556
  simp only [CollatzResearch.WordTrace]
  refine ⟨93308064225799462520048761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124410752301065950026731681 93308064225799462520048761)
  ·
    refine ⟨69981048169349596890036571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93308064225799462520048761 69981048169349596890036571)
    ·
      refine ⟨104971572254024395335054857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69981048169349596890036571 104971572254024395335054857)
      ·
        refine ⟨78728679190518296501291143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104971572254024395335054857 78728679190518296501291143)
        ·
          refine ⟨118093018785777444751936715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78728679190518296501291143 118093018785777444751936715)
          ·
            refine ⟨177139528178666167127905073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118093018785777444751936715 177139528178666167127905073)
            ·
              refine ⟨132854646133999625345928805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177139528178666167127905073 132854646133999625345928805)
              ·
                refine ⟨24910246150124929752361651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132854646133999625345928805 24910246150124929752361651)
                ·
                  refine ⟨37365369225187394628542477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24910246150124929752361651 37365369225187394628542477)
                  ·
                    refine ⟨14012013459445272985703429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37365369225187394628542477 14012013459445272985703429)
                    ·
                      refine ⟨2627252523645988684819393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14012013459445272985703429 2627252523645988684819393)
                      ·
                        rfl

theorem cell23_5116556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_5116556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116556 prefixEnd_5116556 := by exact prefixLift 5116556
  have htrace : WordTrace (prefixWord ++ tailWord_5116556) baseStart_5116556 baseEnd_5116556 := by
    simpa [prefixWord, tailWord_5116556, baseEnd_5116556] using wordTrace_append hprefix tailTrace_5116556
  have hstable : (prefixWord ++ tailWord_5116556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116556).length < 2 ^ (prefixWord ++ tailWord_5116556).sum := by decide
  have hdescent : baseEnd_5116556 < baseStart_5116556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116573 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_5116573 : Nat := 118140960795 + 5116573 * 2 ^ 59
def prefixEnd_5116573 : Nat := 4983230072969 + 3 ^ 40 * 5116573 * 2
def baseEnd_5116573 : Nat := 2627261252817115118306815

theorem tailTrace_5116573 : CollatzResearch.WordTrace tailWord_5116573 prefixEnd_5116573 2627261252817115118306815 := by
  unfold tailWord_5116573
  simp only [CollatzResearch.WordTrace]
  refine ⟨186616748492537336943466373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124411165661691557962310915 186616748492537336943466373)
  ·
    refine ⟨34990640342350750676899945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186616748492537336943466373 34990640342350750676899945)
    ·
      refine ⟨26242980256763063007674959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34990640342350750676899945 26242980256763063007674959)
      ·
        refine ⟨39364470385144594511512439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26242980256763063007674959 39364470385144594511512439)
        ·
          refine ⟨59046705577716891767268659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39364470385144594511512439 59046705577716891767268659)
          ·
            refine ⟨88570058366575337650902989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59046705577716891767268659 88570058366575337650902989)
            ·
              refine ⟨33213771887465751619088621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88570058366575337650902989 33213771887465751619088621)
              ·
                refine ⟨12455164457799656857158233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33213771887465751619088621 12455164457799656857158233)
                ·
                  refine ⟨9341373343349742642868675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12455164457799656857158233 9341373343349742642868675)
                  ·
                    refine ⟨14012060015024613964303013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9341373343349742642868675 14012060015024613964303013)
                    ·
                      refine ⟨2627261252817115118306815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14012060015024613964303013 2627261252817115118306815)
                      ·
                        rfl

theorem cell23_5116573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_5116573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116573 prefixEnd_5116573 := by exact prefixLift 5116573
  have htrace : WordTrace (prefixWord ++ tailWord_5116573) baseStart_5116573 baseEnd_5116573 := by
    simpa [prefixWord, tailWord_5116573, baseEnd_5116573] using wordTrace_append hprefix tailTrace_5116573
  have hstable : (prefixWord ++ tailWord_5116573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116573).length < 2 ^ (prefixWord ++ tailWord_5116573).sum := by decide
  have hdescent : baseEnd_5116573 < baseStart_5116573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116650 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_5116650 : Nat := 118140960795 + 5116650 * 2 ^ 59
def prefixEnd_5116650 : Nat := 4983230072969 + 3 ^ 40 * 5116650 * 2
def baseEnd_5116650 : Nat := 2627300790827511317043961

theorem tailTrace_5116650 : CollatzResearch.WordTrace tailWord_5116650 prefixEnd_5116650 2627300790827511317043961 := by
  unfold tailWord_5116650
  simp only [CollatzResearch.WordTrace]
  refine ⟨46654889228314594773504851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124413037942172252729346269 46654889228314594773504851)
  ·
    refine ⟨69982333842471892160257277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46654889228314594773504851 69982333842471892160257277)
    ·
      refine ⟨26243375190926959560096479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69982333842471892160257277 26243375190926959560096479)
      ·
        refine ⟨39365062786390439340144719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26243375190926959560096479 39365062786390439340144719)
        ·
          refine ⟨59047594179585659010217079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39365062786390439340144719 59047594179585659010217079)
          ·
            refine ⟨88571391269378488515325619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59047594179585659010217079 88571391269378488515325619)
            ·
              refine ⟨132857086904067732772988429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88571391269378488515325619 132857086904067732772988429)
              ·
                refine ⟨49821407589025399789870661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132857086904067732772988429 49821407589025399789870661)
                ·
                  refine ⟨9341513922942262460600749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49821407589025399789870661 9341513922942262460600749)
                  ·
                    refine ⟨3503067721103348422725281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9341513922942262460600749 3503067721103348422725281)
                    ·
                      refine ⟨2627300790827511317043961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3503067721103348422725281 2627300790827511317043961)
                      ·
                        rfl

theorem cell23_5116650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_5116650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116650 prefixEnd_5116650 := by exact prefixLift 5116650
  have htrace : WordTrace (prefixWord ++ tailWord_5116650) baseStart_5116650 baseEnd_5116650 := by
    simpa [prefixWord, tailWord_5116650, baseEnd_5116650] using wordTrace_append hprefix tailTrace_5116650
  have hstable : (prefixWord ++ tailWord_5116650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116650).length < 2 ^ (prefixWord ++ tailWord_5116650).sum := by decide
  have hdescent : baseEnd_5116650 < baseStart_5116650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116657 : List Nat := [1, 2, 2, 2, 2, 2, 1, 6, 1, 1, 3]
def baseStart_5116657 : Nat := 118140960795 + 5116657 * 2 ^ 59
def prefixEnd_5116657 : Nat := 4983230072969 + 3 ^ 40 * 5116657 * 2
def baseEnd_5116657 : Nat := 2627304385192092789656429

theorem tailTrace_5116657 : CollatzResearch.WordTrace tailWord_5116657 prefixEnd_5116657 2627304385192092789656429 := by
  unfold tailWord_5116657
  simp only [CollatzResearch.WordTrace]
  refine ⟨186619812224233019289524225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124413208149488679526349483 186619812224233019289524225)
  ·
    refine ⟨139964859168174764467143169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186619812224233019289524225 139964859168174764467143169)
    ·
      refine ⟨104973644376131073350357377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139964859168174764467143169 104973644376131073350357377)
      ·
        refine ⟨78730233282098305012768033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104973644376131073350357377 78730233282098305012768033)
        ·
          refine ⟨59047674961573728759576025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78730233282098305012768033 59047674961573728759576025)
          ·
            refine ⟨44285756221180296569682019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59047674961573728759576025 44285756221180296569682019)
            ·
              refine ⟨66428634331770444854523029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44285756221180296569682019 66428634331770444854523029)
              ·
                refine ⟨3113842234301739602555767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66428634331770444854523029 3113842234301739602555767)
                ·
                  refine ⟨4670763351452609403833651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3113842234301739602555767 4670763351452609403833651)
                  ·
                    refine ⟨7006145027178914105750477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4670763351452609403833651 7006145027178914105750477)
                    ·
                      refine ⟨2627304385192092789656429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7006145027178914105750477 2627304385192092789656429)
                      ·
                        rfl

theorem cell23_5116657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_5116657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116657 prefixEnd_5116657 := by exact prefixLift 5116657
  have htrace : WordTrace (prefixWord ++ tailWord_5116657) baseStart_5116657 baseEnd_5116657 := by
    simpa [prefixWord, tailWord_5116657, baseEnd_5116657] using wordTrace_append hprefix tailTrace_5116657
  have hstable : (prefixWord ++ tailWord_5116657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116657).length < 2 ^ (prefixWord ++ tailWord_5116657).sum := by decide
  have hdescent : baseEnd_5116657 < baseStart_5116657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116680 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_5116680 : Nat := 118140960795 + 5116680 * 2 ^ 59
def prefixEnd_5116680 : Nat := 4983230072969 + 3 ^ 40 * 5116680 * 2
def baseEnd_5116680 : Nat := 2627316195247146199668823

theorem tailTrace_5116680 : CollatzResearch.WordTrace tailWord_5116680 prefixEnd_5116680 2627316195247146199668823 := by
  unfold tailWord_5116680
  simp only [CollatzResearch.WordTrace]
  refine ⟨93310325551574847108805747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124413767402099796145074329 93310325551574847108805747)
  ·
    refine ⟨139965488327362270663208621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93310325551574847108805747 139965488327362270663208621)
    ·
      refine ⟨52487058122760851498703233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139965488327362270663208621 52487058122760851498703233)
      ·
        refine ⟨39365293592070638624027425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52487058122760851498703233 39365293592070638624027425)
        ·
          refine ⟨29523970194052978968020569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39365293592070638624027425 29523970194052978968020569)
          ·
            refine ⟨22142977645539734226015427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29523970194052978968020569 22142977645539734226015427)
            ·
              refine ⟨33214466468309601339023141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22142977645539734226015427 33214466468309601339023141)
              ·
                refine ⟨6227712462808050251066839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33214466468309601339023141 6227712462808050251066839)
                ·
                  refine ⟨9341568694212075376600259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6227712462808050251066839 9341568694212075376600259)
                  ·
                    refine ⟨14012353041318113064900389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9341568694212075376600259 14012353041318113064900389)
                    ·
                      refine ⟨2627316195247146199668823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14012353041318113064900389 2627316195247146199668823)
                      ·
                        rfl

theorem cell23_5116680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_5116680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116680 prefixEnd_5116680 := by exact prefixLift 5116680
  have htrace : WordTrace (prefixWord ++ tailWord_5116680) baseStart_5116680 baseEnd_5116680 := by
    simpa [prefixWord, tailWord_5116680, baseEnd_5116680] using wordTrace_append hprefix tailTrace_5116680
  have hstable : (prefixWord ++ tailWord_5116680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116680).length < 2 ^ (prefixWord ++ tailWord_5116680).sum := by decide
  have hdescent : baseEnd_5116680 < baseStart_5116680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116693 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_5116693 : Nat := 118140960795 + 5116693 * 2 ^ 59
def prefixEnd_5116693 : Nat := 4983230072969 + 3 ^ 40 * 5116693 * 2
def baseEnd_5116693 : Nat := 2627322870495654648806263

theorem tailTrace_5116693 : CollatzResearch.WordTrace tailWord_5116693 prefixEnd_5116693 2627322870495654648806263 := by
  unfold tailWord_5116693
  simp only [CollatzResearch.WordTrace]
  refine ⟨186621125252102597437834733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124414083501401731625223155 186621125252102597437834733)
  ·
    refine ⟨69982921969538474039188025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186621125252102597437834733 69982921969538474039188025)
    ·
      refine ⟨52487191477153855529391019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69982921969538474039188025 52487191477153855529391019)
      ·
        refine ⟨78730787215730783294086529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52487191477153855529391019 78730787215730783294086529)
        ·
          refine ⟨59048090411798087470564897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78730787215730783294086529 59048090411798087470564897)
          ·
            refine ⟨44286067808848565602923673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59048090411798087470564897 44286067808848565602923673)
            ·
              refine ⟨33214550856636424202192755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44286067808848565602923673 33214550856636424202192755)
              ·
                refine ⟨49821826284954636303289133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33214550856636424202192755 49821826284954636303289133)
                ·
                  refine ⟨18683184856857988613733425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49821826284954636303289133 18683184856857988613733425)
                  ·
                    refine ⟨14012388642643491460300069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18683184856857988613733425 14012388642643491460300069)
                    ·
                      refine ⟨2627322870495654648806263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14012388642643491460300069 2627322870495654648806263)
                      ·
                        rfl

theorem cell23_5116693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_5116693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116693 prefixEnd_5116693 := by exact prefixLift 5116693
  have htrace : WordTrace (prefixWord ++ tailWord_5116693) baseStart_5116693 baseEnd_5116693 := by
    simpa [prefixWord, tailWord_5116693, baseEnd_5116693] using wordTrace_append hprefix tailTrace_5116693
  have hstable : (prefixWord ++ tailWord_5116693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116693).length < 2 ^ (prefixWord ++ tailWord_5116693).sum := by decide
  have hdescent : baseEnd_5116693 < baseStart_5116693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116700 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_5116700 : Nat := 118140960795 + 5116700 * 2 ^ 59
def prefixEnd_5116700 : Nat := 4983230072969 + 3 ^ 40 * 5116700 * 2
def baseEnd_5116700 : Nat := 2627326464860236121418731

theorem tailTrace_5116700 : CollatzResearch.WordTrace tailWord_5116700 prefixEnd_5116700 2627326464860236121418731 := by
  unfold tailWord_5116700
  simp only [CollatzResearch.WordTrace]
  refine ⟨93310690281538618816669777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124414253708718158422226369 93310690281538618816669777)
  ·
    refine ⟨69983017711153964112502333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93310690281538618816669777 69983017711153964112502333)
    ·
      refine ⟨26243631641682736542188375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69983017711153964112502333 26243631641682736542188375)
      ·
        refine ⟨39365447462524104813282563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26243631641682736542188375 39365447462524104813282563)
        ·
          refine ⟨59048171193786157219923845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39365447462524104813282563 59048171193786157219923845)
          ·
            refine ⟨11071532098834904478735721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59048171193786157219923845 11071532098834904478735721)
            ·
              refine ⟨8303649074126178359051791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11071532098834904478735721 8303649074126178359051791)
              ·
                refine ⟨12455473611189267538577687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8303649074126178359051791 12455473611189267538577687)
                ·
                  refine ⟨18683210416783901307866531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12455473611189267538577687 18683210416783901307866531)
                  ·
                    refine ⟨28024815625175851961799797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18683210416783901307866531 28024815625175851961799797)
                    ·
                      refine ⟨2627326464860236121418731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28024815625175851961799797 2627326464860236121418731)
                      ·
                        rfl

theorem cell23_5116700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_5116700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116700 prefixEnd_5116700 := by exact prefixLift 5116700
  have htrace : WordTrace (prefixWord ++ tailWord_5116700) baseStart_5116700 baseEnd_5116700 := by
    simpa [prefixWord, tailWord_5116700, baseEnd_5116700] using wordTrace_append hprefix tailTrace_5116700
  have hstable : (prefixWord ++ tailWord_5116700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116700).length < 2 ^ (prefixWord ++ tailWord_5116700).sum := by decide
  have hdescent : baseEnd_5116700 < baseStart_5116700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116703 : List Nat := [1, 1, 2, 4, 2, 4, 9]
def baseStart_5116703 : Nat := 118140960795 + 5116703 * 2 ^ 59
def prefixEnd_5116703 : Nat := 4983230072969 + 3 ^ 40 * 5116703 * 2
def baseEnd_5116703 : Nat := 32436148213607402588657

theorem tailTrace_5116703 : CollatzResearch.WordTrace tailWord_5116703 prefixEnd_5116703 32436148213607402588657 := by
  unfold tailWord_5116703
  simp only [CollatzResearch.WordTrace]
  refine ⟨186621489982066369145698763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124414326654710912763799175 186621489982066369145698763)
  ·
    refine ⟨279932234973099553718548145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186621489982066369145698763 279932234973099553718548145)
    ·
      refine ⟨209949176229824665288911109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279932234973099553718548145 209949176229824665288911109)
      ·
        refine ⟨39365470543092124741670833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209949176229824665288911109 39365470543092124741670833)
        ·
          refine ⟨29524102907319093556253125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39365470543092124741670833 29524102907319093556253125)
          ·
            refine ⟨5535769295122330041797461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29524102907319093556253125 5535769295122330041797461)
            ·
              refine ⟨32436148213607402588657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5535769295122330041797461 32436148213607402588657)
              ·
                rfl

theorem cell23_5116703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 9].length) (baseStart_5116703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116703 prefixEnd_5116703 := by exact prefixLift 5116703
  have htrace : WordTrace (prefixWord ++ tailWord_5116703) baseStart_5116703 baseEnd_5116703 := by
    simpa [prefixWord, tailWord_5116703, baseEnd_5116703] using wordTrace_append hprefix tailTrace_5116703
  have hstable : (prefixWord ++ tailWord_5116703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116703).length < 2 ^ (prefixWord ++ tailWord_5116703).sum := by decide
  have hdescent : baseEnd_5116703 < baseStart_5116703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116713 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 3, 3, 3]
def baseStart_5116713 : Nat := 118140960795 + 5116713 * 2 ^ 59
def prefixEnd_5116713 : Nat := 4983230072969 + 3 ^ 40 * 5116713 * 2
def baseEnd_5116713 : Nat := 2627333140108744570556171

theorem tailTrace_5116713 : CollatzResearch.WordTrace tailWord_5116713 prefixEnd_5116713 2627333140108744570556171 := by
  unfold tailWord_5116713
  simp only [CollatzResearch.WordTrace]
  refine ⟨186621854712030140853562793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124414569808020093902375195 186621854712030140853562793)
  ·
    refine ⟨139966391034022605640172095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186621854712030140853562793 139966391034022605640172095)
    ·
      refine ⟨209949586551033908460258143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139966391034022605640172095 209949586551033908460258143)
      ·
        refine ⟨314924379826550862690387215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209949586551033908460258143 314924379826550862690387215)
        ·
          refine ⟨472386569739826294035580823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314924379826550862690387215 472386569739826294035580823)
          ·
            refine ⟨708579854609739441053371235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472386569739826294035580823 708579854609739441053371235)
            ·
              refine ⟨1062869781914609161580056853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708579854609739441053371235 1062869781914609161580056853)
              ·
                refine ⟨49822021027247304449065165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1062869781914609161580056853 49822021027247304449065165)
                ·
                  refine ⟨18683257885217739168399437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49822021027247304449065165 18683257885217739168399437)
                  ·
                    refine ⟨7006221706956652188149789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18683257885217739168399437 7006221706956652188149789)
                    ·
                      refine ⟨2627333140108744570556171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7006221706956652188149789 2627333140108744570556171)
                      ·
                        rfl

theorem cell23_5116713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3, 3].length) (baseStart_5116713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116713 prefixEnd_5116713 := by exact prefixLift 5116713
  have htrace : WordTrace (prefixWord ++ tailWord_5116713) baseStart_5116713 baseEnd_5116713 := by
    simpa [prefixWord, tailWord_5116713, baseEnd_5116713] using wordTrace_append hprefix tailTrace_5116713
  have hstable : (prefixWord ++ tailWord_5116713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116713).length < 2 ^ (prefixWord ++ tailWord_5116713).sum := by decide
  have hdescent : baseEnd_5116713 < baseStart_5116713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116724 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_5116724 : Nat := 118140960795 + 5116724 * 2 ^ 59
def prefixEnd_5116724 : Nat := 4983230072969 + 3 ^ 40 * 5116724 * 2
def baseEnd_5116724 : Nat := 875779596131981342506207

theorem tailTrace_5116724 : CollatzResearch.WordTrace tailWord_5116724 prefixEnd_5116724 875779596131981342506207 := by
  unfold tailWord_5116724
  simp only [CollatzResearch.WordTrace]
  refine ⟨93311127957495144866106613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124414837276660193154808817 93311127957495144866106613)
  ·
    refine ⟨8747918246015169831197495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93311127957495144866106613 8747918246015169831197495)
    ·
      refine ⟨13121877369022754746796243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8747918246015169831197495 13121877369022754746796243)
      ·
        refine ⟨19682816053534132120194365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13121877369022754746796243 19682816053534132120194365)
        ·
          refine ⟨7381056020075299545072887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19682816053534132120194365 7381056020075299545072887)
          ·
            refine ⟨11071584030112949317609331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7381056020075299545072887 11071584030112949317609331)
            ·
              refine ⟨16607376045169423976413997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11071584030112949317609331 16607376045169423976413997)
              ·
                refine ⟨6227766016938533991155249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16607376045169423976413997 6227766016938533991155249)
                ·
                  refine ⟨4670824512703900493366437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6227766016938533991155249 4670824512703900493366437)
                  ·
                    refine ⟨875779596131981342506207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4670824512703900493366437 875779596131981342506207)
                    ·
                      rfl

theorem cell23_5116724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_5116724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116724 prefixEnd_5116724 := by exact prefixLift 5116724
  have htrace : WordTrace (prefixWord ++ tailWord_5116724) baseStart_5116724 baseEnd_5116724 := by
    simpa [prefixWord, tailWord_5116724, baseEnd_5116724] using wordTrace_append hprefix tailTrace_5116724
  have hstable : (prefixWord ++ tailWord_5116724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116724).length < 2 ^ (prefixWord ++ tailWord_5116724).sum := by decide
  have hdescent : baseEnd_5116724 < baseStart_5116724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116764 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_5116764 : Nat := 118140960795 + 5116764 * 2 ^ 59
def prefixEnd_5116764 : Nat := 4983230072969 + 3 ^ 40 * 5116764 * 2
def baseEnd_5116764 : Nat := 2627359327622123871018437

theorem tailTrace_5116764 : CollatzResearch.WordTrace tailWord_5116764 prefixEnd_5116764 2627359327622123871018437 := by
  unfold tailWord_5116764
  simp only [CollatzResearch.WordTrace]
  refine ⟨93311857417422688281834673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124415809889896917709112897 93311857417422688281834673)
  ·
    refine ⟨69983893063067016211376005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93311857417422688281834673 69983893063067016211376005)
    ·
      refine ⟨13121979949325065539633001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69983893063067016211376005 13121979949325065539633001)
      ·
        refine ⟨9841484961993799154724751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13121979949325065539633001 9841484961993799154724751)
        ·
          refine ⟨14762227442990698732087127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9841484961993799154724751 14762227442990698732087127)
          ·
            refine ⟨22143341164486048098130691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14762227442990698732087127 22143341164486048098130691)
            ·
              refine ⟨33215011746729072147196037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22143341164486048098130691 33215011746729072147196037)
              ·
                refine ⟨6227814702511701027599257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33215011746729072147196037 6227814702511701027599257)
                ·
                  refine ⟨4670861026883775770699443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6227814702511701027599257 4670861026883775770699443)
                  ·
                    refine ⟨7006291540325663656049165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4670861026883775770699443 7006291540325663656049165)
                    ·
                      refine ⟨2627359327622123871018437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7006291540325663656049165 2627359327622123871018437)
                      ·
                        rfl

theorem cell23_5116764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_5116764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116764 prefixEnd_5116764 := by exact prefixLift 5116764
  have htrace : WordTrace (prefixWord ++ tailWord_5116764) baseStart_5116764 baseEnd_5116764 := by
    simpa [prefixWord, tailWord_5116764, baseEnd_5116764] using wordTrace_append hprefix tailTrace_5116764
  have hstable : (prefixWord ++ tailWord_5116764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116764).length < 2 ^ (prefixWord ++ tailWord_5116764).sum := by decide
  have hdescent : baseEnd_5116764 < baseStart_5116764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116773 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_5116773 : Nat := 118140960795 + 5116773 * 2 ^ 59
def prefixEnd_5116773 : Nat := 4983230072969 + 3 ^ 40 * 5116773 * 2
def baseEnd_5116773 : Nat := 2627363948948014335805895

theorem tailTrace_5116773 : CollatzResearch.WordTrace tailWord_5116773 prefixEnd_5116773 2627363948948014335805895 := by
  unfold tailWord_5116773
  simp only [CollatzResearch.WordTrace]
  refine ⟨186624043091812771100746973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124416028727875180733831315 186624043091812771100746973)
  ·
    refine ⟨69984016159429789162780115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186624043091812771100746973 69984016159429789162780115)
    ·
      refine ⟨104976024239144683744170173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69984016159429789162780115 104976024239144683744170173)
      ·
        refine ⟨39366009089679256404063815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104976024239144683744170173 39366009089679256404063815)
        ·
          refine ⟨59049013634518884606095723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39366009089679256404063815 59049013634518884606095723)
          ·
            refine ⟨88573520451778326909143585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59049013634518884606095723 88573520451778326909143585)
            ·
              refine ⟨66430140338833745181857689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88573520451778326909143585 66430140338833745181857689)
              ·
                refine ⟨49822605254125308886393267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66430140338833745181857689 49822605254125308886393267)
                ·
                  refine ⟨74733907881187963329589901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49822605254125308886393267 74733907881187963329589901)
                  ·
                    refine ⟨28025215455445486248596213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74733907881187963329589901 28025215455445486248596213)
                    ·
                      refine ⟨2627363948948014335805895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28025215455445486248596213 2627363948948014335805895)
                      ·
                        rfl

theorem cell23_5116773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_5116773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116773 prefixEnd_5116773 := by exact prefixLift 5116773
  have htrace : WordTrace (prefixWord ++ tailWord_5116773) baseStart_5116773 baseEnd_5116773 := by
    simpa [prefixWord, tailWord_5116773, baseEnd_5116773] using wordTrace_append hprefix tailTrace_5116773
  have hstable : (prefixWord ++ tailWord_5116773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116773).length < 2 ^ (prefixWord ++ tailWord_5116773).sum := by decide
  have hdescent : baseEnd_5116773 < baseStart_5116773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116793 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 9]
def baseStart_5116793 : Nat := 118140960795 + 5116793 * 2 ^ 59
def prefixEnd_5116793 : Nat := 4983230072969 + 3 ^ 40 * 5116793 * 2
def baseEnd_5116793 : Nat := 291930468729011584172867

theorem tailTrace_5116793 : CollatzResearch.WordTrace tailWord_5116793 prefixEnd_5116793 291930468729011584172867 := by
  unfold tailWord_5116793
  simp only [CollatzResearch.WordTrace]
  refine ⟨186624772551740314516475033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124416515034493543010983355 186624772551740314516475033)
  ·
    refine ⟨139968579413805235887356275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186624772551740314516475033 139968579413805235887356275)
    ·
      refine ⟨209952869120707853831034413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139968579413805235887356275 209952869120707853831034413)
      ·
        refine ⟨78732325920265445186637905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209952869120707853831034413 78732325920265445186637905)
        ·
          refine ⟨59049244440199083889978429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78732325920265445186637905 59049244440199083889978429)
          ·
            refine ⟨22143466665074656458741911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59049244440199083889978429 22143466665074656458741911)
            ·
              refine ⟨33215199997611984688112867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22143466665074656458741911 33215199997611984688112867)
              ·
                refine ⟨49822799996417977032169301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33215199997611984688112867 49822799996417977032169301)
                ·
                  refine ⟨291930468729011584172867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49822799996417977032169301 291930468729011584172867)
                  ·
                    rfl

theorem cell23_5116793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 9].length) (baseStart_5116793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116793 prefixEnd_5116793 := by exact prefixLift 5116793
  have htrace : WordTrace (prefixWord ++ tailWord_5116793) baseStart_5116793 baseEnd_5116793 := by
    simpa [prefixWord, tailWord_5116793, baseEnd_5116793] using wordTrace_append hprefix tailTrace_5116793
  have hstable : (prefixWord ++ tailWord_5116793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116793).length < 2 ^ (prefixWord ++ tailWord_5116793).sum := by decide
  have hdescent : baseEnd_5116793 < baseStart_5116793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116821 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 2, 2, 2]
def baseStart_5116821 : Nat := 118140960795 + 5116821 * 2 ^ 59
def prefixEnd_5116821 : Nat := 4983230072969 + 3 ^ 40 * 5116821 * 2
def baseEnd_5116821 : Nat := 2627388596019430148005675

theorem tailTrace_5116821 : CollatzResearch.WordTrace tailWord_5116821 prefixEnd_5116821 2627388596019430148005675 := by
  unfold tailWord_5116821
  simp only [CollatzResearch.WordTrace]
  refine ⟨186625793795638875298494317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124417195863759250198996211 186625793795638875298494317)
  ·
    refine ⟨69984672673364578236935369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186625793795638875298494317 69984672673364578236935369)
    ·
      refine ⟨52488504505023433677701527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69984672673364578236935369 52488504505023433677701527)
      ·
        refine ⟨78732756757535150516552291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52488504505023433677701527 78732756757535150516552291)
        ·
          refine ⟨118099135136302725774828437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78732756757535150516552291 118099135136302725774828437)
          ·
            refine ⟨5535896959514190270695083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118099135136302725774828437 5535896959514190270695083)
            ·
              refine ⟨8303845439271285406042625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5535896959514190270695083 8303845439271285406042625)
              ·
                refine ⟨6227884079453464054531969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8303845439271285406042625 6227884079453464054531969)
                ·
                  refine ⟨4670913059590098040898977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6227884079453464054531969 4670913059590098040898977)
                  ·
                    refine ⟨3503184794692573530674233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4670913059590098040898977 3503184794692573530674233)
                    ·
                      refine ⟨2627388596019430148005675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3503184794692573530674233 2627388596019430148005675)
                      ·
                        rfl

theorem cell23_5116821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_5116821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116821 prefixEnd_5116821 := by exact prefixLift 5116821
  have htrace : WordTrace (prefixWord ++ tailWord_5116821) baseStart_5116821 baseEnd_5116821 := by
    simpa [prefixWord, tailWord_5116821, baseEnd_5116821] using wordTrace_append hprefix tailTrace_5116821
  have hstable : (prefixWord ++ tailWord_5116821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116821).length < 2 ^ (prefixWord ++ tailWord_5116821).sum := by decide
  have hdescent : baseEnd_5116821 < baseStart_5116821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116861 : List Nat := [1, 4, 1, 2, 5, 1, 1, 3, 5]
def baseStart_5116861 : Nat := 118140960795 + 5116861 * 2 ^ 59
def prefixEnd_5116861 : Nat := 4983230072969 + 3 ^ 40 * 5116861 * 2
def baseEnd_5116861 : Nat := 291934348360623332389499

theorem tailTrace_5116861 : CollatzResearch.WordTrace tailWord_5116861 prefixEnd_5116861 291934348360623332389499 := by
  unfold tailWord_5116861
  simp only [CollatzResearch.WordTrace]
  refine ⟨186627252715493962129950437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124418168476995974753300291 186627252715493962129950437)
  ·
    refine ⟨34992609884155117899365707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186627252715493962129950437 34992609884155117899365707)
    ·
      refine ⟨52488914826232676849048561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34992609884155117899365707 52488914826232676849048561)
      ·
        refine ⟨39366686119674507636786421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52488914826232676849048561 39366686119674507636786421)
        ·
          refine ⟨3690626823719485090948727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39366686119674507636786421 3690626823719485090948727)
          ·
            refine ⟨5535940235579227636423091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3690626823719485090948727 5535940235579227636423091)
            ·
              refine ⟨8303910353368841454634637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5535940235579227636423091 8303910353368841454634637)
              ·
                refine ⟨3113966382513315545487989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8303910353368841454634637 3113966382513315545487989)
                ·
                  refine ⟨291934348360623332389499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3113966382513315545487989 291934348360623332389499)
                  ·
                    rfl

theorem cell23_5116861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_5116861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116861 prefixEnd_5116861 := by exact prefixLift 5116861
  have htrace : WordTrace (prefixWord ++ tailWord_5116861) baseStart_5116861 baseEnd_5116861 := by
    simpa [prefixWord, tailWord_5116861, baseEnd_5116861] using wordTrace_append hprefix tailTrace_5116861
  have hstable : (prefixWord ++ tailWord_5116861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116861).length < 2 ^ (prefixWord ++ tailWord_5116861).sum := by decide
  have hdescent : baseEnd_5116861 < baseStart_5116861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116938 : List Nat := [3, 1, 2, 2, 3, 3, 2, 2, 1, 4]
def baseStart_5116938 : Nat := 118140960795 + 5116938 * 2 ^ 59
def prefixEnd_5116938 : Nat := 4983230072969 + 3 ^ 40 * 5116938 * 2
def baseEnd_5116938 : Nat := 875816224418668730080879

theorem tailTrace_5116938 : CollatzResearch.WordTrace tailWord_5116938 prefixEnd_5116938 875816224418668730080879 := by
  unfold tailWord_5116938
  simp only [CollatzResearch.WordTrace]
  refine ⟨46657515284053751070125867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124420040757476669520335645 46657515284053751070125867)
  ·
    refine ⟨69986272926080626605188801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46657515284053751070125867 69986272926080626605188801)
    ·
      refine ⟨52489704694560469953891601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69986272926080626605188801 52489704694560469953891601)
      ·
        refine ⟨39367278520920352465418701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52489704694560469953891601 39367278520920352465418701)
        ·
          refine ⟨14762729445345132174532013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39367278520920352465418701 14762729445345132174532013)
          ·
            refine ⟨5536023542004424565449505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14762729445345132174532013 5536023542004424565449505)
            ·
              refine ⟨4152017656503318424087129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5536023542004424565449505 4152017656503318424087129)
              ·
                refine ⟨3114013242377488818065347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4152017656503318424087129 3114013242377488818065347)
                ·
                  refine ⟨4671019863566233227098021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114013242377488818065347 4671019863566233227098021)
                  ·
                    refine ⟨875816224418668730080879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4671019863566233227098021 875816224418668730080879)
                    ·
                      rfl

theorem cell23_5116938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_5116938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116938 prefixEnd_5116938 := by exact prefixLift 5116938
  have htrace : WordTrace (prefixWord ++ tailWord_5116938) baseStart_5116938 baseEnd_5116938 := by
    simpa [prefixWord, tailWord_5116938, baseEnd_5116938] using wordTrace_append hprefix tailTrace_5116938
  have hstable : (prefixWord ++ tailWord_5116938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116938).length < 2 ^ (prefixWord ++ tailWord_5116938).sum := by decide
  have hdescent : baseEnd_5116938 < baseStart_5116938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116977 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 4, 4]
def baseStart_5116977 : Nat := 118140960795 + 5116977 * 2 ^ 59
def prefixEnd_5116977 : Nat := 4983230072969 + 3 ^ 40 * 5116977 * 2
def baseEnd_5116977 : Nat := 875822899667177179218319

theorem tailTrace_5116977 : CollatzResearch.WordTrace tailWord_5116977 prefixEnd_5116977 875822899667177179218319 := by
  unfold tailWord_5116977
  simp only [CollatzResearch.WordTrace]
  refine ⟨186631483583073713941173185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124420989055382475960782123 186631483583073713941173185)
  ·
    refine ⟨139973612687305285455879889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186631483583073713941173185 139973612687305285455879889)
    ·
      refine ⟨104980209515478964091909917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139973612687305285455879889 104980209515478964091909917)
      ·
        refine ⟨39367578568304611534466219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104980209515478964091909917 39367578568304611534466219)
        ·
          refine ⟨59051367852456917301699329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39367578568304611534466219 59051367852456917301699329)
          ·
            refine ⟨44288525889342687976274497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59051367852456917301699329 44288525889342687976274497)
            ·
              refine ⟨33216394417007015982205873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44288525889342687976274497 33216394417007015982205873)
              ·
                refine ⟨24912295812755261986654405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33216394417007015982205873 24912295812755261986654405)
                ·
                  refine ⟨4671055464891611622497701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24912295812755261986654405 4671055464891611622497701)
                  ·
                    refine ⟨875822899667177179218319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4671055464891611622497701 875822899667177179218319)
                    ·
                      rfl

theorem cell23_5116977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_5116977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116977 prefixEnd_5116977 := by exact prefixLift 5116977
  have htrace : WordTrace (prefixWord ++ tailWord_5116977) baseStart_5116977 baseEnd_5116977 := by
    simpa [prefixWord, tailWord_5116977, baseEnd_5116977] using wordTrace_append hprefix tailTrace_5116977
  have hstable : (prefixWord ++ tailWord_5116977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116977).length < 2 ^ (prefixWord ++ tailWord_5116977).sum := by decide
  have hdescent : baseEnd_5116977 < baseStart_5116977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5116984 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 1, 1, 4]
def baseStart_5116984 : Nat := 118140960795 + 5116984 * 2 ^ 59
def prefixEnd_5116984 : Nat := 4983230072969 + 3 ^ 40 * 5116984 * 2
def baseEnd_5116984 : Nat := 2627472293366113010267425

theorem tailTrace_5116984 : CollatzResearch.WordTrace tailWord_5116984 prefixEnd_5116984 2627472293366113010267425 := by
  unfold tailWord_5116984
  simp only [CollatzResearch.WordTrace]
  refine ⟨93315869447024177068339003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124421159262698902757785337 93315869447024177068339003)
  ·
    refine ⟨139973804170536265602508505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93315869447024177068339003 139973804170536265602508505)
    ·
      refine ⟨104980353127902199201881379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139973804170536265602508505 104980353127902199201881379)
      ·
        refine ⟨157470529691853298802822069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104980353127902199201881379 157470529691853298802822069)
        ·
          refine ⟨14762862158611246762764569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157470529691853298802822069 14762862158611246762764569)
          ·
            refine ⟨11072146618958435072073427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14762862158611246762764569 11072146618958435072073427)
            ·
              refine ⟨16608219928437652608110141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11072146618958435072073427 16608219928437652608110141)
              ·
                refine ⟨6228082473164119728041303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16608219928437652608110141 6228082473164119728041303)
                ·
                  refine ⟨9342123709746179592061955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6228082473164119728041303 9342123709746179592061955)
                  ·
                    refine ⟨14013185564619269388092933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9342123709746179592061955 14013185564619269388092933)
                    ·
                      refine ⟨2627472293366113010267425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14013185564619269388092933 2627472293366113010267425)
                      ·
                        rfl

theorem cell23_5116984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_5116984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5116984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5116984 prefixEnd_5116984 := by exact prefixLift 5116984
  have htrace : WordTrace (prefixWord ++ tailWord_5116984) baseStart_5116984 baseEnd_5116984 := by
    simpa [prefixWord, tailWord_5116984, baseEnd_5116984] using wordTrace_append hprefix tailTrace_5116984
  have hstable : (prefixWord ++ tailWord_5116984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5116984).length < 2 ^ (prefixWord ++ tailWord_5116984).sum := by decide
  have hdescent : baseEnd_5116984 < baseStart_5116984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5116984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117017 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 1, 3, 3]
def baseStart_5117017 : Nat := 118140960795 + 5117017 * 2 ^ 59
def prefixEnd_5117017 : Nat := 4983230072969 + 3 ^ 40 * 5117017 * 2
def baseEnd_5117017 : Nat := 2627489238227711381154773

theorem tailTrace_5117017 : CollatzResearch.WordTrace tailWord_5117017 prefixEnd_5117017 2627489238227711381154773 := by
  unfold tailWord_5117017
  simp only [CollatzResearch.WordTrace]
  refine ⟨186632942502928800772629305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124421961668619200515086203 186632942502928800772629305)
  ·
    refine ⟨139974706877196600579471979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186632942502928800772629305 139974706877196600579471979)
    ·
      refine ⟨209962060315794900869207969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139974706877196600579471979 209962060315794900869207969)
      ·
        refine ⟨157471545236846175651905977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209962060315794900869207969 157471545236846175651905977)
        ·
          refine ⟨118103658927634631738929483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157471545236846175651905977 118103658927634631738929483)
          ·
            refine ⟨177155488391451947608394225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118103658927634631738929483 177155488391451947608394225)
            ·
              refine ⟨132866616293588960706295669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177155488391451947608394225 132866616293588960706295669)
              ·
                refine ⟨12456245277523965066215219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132866616293588960706295669 12456245277523965066215219)
                ·
                  refine ⟨18684367916285947599322829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12456245277523965066215219 18684367916285947599322829)
                  ·
                    refine ⟨7006637968607230349746061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18684367916285947599322829 7006637968607230349746061)
                    ·
                      refine ⟨2627489238227711381154773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7006637968607230349746061 2627489238227711381154773)
                      ·
                        rfl

theorem cell23_5117017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 3, 3].length) (baseStart_5117017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117017 prefixEnd_5117017 := by exact prefixLift 5117017
  have htrace : WordTrace (prefixWord ++ tailWord_5117017) baseStart_5117017 baseEnd_5117017 := by
    simpa [prefixWord, tailWord_5117017, baseEnd_5117017] using wordTrace_append hprefix tailTrace_5117017
  have hstable : (prefixWord ++ tailWord_5117017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117017).length < 2 ^ (prefixWord ++ tailWord_5117017).sum := by decide
  have hdescent : baseEnd_5117017 < baseStart_5117017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117077 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_5117077 : Nat := 118140960795 + 5117077 * 2 ^ 59
def prefixEnd_5117077 : Nat := 4983230072969 + 3 ^ 40 * 5117077 * 2
def baseEnd_5117077 : Nat := 2627520047066981146404497

theorem tailTrace_5117077 : CollatzResearch.WordTrace tailWord_5117077 prefixEnd_5117077 2627520047066981146404497 := by
  unfold tailWord_5117077
  simp only [CollatzResearch.WordTrace]
  refine ⟨186635130882711431019813485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124423420588474287346542323 186635130882711431019813485)
  ·
    refine ⟨69988174081016786632430057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186635130882711431019813485 69988174081016786632430057)
    ·
      refine ⟨52491130560762589974322543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69988174081016786632430057 52491130560762589974322543)
      ·
        refine ⟨78736695841143884961483815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52491130560762589974322543 78736695841143884961483815)
        ·
          refine ⟨118105043761715827442225723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78736695841143884961483815 118105043761715827442225723)
          ·
            refine ⟨177157565642573741163338585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118105043761715827442225723 177157565642573741163338585)
            ·
              refine ⟨132868174231930305872503939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177157565642573741163338585 132868174231930305872503939)
              ·
                refine ⟨199302261347895458808755909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132868174231930305872503939 199302261347895458808755909)
                ·
                  refine ⟨37369174002730398526641733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199302261347895458808755909 37369174002730398526641733)
                  ·
                    refine ⟨7006720125511949723745325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37369174002730398526641733 7006720125511949723745325)
                    ·
                      refine ⟨2627520047066981146404497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7006720125511949723745325 2627520047066981146404497)
                      ·
                        rfl

theorem cell23_5117077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_5117077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117077 prefixEnd_5117077 := by exact prefixLift 5117077
  have htrace : WordTrace (prefixWord ++ tailWord_5117077) baseStart_5117077 baseEnd_5117077 := by
    simpa [prefixWord, tailWord_5117077, baseEnd_5117077] using wordTrace_append hprefix tailTrace_5117077
  have hstable : (prefixWord ++ tailWord_5117077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117077).length < 2 ^ (prefixWord ++ tailWord_5117077).sum := by decide
  have hdescent : baseEnd_5117077 < baseStart_5117077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117095 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_5117095 : Nat := 118140960795 + 5117095 * 2 ^ 59
def prefixEnd_5117095 : Nat := 4983230072969 + 3 ^ 40 * 5117095 * 2
def baseEnd_5117095 : Nat := 2627529289718762075979415

theorem tailTrace_5117095 : CollatzResearch.WordTrace tailWord_5117095 prefixEnd_5117095 2627529289718762075979415 := by
  unfold tailWord_5117095
  simp only [CollatzResearch.WordTrace]
  refine ⟨186635787396646220093968739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124423858264430813395979159 186635787396646220093968739)
  ·
    refine ⟨279953681094969330140953109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186635787396646220093968739 279953681094969330140953109)
    ·
      refine ⟨13122828801326687350357177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 279953681094969330140953109 13122828801326687350357177)
      ·
        refine ⟨9842121600995015512767883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13122828801326687350357177 9842121600995015512767883)
        ·
          refine ⟨14763182401492523269151825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9842121600995015512767883 14763182401492523269151825)
          ·
            refine ⟨11072386801119392451863869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14763182401492523269151825 11072386801119392451863869)
            ·
              refine ⟨4152145050419772169448951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11072386801119392451863869 4152145050419772169448951)
              ·
                refine ⟨6228217575629658254173427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4152145050419772169448951 6228217575629658254173427)
                ·
                  refine ⟨9342326363444487381260141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6228217575629658254173427 9342326363444487381260141)
                  ·
                    refine ⟨3503372386291682767972553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9342326363444487381260141 3503372386291682767972553)
                    ·
                      refine ⟨2627529289718762075979415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3503372386291682767972553 2627529289718762075979415)
                      ·
                        rfl

theorem cell23_5117095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_5117095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117095 prefixEnd_5117095 := by exact prefixLift 5117095
  have htrace : WordTrace (prefixWord ++ tailWord_5117095) baseStart_5117095 baseEnd_5117095 := by
    simpa [prefixWord, tailWord_5117095, baseEnd_5117095] using wordTrace_append hprefix tailTrace_5117095
  have hstable : (prefixWord ++ tailWord_5117095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117095).length < 2 ^ (prefixWord ++ tailWord_5117095).sum := by decide
  have hdescent : baseEnd_5117095 < baseStart_5117095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117121 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5117121 : Nat := 118140960795 + 5117121 * 2 ^ 59
def prefixEnd_5117121 : Nat := 4983230072969 + 3 ^ 40 * 5117121 * 2
def baseEnd_5117121 : Nat := 2627542640215778974254295

theorem tailTrace_5117121 : CollatzResearch.WordTrace tailWord_5117121 prefixEnd_5117121 2627542640215778974254295 := by
  unfold tailWord_5117121
  simp only [CollatzResearch.WordTrace]
  refine ⟨186636735694552026534415217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124424490463034684356276811 186636735694552026534415217)
  ·
    refine ⟨139977551770914019900811413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186636735694552026534415217 139977551770914019900811413)
    ·
      refine ⟨6561447739261594682850535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139977551770914019900811413 6561447739261594682850535)
      ·
        refine ⟨9842171608892392024275803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6561447739261594682850535 9842171608892392024275803)
        ·
          refine ⟨14763257413338588036413705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9842171608892392024275803 14763257413338588036413705)
          ·
            refine ⟨11072443060003941027310279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14763257413338588036413705 11072443060003941027310279)
            ·
              refine ⟨16608664590005911540965419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11072443060003941027310279 16608664590005911540965419)
              ·
                refine ⟨24912996885008867311448129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16608664590005911540965419 24912996885008867311448129)
                ·
                  refine ⟨18684747663756650483586097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24912996885008867311448129 18684747663756650483586097)
                  ·
                    refine ⟨14013560747817487862689573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18684747663756650483586097 14013560747817487862689573)
                    ·
                      refine ⟨2627542640215778974254295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14013560747817487862689573 2627542640215778974254295)
                      ·
                        rfl

theorem cell23_5117121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5117121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117121 prefixEnd_5117121 := by exact prefixLift 5117121
  have htrace : WordTrace (prefixWord ++ tailWord_5117121) baseStart_5117121 baseEnd_5117121 := by
    simpa [prefixWord, tailWord_5117121, baseEnd_5117121] using wordTrace_append hprefix tailTrace_5117121
  have hstable : (prefixWord ++ tailWord_5117121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117121).length < 2 ^ (prefixWord ++ tailWord_5117121).sum := by decide
  have hdescent : baseEnd_5117121 < baseStart_5117121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117127 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 4, 5]
def baseStart_5117127 : Nat := 118140960795 + 5117127 * 2 ^ 59
def prefixEnd_5117127 : Nat := 4983230072969 + 3 ^ 40 * 5117127 * 2
def baseEnd_5117127 : Nat := 875848573699901983593089

theorem tailTrace_5117127 : CollatzResearch.WordTrace tailWord_5117127 prefixEnd_5117127 875848573699901983593089 := by
  unfold tailWord_5117127
  simp only [CollatzResearch.WordTrace]
  refine ⟨186636954532530289559133635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124424636355020193039422423 186636954532530289559133635)
  ·
    refine ⟨279955431798795434338700453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186636954532530289559133635 279955431798795434338700453)
    ·
      refine ⟨52491643462274143938506335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279955431798795434338700453 52491643462274143938506335)
      ·
        refine ⟨78737465193411215907759503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52491643462274143938506335 78737465193411215907759503)
        ·
          refine ⟨118106197790116823861639255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78737465193411215907759503 118106197790116823861639255)
          ·
            refine ⟨177159296685175235792458883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118106197790116823861639255 177159296685175235792458883)
            ·
              refine ⟨265738945027762853688688325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177159296685175235792458883 265738945027762853688688325)
              ·
                refine ⟨49826052192705535066629061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 265738945027762853688688325 49826052192705535066629061)
                ·
                  refine ⟨9342384786132287824992949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49826052192705535066629061 9342384786132287824992949)
                  ·
                    refine ⟨875848573699901983593089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9342384786132287824992949 875848573699901983593089)
                    ·
                      rfl

theorem cell23_5117127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_5117127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117127 prefixEnd_5117127 := by exact prefixLift 5117127
  have htrace : WordTrace (prefixWord ++ tailWord_5117127) baseStart_5117127 baseEnd_5117127 := by
    simpa [prefixWord, tailWord_5117127, baseEnd_5117127] using wordTrace_append hprefix tailTrace_5117127
  have hstable : (prefixWord ++ tailWord_5117127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117127).length < 2 ^ (prefixWord ++ tailWord_5117127).sum := by decide
  have hdescent : baseEnd_5117127 < baseStart_5117127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117144 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 1, 7]
def baseStart_5117144 : Nat := 118140960795 + 5117144 * 2 ^ 59
def prefixEnd_5117144 : Nat := 4983230072969 + 3 ^ 40 * 5117144 * 2
def baseEnd_5117144 : Nat := 875851483423610794755563

theorem tailTrace_5117144 : CollatzResearch.WordTrace tailWord_5117144 prefixEnd_5117144 875851483423610794755563 := by
  unfold tailWord_5117144
  simp only [CollatzResearch.WordTrace]
  refine ⟨93318787286734350731251243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124425049715645800975001657 93318787286734350731251243)
  ·
    refine ⟨139978180930101526096876865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93318787286734350731251243 139978180930101526096876865)
    ·
      refine ⟨104983635697576144572657649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139978180930101526096876865 104983635697576144572657649)
      ·
        refine ⟨78737726773182108429493237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104983635697576144572657649 78737726773182108429493237)
        ·
          refine ⟨7381661884985822665264991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78737726773182108429493237 7381661884985822665264991)
          ·
            refine ⟨11072492827478733997897487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7381661884985822665264991 11072492827478733997897487)
            ·
              refine ⟨16608739241218100996846231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11072492827478733997897487 16608739241218100996846231)
              ·
                refine ⟨24913108861827151495269347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16608739241218100996846231 24913108861827151495269347)
                ·
                  refine ⟨37369663292740727242904021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24913108861827151495269347 37369663292740727242904021)
                  ·
                    refine ⟨875851483423610794755563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37369663292740727242904021 875851483423610794755563)
                    ·
                      rfl

theorem cell23_5117144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_5117144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117144 prefixEnd_5117144 := by exact prefixLift 5117144
  have htrace : WordTrace (prefixWord ++ tailWord_5117144) baseStart_5117144 baseEnd_5117144 := by
    simpa [prefixWord, tailWord_5117144, baseEnd_5117144] using wordTrace_append hprefix tailTrace_5117144
  have hstable : (prefixWord ++ tailWord_5117144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117144).length < 2 ^ (prefixWord ++ tailWord_5117144).sum := by decide
  have hdescent : baseEnd_5117144 < baseStart_5117144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117177 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_5117177 : Nat := 118140960795 + 5117177 * 2 ^ 59
def prefixEnd_5117177 : Nat := 4983230072969 + 3 ^ 40 * 5117177 * 2
def baseEnd_5117177 : Nat := 2627571395132430755154037

theorem tailTrace_5117177 : CollatzResearch.WordTrace tailWord_5117177 prefixEnd_5117177 2627571395132430755154037 := by
  unfold tailWord_5117177
  simp only [CollatzResearch.WordTrace]
  refine ⟨186638778182349148098453785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124425852121566098732302523 186638778182349148098453785)
  ·
    refine ⟨139979083636761861073840339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186638778182349148098453785 139979083636761861073840339)
    ·
      refine ⟨209968625455142791610760509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139979083636761861073840339 209968625455142791610760509)
      ·
        refine ⟨78738234545678546854035191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209968625455142791610760509 78738234545678546854035191)
        ·
          refine ⟨118107351818517820281052787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78738234545678546854035191 118107351818517820281052787)
          ·
            refine ⟨177161027727776730421579181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118107351818517820281052787 177161027727776730421579181)
            ·
              refine ⟨66435385397916273908092193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177161027727776730421579181 66435385397916273908092193)
              ·
                refine ⟨49826539048437205431069145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66435385397916273908092193 49826539048437205431069145)
                ·
                  refine ⟨37369904286327904073301859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49826539048437205431069145 37369904286327904073301859)
                  ·
                    refine ⟨56054856429491856109952789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37369904286327904073301859 56054856429491856109952789)
                    ·
                      refine ⟨2627571395132430755154037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56054856429491856109952789 2627571395132430755154037)
                      ·
                        rfl

theorem cell23_5117177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_5117177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117177 prefixEnd_5117177 := by exact prefixLift 5117177
  have htrace : WordTrace (prefixWord ++ tailWord_5117177) baseStart_5117177 baseEnd_5117177 := by
    simpa [prefixWord, tailWord_5117177, baseEnd_5117177] using wordTrace_append hprefix tailTrace_5117177
  have hstable : (prefixWord ++ tailWord_5117177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117177).length < 2 ^ (prefixWord ++ tailWord_5117177).sum := by decide
  have hdescent : baseEnd_5117177 < baseStart_5117177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117208 : List Nat := [2, 1, 2, 3, 1, 3, 3, 3, 1, 4]
def baseStart_5117208 : Nat := 118140960795 + 5117208 * 2 ^ 59
def prefixEnd_5117208 : Nat := 4983230072969 + 3 ^ 40 * 5117208 * 2
def baseEnd_5117208 : Nat := 875862437677573377955465

theorem tailTrace_5117208 : CollatzResearch.WordTrace tailWord_5117208 prefixEnd_5117208 875862437677573377955465 := by
  unfold tailWord_5117208
  simp only [CollatzResearch.WordTrace]
  refine ⟨93319954422618420196416139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124426605896824560261888185 93319954422618420196416139)
  ·
    refine ⟨139979931633927630294624209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93319954422618420196416139 139979931633927630294624209)
    ·
      refine ⟨104984948725445722720968157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139979931633927630294624209 104984948725445722720968157)
      ·
        refine ⟨39369355772042146020363059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104984948725445722720968157 39369355772042146020363059)
        ·
          refine ⟨59054033658063219030544589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39369355772042146020363059 59054033658063219030544589)
          ·
            refine ⟨22145262621773707136454221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59054033658063219030544589 22145262621773707136454221)
            ·
              refine ⟨8304473483165140176170333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22145262621773707136454221 8304473483165140176170333)
              ·
                refine ⟨3114177556186927566063875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8304473483165140176170333 3114177556186927566063875)
                ·
                  refine ⟨4671266334280391349095813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114177556186927566063875 4671266334280391349095813)
                  ·
                    refine ⟨875862437677573377955465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4671266334280391349095813 875862437677573377955465)
                    ·
                      rfl

theorem cell23_5117208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_5117208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117208 prefixEnd_5117208 := by exact prefixLift 5117208
  have htrace : WordTrace (prefixWord ++ tailWord_5117208) baseStart_5117208 baseEnd_5117208 := by
    simpa [prefixWord, tailWord_5117208, baseEnd_5117208] using wordTrace_append hprefix tailTrace_5117208
  have hstable : (prefixWord ++ tailWord_5117208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117208).length < 2 ^ (prefixWord ++ tailWord_5117208).sum := by decide
  have hdescent : baseEnd_5117208 < baseStart_5117208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117218 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_5117218 : Nat := 118140960795 + 5117218 * 2 ^ 59
def prefixEnd_5117218 : Nat := 4983230072969 + 3 ^ 40 * 5117218 * 2
def baseEnd_5117218 : Nat := 2627592447839265094741349

theorem tailTrace_5117218 : CollatzResearch.WordTrace tailWord_5117218 prefixEnd_5117218 2627592447839265094741349 := by
  unfold tailWord_5117218
  simp only [CollatzResearch.WordTrace]
  refine ⟨46660068393800153025174077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124426849050133741400464205 46660068393800153025174077)
  ·
    refine ⟨17497525647675057384440279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46660068393800153025174077 17497525647675057384440279)
    ·
      refine ⟨26246288471512586076660419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17497525647675057384440279 26246288471512586076660419)
      ·
        refine ⟨39369432707268879114990629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26246288471512586076660419 39369432707268879114990629)
        ·
          refine ⟨7381768632612914834060743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39369432707268879114990629 7381768632612914834060743)
          ·
            refine ⟨11072652948919372251091115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7381768632612914834060743 11072652948919372251091115)
            ·
              refine ⟨16608979423379058376636673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11072652948919372251091115 16608979423379058376636673)
              ·
                refine ⟨12456734567534293782477505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16608979423379058376636673 12456734567534293782477505)
                ·
                  refine ⟨9342550925650720336858129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12456734567534293782477505 9342550925650720336858129)
                  ·
                    refine ⟨7006913194238040252643597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9342550925650720336858129 7006913194238040252643597)
                    ·
                      refine ⟨2627592447839265094741349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7006913194238040252643597 2627592447839265094741349)
                      ·
                        rfl

theorem cell23_5117218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_5117218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117218 prefixEnd_5117218 := by exact prefixLift 5117218
  have htrace : WordTrace (prefixWord ++ tailWord_5117218) baseStart_5117218 baseEnd_5117218 := by
    simpa [prefixWord, tailWord_5117218, baseEnd_5117218] using wordTrace_append hprefix tailTrace_5117218
  have hstable : (prefixWord ++ tailWord_5117218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117218).length < 2 ^ (prefixWord ++ tailWord_5117218).sum := by decide
  have hdescent : baseEnd_5117218 < baseStart_5117218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117227 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 5]
def baseStart_5117227 : Nat := 118140960795 + 5117227 * 2 ^ 59
def prefixEnd_5117227 : Nat := 4983230072969 + 3 ^ 40 * 5117227 * 2
def baseEnd_5117227 : Nat := 2627597069165155559528807

theorem tailTrace_5117227 : CollatzResearch.WordTrace tailWord_5117227 prefixEnd_5117227 2627597069165155559528807 := by
  unfold tailWord_5117227
  simp only [CollatzResearch.WordTrace]
  refine ⟨186640601832168006637773935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124427067888112004425182623 186640601832168006637773935)
  ·
    refine ⟨279960902748252009956660903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186640601832168006637773935 279960902748252009956660903)
    ·
      refine ⟨419941354122378014934991355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279960902748252009956660903 419941354122378014934991355)
      ·
        refine ⟨629912031183567022402487033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419941354122378014934991355 629912031183567022402487033)
        ·
          refine ⟨472434023387675266801865275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 629912031183567022402487033 472434023387675266801865275)
          ·
            refine ⟨708651035081512900202797913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472434023387675266801865275 708651035081512900202797913)
            ·
              refine ⟨531488276311134675152098435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708651035081512900202797913 531488276311134675152098435)
              ·
                refine ⟨797232414466702012728147653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531488276311134675152098435 797232414466702012728147653)
                ·
                  refine ⟨149481077712506627386527685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 797232414466702012728147653 149481077712506627386527685)
                  ·
                    refine ⟨28027702071094992634973941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149481077712506627386527685 28027702071094992634973941)
                    ·
                      refine ⟨2627597069165155559528807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28027702071094992634973941 2627597069165155559528807)
                      ·
                        rfl

theorem cell23_5117227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_5117227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117227 prefixEnd_5117227 := by exact prefixLift 5117227
  have htrace : WordTrace (prefixWord ++ tailWord_5117227) baseStart_5117227 baseEnd_5117227 := by
    simpa [prefixWord, tailWord_5117227, baseEnd_5117227] using wordTrace_append hprefix tailTrace_5117227
  have hstable : (prefixWord ++ tailWord_5117227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117227).length < 2 ^ (prefixWord ++ tailWord_5117227).sum := by decide
  have hdescent : baseEnd_5117227 < baseStart_5117227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117264 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 1, 6]
def baseStart_5117264 : Nat := 118140960795 + 5117264 * 2 ^ 59
def prefixEnd_5117264 : Nat := 4983230072969 + 3 ^ 40 * 5117264 * 2
def baseEnd_5117264 : Nat := 875872022649790638255379

theorem tailTrace_5117264 : CollatzResearch.WordTrace tailWord_5117264 prefixEnd_5117264 875872022649790638255379 := by
  unfold tailWord_5117264
  simp only [CollatzResearch.WordTrace]
  refine ⟨93320975666516980978435423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124427967555355974637913897 93320975666516980978435423)
  ·
    refine ⟨139981463499775471467653135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93320975666516980978435423 139981463499775471467653135)
    ·
      refine ⟨209972195249663207201479703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139981463499775471467653135 209972195249663207201479703)
      ·
        refine ⟨314958292874494810802219555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209972195249663207201479703 314958292874494810802219555)
        ·
          refine ⟨472437439311742216203329333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314958292874494810802219555 472437439311742216203329333)
          ·
            refine ⟨44291009935475832769062125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 472437439311742216203329333 44291009935475832769062125)
            ·
              refine ⟨16609128725803437288398297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44291009935475832769062125 16609128725803437288398297)
              ·
                refine ⟨12456846544352577966298723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16609128725803437288398297 12456846544352577966298723)
                ·
                  refine ⟨18685269816528866949448085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12456846544352577966298723 18685269816528866949448085)
                  ·
                    refine ⟨875872022649790638255379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18685269816528866949448085 875872022649790638255379)
                    ·
                      rfl

theorem cell23_5117264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_5117264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117264 prefixEnd_5117264 := by exact prefixLift 5117264
  have htrace : WordTrace (prefixWord ++ tailWord_5117264) baseStart_5117264 baseEnd_5117264 := by
    simpa [prefixWord, tailWord_5117264, baseEnd_5117264] using wordTrace_append hprefix tailTrace_5117264
  have hstable : (prefixWord ++ tailWord_5117264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117264).length < 2 ^ (prefixWord ++ tailWord_5117264).sum := by decide
  have hdescent : baseEnd_5117264 < baseStart_5117264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117268 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_5117268 : Nat := 118140960795 + 5117268 * 2 ^ 59
def prefixEnd_5117268 : Nat := 4983230072969 + 3 ^ 40 * 5117268 * 2
def baseEnd_5117268 : Nat := 875872707290663299705373

theorem tailTrace_5117268 : CollatzResearch.WordTrace tailWord_5117268 prefixEnd_5117268 875872707290663299705373 := by
  unfold tailWord_5117268
  simp only [CollatzResearch.WordTrace]
  refine ⟨93321048612509735320008229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124428064816679647093344305 93321048612509735320008229)
  ·
    refine ⟨17497696614845575372501543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93321048612509735320008229 17497696614845575372501543)
    ·
      refine ⟨26246544922268363058752315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17497696614845575372501543 26246544922268363058752315)
      ·
        refine ⟨39369817383402544588128473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26246544922268363058752315 39369817383402544588128473)
        ·
          refine ⟨29527363037551908441096355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39369817383402544588128473 29527363037551908441096355)
          ·
            refine ⟨44291044556327862661644533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29527363037551908441096355 44291044556327862661644533)
            ·
              refine ⟨4152285427155737124529175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44291044556327862661644533 4152285427155737124529175)
              ·
                refine ⟨6228428140733605686793763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4152285427155737124529175 6228428140733605686793763)
                ·
                  refine ⟨9342642211100408530190645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6228428140733605686793763 9342642211100408530190645)
                  ·
                    refine ⟨875872707290663299705373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9342642211100408530190645 875872707290663299705373)
                    ·
                      rfl

theorem cell23_5117268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_5117268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117268 prefixEnd_5117268 := by exact prefixLift 5117268
  have htrace : WordTrace (prefixWord ++ tailWord_5117268) baseStart_5117268 baseEnd_5117268 := by
    simpa [prefixWord, tailWord_5117268, baseEnd_5117268] using wordTrace_append hprefix tailTrace_5117268
  have hstable : (prefixWord ++ tailWord_5117268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117268).length < 2 ^ (prefixWord ++ tailWord_5117268).sum := by decide
  have hdescent : baseEnd_5117268 < baseStart_5117268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117338 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3]
def baseStart_5117338 : Nat := 118140960795 + 5117338 * 2 ^ 59
def prefixEnd_5117338 : Nat := 4983230072969 + 3 ^ 40 * 5117338 * 2
def baseEnd_5117338 : Nat := 2627654065517804625240797

theorem tailTrace_5117338 : CollatzResearch.WordTrace tailWord_5117338 prefixEnd_5117338 2627654065517804625240797 := by
  unfold tailWord_5117338
  simp only [CollatzResearch.WordTrace]
  refine ⟨46661162583691468148766167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124429766889843915063376445 46661162583691468148766167)
  ·
    refine ⟨69991743875537202223149251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46661162583691468148766167 69991743875537202223149251)
    ·
      refine ⟨104987615813305803334723877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69991743875537202223149251 104987615813305803334723877)
      ·
        refine ⟨19685177964994838125260727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104987615813305803334723877 19685177964994838125260727)
        ·
          refine ⟨29527766947492257187891091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19685177964994838125260727 29527766947492257187891091)
          ·
            refine ⟨44291650421238385781836637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29527766947492257187891091 44291650421238385781836637)
            ·
              refine ⟨16609368907964394668188739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44291650421238385781836637 16609368907964394668188739)
              ·
                refine ⟨24914053361946592002283109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16609368907964394668188739 24914053361946592002283109)
                ·
                  refine ⟨4671385005364986000428083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24914053361946592002283109 4671385005364986000428083)
                  ·
                    refine ⟨7007077508047479000642125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4671385005364986000428083 7007077508047479000642125)
                    ·
                      refine ⟨2627654065517804625240797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7007077508047479000642125 2627654065517804625240797)
                      ·
                        rfl

theorem cell23_5117338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_5117338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117338 prefixEnd_5117338 := by exact prefixLift 5117338
  have htrace : WordTrace (prefixWord ++ tailWord_5117338) baseStart_5117338 baseEnd_5117338 := by
    simpa [prefixWord, tailWord_5117338, baseEnd_5117338] using wordTrace_append hprefix tailTrace_5117338
  have hstable : (prefixWord ++ tailWord_5117338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117338).length < 2 ^ (prefixWord ++ tailWord_5117338).sum := by decide
  have hdescent : baseEnd_5117338 < baseStart_5117338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117352 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_5117352 : Nat := 118140960795 + 5117352 * 2 ^ 59
def prefixEnd_5117352 : Nat := 4983230072969 + 3 ^ 40 * 5117352 * 2
def baseEnd_5117352 : Nat := 2627661254246967570465733

theorem tailTrace_5117352 : CollatzResearch.WordTrace tailWord_5117352 prefixEnd_5117352 2627661254246967570465733 := by
  unfold tailWord_5117352
  simp only [CollatzResearch.WordTrace]
  refine ⟨93322580478357576493037155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124430107304476768657382873 93322580478357576493037155)
  ·
    refine ⟨139983870717536364739555733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93322580478357576493037155 139983870717536364739555733)
    ·
      refine ⟨6561743939884517097166675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139983870717536364739555733 6561743939884517097166675)
      ·
        refine ⟨9842615909826775645750013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6561743939884517097166675 9842615909826775645750013)
        ·
          refine ⟨3690980966185040867156255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9842615909826775645750013 3690980966185040867156255)
          ·
            refine ⟨5536471449277561300734383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3690980966185040867156255 5536471449277561300734383)
            ·
              refine ⟨8304707173916341951101575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5536471449277561300734383 8304707173916341951101575)
              ·
                refine ⟨12457060760874512926652363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8304707173916341951101575 12457060760874512926652363)
                ·
                  refine ⟨18685591141311769389978545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12457060760874512926652363 18685591141311769389978545)
                  ·
                    refine ⟨14014193355983827042483909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18685591141311769389978545 14014193355983827042483909)
                    ·
                      refine ⟨2627661254246967570465733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14014193355983827042483909 2627661254246967570465733)
                      ·
                        rfl

theorem cell23_5117352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_5117352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117352 prefixEnd_5117352 := by exact prefixLift 5117352
  have htrace : WordTrace (prefixWord ++ tailWord_5117352) baseStart_5117352 baseEnd_5117352 := by
    simpa [prefixWord, tailWord_5117352, baseEnd_5117352] using wordTrace_append hprefix tailTrace_5117352
  have hstable : (prefixWord ++ tailWord_5117352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117352).length < 2 ^ (prefixWord ++ tailWord_5117352).sum := by decide
  have hdescent : baseEnd_5117352 < baseStart_5117352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117365 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_5117365 : Nat := 118140960795 + 5117365 * 2 ^ 59
def prefixEnd_5117365 : Nat := 4983230072969 + 3 ^ 40 * 5117365 * 2
def baseEnd_5117365 : Nat := 2627667929495476019603173

theorem tailTrace_5117365 : CollatzResearch.WordTrace tailWord_5117365 prefixEnd_5117365 2627667929495476019603173 := by
  unfold tailWord_5117365
  simp only [CollatzResearch.WordTrace]
  refine ⟨186645635105668056206297549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124430423403778704137531699 186645635105668056206297549)
  ·
    refine ⟨69992113164625521077361581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186645635105668056206297549 69992113164625521077361581)
    ·
      refine ⟨26247042436734570404010593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69992113164625521077361581 26247042436734570404010593)
      ·
        refine ⟨19685281827550927803007945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26247042436734570404010593 19685281827550927803007945)
        ·
          refine ⟨14763961370663195852255959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19685281827550927803007945 14763961370663195852255959)
          ·
            refine ⟨22145942055994793778383939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14763961370663195852255959 22145942055994793778383939)
            ·
              refine ⟨33218913083992190667575909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22145942055994793778383939 33218913083992190667575909)
              ·
                refine ⟨6228546203248535750170483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33218913083992190667575909 6228546203248535750170483)
                ·
                  refine ⟨9342819304872803625255725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6228546203248535750170483 9342819304872803625255725)
                  ·
                    refine ⟨3503557239327301359470897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9342819304872803625255725 3503557239327301359470897)
                    ·
                      refine ⟨2627667929495476019603173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3503557239327301359470897 2627667929495476019603173)
                      ·
                        rfl

theorem cell23_5117365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_5117365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117365 prefixEnd_5117365 := by exact prefixLift 5117365
  have htrace : WordTrace (prefixWord ++ tailWord_5117365) baseStart_5117365 baseEnd_5117365 := by
    simpa [prefixWord, tailWord_5117365, baseEnd_5117365] using wordTrace_append hprefix tailTrace_5117365
  have hstable : (prefixWord ++ tailWord_5117365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117365).length < 2 ^ (prefixWord ++ tailWord_5117365).sum := by decide
  have hdescent : baseEnd_5117365 < baseStart_5117365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117401 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 7]
def baseStart_5117401 : Nat := 118140960795 + 5117401 * 2 ^ 59
def prefixEnd_5117401 : Nat := 4983230072969 + 3 ^ 40 * 5117401 * 2
def baseEnd_5117401 : Nat := 291965157199893097639223

theorem tailTrace_5117401 : CollatzResearch.WordTrace tailWord_5117401 prefixEnd_5117401 291965157199893097639223 := by
  unfold tailWord_5117401
  simp only [CollatzResearch.WordTrace]
  refine ⟨186646948133537634354608057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124431298755691756236405371 186646948133537634354608057)
  ·
    refine ⟨139985211100153225765956043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186646948133537634354608057 139985211100153225765956043)
    ·
      refine ⟨209977816650229838648934065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139985211100153225765956043 209977816650229838648934065)
      ·
        refine ⟨157483362487672378986700549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209977816650229838648934065 157483362487672378986700549)
        ·
          refine ⟨29528130466438571060006353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157483362487672378986700549 29528130466438571060006353)
          ·
            refine ⟨22146097849828928295004765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29528130466438571060006353 22146097849828928295004765)
            ·
              refine ⟨8304786693685848110626787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22146097849828928295004765 8304786693685848110626787)
              ·
                refine ⟨12457180040528772165940181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8304786693685848110626787 12457180040528772165940181)
                ·
                  refine ⟨291965157199893097639223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12457180040528772165940181 291965157199893097639223)
                  ·
                    rfl

theorem cell23_5117401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 7].length) (baseStart_5117401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117401 prefixEnd_5117401 := by exact prefixLift 5117401
  have htrace : WordTrace (prefixWord ++ tailWord_5117401) baseStart_5117401 baseEnd_5117401 := by
    simpa [prefixWord, tailWord_5117401, baseEnd_5117401] using wordTrace_append hprefix tailTrace_5117401
  have hstable : (prefixWord ++ tailWord_5117401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117401).length < 2 ^ (prefixWord ++ tailWord_5117401).sum := by decide
  have hdescent : baseEnd_5117401 < baseStart_5117401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117452 : List Nat := [2, 2, 1, 2, 5, 2, 2, 2, 5]
def baseStart_5117452 : Nat := 118140960795 + 5117452 * 2 ^ 59
def prefixEnd_5117452 : Nat := 4983230072969 + 3 ^ 40 * 5117452 * 2
def baseEnd_5117452 : Nat := 291968066923601908801697

theorem tailTrace_5117452 : CollatzResearch.WordTrace tailWord_5117452 prefixEnd_5117452 291968066923601908801697 := by
  unfold tailWord_5117452
  simp only [CollatzResearch.WordTrace]
  refine ⟨93324404128176435032357305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124432538837568580043143073 93324404128176435032357305)
  ·
    refine ⟨69993303096132326274267979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93324404128176435032357305 69993303096132326274267979)
    ·
      refine ⟨104989954644198489411401969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69993303096132326274267979 104989954644198489411401969)
      ·
        refine ⟨78742465983148867058551477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104989954644198489411401969 78742465983148867058551477)
        ·
          refine ⟨7382106185920206286739201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78742465983148867058551477 7382106185920206286739201)
          ·
            refine ⟨5536579639440154715054401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7382106185920206286739201 5536579639440154715054401)
            ·
              refine ⟨4152434729580116036290801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5536579639440154715054401 4152434729580116036290801)
              ·
                refine ⟨3114326047185087027218101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4152434729580116036290801 3114326047185087027218101)
                ·
                  refine ⟨291968066923601908801697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3114326047185087027218101 291968066923601908801697)
                  ·
                    rfl

theorem cell23_5117452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_5117452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117452 prefixEnd_5117452 := by exact prefixLift 5117452
  have htrace : WordTrace (prefixWord ++ tailWord_5117452) baseStart_5117452 baseEnd_5117452 := by
    simpa [prefixWord, tailWord_5117452, baseEnd_5117452] using wordTrace_append hprefix tailTrace_5117452
  have hstable : (prefixWord ++ tailWord_5117452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117452).length < 2 ^ (prefixWord ++ tailWord_5117452).sum := by decide
  have hdescent : baseEnd_5117452 < baseStart_5117452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117495 : List Nat := [1, 1, 3, 1, 2, 4, 1, 5, 1, 4]
def baseStart_5117495 : Nat := 118140960795 + 5117495 * 2 ^ 59
def prefixEnd_5117495 : Nat := 4983230072969 + 3 ^ 40 * 5117495 * 2
def baseEnd_5117495 : Nat := 875911560660186836992525

theorem tailTrace_5117495 : CollatzResearch.WordTrace tailWord_5117495 prefixEnd_5117495 875911560660186836992525 := by
  unfold tailWord_5117495
  simp only [CollatzResearch.WordTrace]
  refine ⟨186650376595197088408529939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124433584396798058939019959 186650376595197088408529939)
  ·
    refine ⟨279975564892795632612794909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186650376595197088408529939 279975564892795632612794909)
    ·
      refine ⟨104990836834798362229798091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279975564892795632612794909 104990836834798362229798091)
      ·
        refine ⟨157486255252197543344697137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104990836834798362229798091 157486255252197543344697137)
        ·
          refine ⟨118114691439148157508522853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157486255252197543344697137 118114691439148157508522853)
          ·
            refine ⟨22146504644840279532848035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118114691439148157508522853 22146504644840279532848035)
            ·
              refine ⟨33219756967260419299272053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22146504644840279532848035 33219756967260419299272053)
              ·
                refine ⟨3114352215680664309306755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33219756967260419299272053 3114352215680664309306755)
                ·
                  refine ⟨4671528323520996463960133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114352215680664309306755 4671528323520996463960133)
                  ·
                    refine ⟨875911560660186836992525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4671528323520996463960133 875911560660186836992525)
                    ·
                      rfl

theorem cell23_5117495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_5117495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117495 prefixEnd_5117495 := by exact prefixLift 5117495
  have htrace : WordTrace (prefixWord ++ tailWord_5117495) baseStart_5117495 baseEnd_5117495 := by
    simpa [prefixWord, tailWord_5117495, baseEnd_5117495] using wordTrace_append hprefix tailTrace_5117495
  have hstable : (prefixWord ++ tailWord_5117495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117495).length < 2 ^ (prefixWord ++ tailWord_5117495).sum := by decide
  have hdescent : baseEnd_5117495 < baseStart_5117495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117551 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 3, 6]
def baseStart_5117551 : Nat := 118140960795 + 5117551 * 2 ^ 59
def prefixEnd_5117551 : Nat := 4983230072969 + 3 ^ 40 * 5117551 * 2
def baseEnd_5117551 : Nat := 875921145632404097292439

theorem tailTrace_5117551 : CollatzResearch.WordTrace tailWord_5117551 prefixEnd_5117551 875921145632404097292439 := by
  unfold tailWord_5117551
  simp only [CollatzResearch.WordTrace]
  refine ⟨186652419082994209972568507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124434946055329473315045671 186652419082994209972568507)
  ·
    refine ⟨279978628624491314958852761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186652419082994209972568507 279978628624491314958852761)
    ·
      refine ⟨209983971468368486219139571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279978628624491314958852761 209983971468368486219139571)
      ·
        refine ⟨314975957202552729328709357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209983971468368486219139571 314975957202552729328709357)
        ·
          refine ⟨118115983950957273498266009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314975957202552729328709357 118115983950957273498266009)
          ·
            refine ⟨88586987963217955123699507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118115983950957273498266009 88586987963217955123699507)
            ·
              refine ⟨132880481944826932685549261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88586987963217955123699507 132880481944826932685549261)
              ·
                refine ⟨49830180729310099757080973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132880481944826932685549261 49830180729310099757080973)
                ·
                  refine ⟨18686317773491287408905365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49830180729310099757080973 18686317773491287408905365)
                  ·
                    refine ⟨875921145632404097292439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18686317773491287408905365 875921145632404097292439)
                    ·
                      rfl

theorem cell23_5117551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 6].length) (baseStart_5117551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117551 prefixEnd_5117551 := by exact prefixLift 5117551
  have htrace : WordTrace (prefixWord ++ tailWord_5117551) baseStart_5117551 baseEnd_5117551 := by
    simpa [prefixWord, tailWord_5117551, baseEnd_5117551] using wordTrace_append hprefix tailTrace_5117551
  have hstable : (prefixWord ++ tailWord_5117551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117551).length < 2 ^ (prefixWord ++ tailWord_5117551).sum := by decide
  have hdescent : baseEnd_5117551 < baseStart_5117551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117568 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 4, 4]
def baseStart_5117568 : Nat := 118140960795 + 5117568 * 2 ^ 59
def prefixEnd_5117568 : Nat := 4983230072969 + 3 ^ 40 * 5117568 * 2
def baseEnd_5117568 : Nat := 875924055356112908454913

theorem tailTrace_5117568 : CollatzResearch.WordTrace tailWord_5117568 prefixEnd_5117568 875924055356112908454913 := by
  unfold tailWord_5117568
  simp only [CollatzResearch.WordTrace]
  refine ⟨93326519561966310937968679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124435359415955081250624905 93326519561966310937968679)
  ·
    refine ⟨139989779342949466406953019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93326519561966310937968679 139989779342949466406953019)
    ·
      refine ⟨209984669014424199610429529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139989779342949466406953019 209984669014424199610429529)
      ·
        refine ⟨157488501760818149707822147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209984669014424199610429529 157488501760818149707822147)
        ·
          refine ⟨236232752641227224561733221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157488501760818149707822147 236232752641227224561733221)
          ·
            refine ⟨44293641120230104605324979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236232752641227224561733221 44293641120230104605324979)
            ·
              refine ⟨66440461680345156907987469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44293641120230104605324979 66440461680345156907987469)
              ·
                refine ⟨24915173130129433840495301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66440461680345156907987469 24915173130129433840495301)
                ·
                  refine ⟨4671594961899268845092869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24915173130129433840495301 4671594961899268845092869)
                  ·
                    refine ⟨875924055356112908454913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4671594961899268845092869 875924055356112908454913)
                    ·
                      rfl

theorem cell23_5117568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4, 4].length) (baseStart_5117568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117568 prefixEnd_5117568 := by exact prefixLift 5117568
  have htrace : WordTrace (prefixWord ++ tailWord_5117568) baseStart_5117568 baseEnd_5117568 := by
    simpa [prefixWord, tailWord_5117568, baseEnd_5117568] using wordTrace_append hprefix tailTrace_5117568
  have hstable : (prefixWord ++ tailWord_5117568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117568).length < 2 ^ (prefixWord ++ tailWord_5117568).sum := by decide
  have hdescent : baseEnd_5117568 < baseStart_5117568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117592 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 1, 1, 4]
def baseStart_5117592 : Nat := 118140960795 + 5117592 * 2 ^ 59
def prefixEnd_5117592 : Nat := 4983230072969 + 3 ^ 40 * 5117592 * 2
def baseEnd_5117592 : Nat := 2627784489604046631464629

theorem tailTrace_5117592 : CollatzResearch.WordTrace tailWord_5117592 prefixEnd_5117592 2627784489604046631464629 := by
  unfold tailWord_5117592
  simp only [CollatzResearch.WordTrace]
  refine ⟨93326957237922836987405515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124435942983897115983207353 93326957237922836987405515)
  ·
    refine ⟨139990435856884255481108273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93326957237922836987405515 139990435856884255481108273)
    ·
      refine ⟨104992826892663191610831205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139990435856884255481108273 104992826892663191610831205)
      ·
        refine ⟨19686155042374348427030851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104992826892663191610831205 19686155042374348427030851)
        ·
          refine ⟨29529232563561522640546277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19686155042374348427030851 29529232563561522640546277)
          ·
            refine ⟨5536731105667785495102427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29529232563561522640546277 5536731105667785495102427)
            ·
              refine ⟨8305096658501678242653641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5536731105667785495102427 8305096658501678242653641)
              ·
                refine ⟨6228822493876258681990231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8305096658501678242653641 6228822493876258681990231)
                ·
                  refine ⟨9343233740814388022985347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6228822493876258681990231 9343233740814388022985347)
                  ·
                    refine ⟨14014850611221582034478021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9343233740814388022985347 14014850611221582034478021)
                    ·
                      refine ⟨2627784489604046631464629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14014850611221582034478021 2627784489604046631464629)
                      ·
                        rfl

theorem cell23_5117592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_5117592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117592 prefixEnd_5117592 := by exact prefixLift 5117592
  have htrace : WordTrace (prefixWord ++ tailWord_5117592) baseStart_5117592 baseEnd_5117592 := by
    simpa [prefixWord, tailWord_5117592, baseEnd_5117592] using wordTrace_append hprefix tailTrace_5117592
  have hstable : (prefixWord ++ tailWord_5117592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117592).length < 2 ^ (prefixWord ++ tailWord_5117592).sum := by decide
  have hdescent : baseEnd_5117592 < baseStart_5117592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117602 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_5117602 : Nat := 118140960795 + 5117602 * 2 ^ 59
def prefixEnd_5117602 : Nat := 4983230072969 + 3 ^ 40 * 5117602 * 2
def baseEnd_5117602 : Nat := 875929874803530530779861

theorem tailTrace_5117602 : CollatzResearch.WordTrace tailWord_5117602 prefixEnd_5117602 875929874803530530779861 := by
  unfold tailWord_5117602
  simp only [CollatzResearch.WordTrace]
  refine ⟨46663569801452361420668765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124436186137206297121783373 46663569801452361420668765)
  ·
    refine ⟨17498838675544635532750787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46663569801452361420668765 17498838675544635532750787)
    ·
      refine ⟨26248258013316953299126181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17498838675544635532750787 26248258013316953299126181)
      ·
        refine ⟨4921548377496928743586159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26248258013316953299126181 4921548377496928743586159)
        ·
          refine ⟨7382322566245393115379239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4921548377496928743586159 7382322566245393115379239)
          ·
            refine ⟨11073483849368089673068859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7382322566245393115379239 11073483849368089673068859)
            ·
              refine ⟨16610225774052134509603289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11073483849368089673068859 16610225774052134509603289)
              ·
                refine ⟨12457669330539100882202467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16610225774052134509603289 12457669330539100882202467)
                ·
                  refine ⟨18686503995808651323303701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12457669330539100882202467 18686503995808651323303701)
                  ·
                    refine ⟨875929874803530530779861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18686503995808651323303701 875929874803530530779861)
                    ·
                      rfl

theorem cell23_5117602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_5117602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117602 prefixEnd_5117602 := by exact prefixLift 5117602
  have htrace : WordTrace (prefixWord ++ tailWord_5117602) baseStart_5117602 baseEnd_5117602 := by
    simpa [prefixWord, tailWord_5117602, baseEnd_5117602] using wordTrace_append hprefix tailTrace_5117602
  have hstable : (prefixWord ++ tailWord_5117602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117602).length < 2 ^ (prefixWord ++ tailWord_5117602).sum := by decide
  have hdescent : baseEnd_5117602 < baseStart_5117602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117625 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 4, 1, 3]
def baseStart_5117625 : Nat := 118140960795 + 5117625 * 2 ^ 59
def prefixEnd_5117625 : Nat := 4983230072969 + 3 ^ 40 * 5117625 * 2
def baseEnd_5117625 : Nat := 2627801434465645002351977

theorem tailTrace_5117625 : CollatzResearch.WordTrace tailWord_5117625 prefixEnd_5117625 2627801434465645002351977 := by
  unfold tailWord_5117625
  simp only [CollatzResearch.WordTrace]
  refine ⟨186655118084726120610762329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124436745389817413740508219 186655118084726120610762329)
  ·
    refine ⟨139991338563544590458071747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186655118084726120610762329 139991338563544590458071747)
    ·
      refine ⟨209987007845316885687107621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139991338563544590458071747 209987007845316885687107621)
      ·
        refine ⟨39372563970996916066332679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209987007845316885687107621 39372563970996916066332679)
        ·
          refine ⟨59058845956495374099499019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39372563970996916066332679 59058845956495374099499019)
          ·
            refine ⟨88588268934743061149248529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59058845956495374099499019 88588268934743061149248529)
            ·
              refine ⟨66441201701057295861936397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88588268934743061149248529 66441201701057295861936397)
              ·
                refine ⟨24915450637896485948226149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66441201701057295861936397 24915450637896485948226149)
                ·
                  refine ⟨4671646994605591115292403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24915450637896485948226149 4671646994605591115292403)
                  ·
                    refine ⟨7007470491908386672938605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4671646994605591115292403 7007470491908386672938605)
                    ·
                      refine ⟨2627801434465645002351977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7007470491908386672938605 2627801434465645002351977)
                      ·
                        rfl

theorem cell23_5117625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_5117625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117625 prefixEnd_5117625 := by exact prefixLift 5117625
  have htrace : WordTrace (prefixWord ++ tailWord_5117625) baseStart_5117625 baseEnd_5117625 := by
    simpa [prefixWord, tailWord_5117625, baseEnd_5117625] using wordTrace_append hprefix tailTrace_5117625
  have hstable : (prefixWord ++ tailWord_5117625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117625).length < 2 ^ (prefixWord ++ tailWord_5117625).sum := by decide
  have hdescent : baseEnd_5117625 < baseStart_5117625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117626 : List Nat := [3, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2]
def baseStart_5117626 : Nat := 118140960795 + 5117626 * 2 ^ 59
def prefixEnd_5117626 : Nat := 4983230072969 + 3 ^ 40 * 5117626 * 2
def baseEnd_5117626 : Nat := 2627801947946299498439473

theorem tailTrace_5117626 : CollatzResearch.WordTrace tailWord_5117626 prefixEnd_5117626 2627801947946299498439473 := by
  unfold tailWord_5117626
  simp only [CollatzResearch.WordTrace]
  refine ⟨46663788639430624445387183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124436769705148331854365821 46663788639430624445387183)
  ·
    refine ⟨69995682959145936668080775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46663788639430624445387183 69995682959145936668080775)
    ·
      refine ⟨104993524438718905002121163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69995682959145936668080775 104993524438718905002121163)
      ·
        refine ⟨157490286658078357503181745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104993524438718905002121163 157490286658078357503181745)
        ·
          refine ⟨118117714993558768127386309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157490286658078357503181745 118117714993558768127386309)
          ·
            refine ⟨22147071561292269023884933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118117714993558768127386309 22147071561292269023884933)
            ·
              refine ⟨4152575917742300441978425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22147071561292269023884933 4152575917742300441978425)
              ·
                refine ⟨3114431938306725331483819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4152575917742300441978425 3114431938306725331483819)
                ·
                  refine ⟨4671647907460087997225729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114431938306725331483819 4671647907460087997225729)
                  ·
                    refine ⟨3503735930595065997919297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4671647907460087997225729 3503735930595065997919297)
                    ·
                      refine ⟨2627801947946299498439473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3503735930595065997919297 2627801947946299498439473)
                      ·
                        rfl

theorem cell23_5117626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2].length) (baseStart_5117626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117626 prefixEnd_5117626 := by exact prefixLift 5117626
  have htrace : WordTrace (prefixWord ++ tailWord_5117626) baseStart_5117626 baseEnd_5117626 := by
    simpa [prefixWord, tailWord_5117626, baseEnd_5117626] using wordTrace_append hprefix tailTrace_5117626
  have hstable : (prefixWord ++ tailWord_5117626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117626).length < 2 ^ (prefixWord ++ tailWord_5117626).sum := by decide
  have hdescent : baseEnd_5117626 < baseStart_5117626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117628 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_5117628 : Nat := 118140960795 + 5117628 * 2 ^ 59
def prefixEnd_5117628 : Nat := 4983230072969 + 3 ^ 40 * 5117628 * 2
def baseEnd_5117628 : Nat := 875934324969202830204821

theorem tailTrace_5117628 : CollatzResearch.WordTrace tailWord_5117628 prefixEnd_5117628 875934324969202830204821 := by
  unfold tailWord_5117628
  simp only [CollatzResearch.WordTrace]
  refine ⟨93327613751857626061560769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124436818335810168082081025 93327613751857626061560769)
  ·
    refine ⟨69995710313893219546170577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93327613751857626061560769 69995710313893219546170577)
    ·
      refine ⟨52496782735419914659627933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69995710313893219546170577 52496782735419914659627933)
      ·
        refine ⟨19686293525782467997360475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52496782735419914659627933 19686293525782467997360475)
        ·
          refine ⟨29529440288673701996040713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19686293525782467997360475 29529440288673701996040713)
          ·
            refine ⟨22147080216505276497030535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29529440288673701996040713 22147080216505276497030535)
            ·
              refine ⟨33220620324757914745545803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22147080216505276497030535 33220620324757914745545803)
              ·
                refine ⟨49830930487136872118318705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33220620324757914745545803 49830930487136872118318705)
                ·
                  refine ⟨37373197865352654088739029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49830930487136872118318705 37373197865352654088739029)
                  ·
                    refine ⟨875934324969202830204821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37373197865352654088739029 875934324969202830204821)
                    ·
                      rfl

theorem cell23_5117628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_5117628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117628 prefixEnd_5117628 := by exact prefixLift 5117628
  have htrace : WordTrace (prefixWord ++ tailWord_5117628) baseStart_5117628 baseEnd_5117628 := by
    simpa [prefixWord, tailWord_5117628, baseEnd_5117628] using wordTrace_append hprefix tailTrace_5117628
  have hstable : (prefixWord ++ tailWord_5117628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117628).length < 2 ^ (prefixWord ++ tailWord_5117628).sum := by decide
  have hdescent : baseEnd_5117628 < baseStart_5117628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117642 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_5117642 : Nat := 118140960795 + 5117642 * 2 ^ 59
def prefixEnd_5117642 : Nat := 4983230072969 + 3 ^ 40 * 5117642 * 2
def baseEnd_5117642 : Nat := 2627810163636771435839399

theorem tailTrace_5117642 : CollatzResearch.WordTrace tailWord_5117642 prefixEnd_5117642 2627810163636771435839399 := by
  unfold tailWord_5117642
  simp only [CollatzResearch.WordTrace]
  refine ⟨46663934531416133128532795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124437158750443021676087453 46663934531416133128532795)
  ·
    refine ⟨69995901797124199692799193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46663934531416133128532795 69995901797124199692799193)
    ·
      refine ⟨52496926347843149769599395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69995901797124199692799193 52496926347843149769599395)
      ·
        refine ⟨78745389521764724654399093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52496926347843149769599395 78745389521764724654399093)
        ·
          refine ⟨7382380267665442936349915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78745389521764724654399093 7382380267665442936349915)
          ·
            refine ⟨11073570401498164404524873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7382380267665442936349915 11073570401498164404524873)
            ·
              refine ⟨8305177801123623303393655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11073570401498164404524873 8305177801123623303393655)
              ·
                refine ⟨12457766701685434955090483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8305177801123623303393655 12457766701685434955090483)
                ·
                  refine ⟨18686650052528152432635725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12457766701685434955090483 18686650052528152432635725)
                  ·
                    refine ⟨7007493769698057162238397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18686650052528152432635725 7007493769698057162238397)
                    ·
                      refine ⟨2627810163636771435839399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7007493769698057162238397 2627810163636771435839399)
                      ·
                        rfl

theorem cell23_5117642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_5117642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117642 prefixEnd_5117642 := by exact prefixLift 5117642
  have htrace : WordTrace (prefixWord ++ tailWord_5117642) baseStart_5117642 baseEnd_5117642 := by
    simpa [prefixWord, tailWord_5117642, baseEnd_5117642] using wordTrace_append hprefix tailTrace_5117642
  have hstable : (prefixWord ++ tailWord_5117642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117642).length < 2 ^ (prefixWord ++ tailWord_5117642).sum := by decide
  have hdescent : baseEnd_5117642 < baseStart_5117642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117668 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_5117668 : Nat := 118140960795 + 5117668 * 2 ^ 59
def prefixEnd_5117668 : Nat := 4983230072969 + 3 ^ 40 * 5117668 * 2
def baseEnd_5117668 : Nat := 2627823514133788334114279

theorem tailTrace_5117668 : CollatzResearch.WordTrace tailWord_5117668 prefixEnd_5117668 2627823514133788334114279 := by
  unfold tailWord_5117668
  simp only [CollatzResearch.WordTrace]
  refine ⟨93328343211785169477288829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124437790949046892636385105 93328343211785169477288829)
  ·
    refine ⟨34998128704419438553983311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93328343211785169477288829 34998128704419438553983311)
    ·
      refine ⟨52497193056629157830974967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34998128704419438553983311 52497193056629157830974967)
      ·
        refine ⟨78745789584943736746462451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52497193056629157830974967 78745789584943736746462451)
        ·
          refine ⟨118118684377415605119693677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78745789584943736746462451 118118684377415605119693677)
          ·
            refine ⟨44294506641530851919885129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118118684377415605119693677 44294506641530851919885129)
            ·
              refine ⟨33220879981148138939913847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44294506641530851919885129 33220879981148138939913847)
              ·
                refine ⟨49831319971722208409870771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33220879981148138939913847 49831319971722208409870771)
                ·
                  refine ⟨74746979957583312614806157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49831319971722208409870771 74746979957583312614806157)
                  ·
                    refine ⟨28030117484093742230552309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74746979957583312614806157 28030117484093742230552309)
                    ·
                      refine ⟨2627823514133788334114279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28030117484093742230552309 2627823514133788334114279)
                      ·
                        rfl

theorem cell23_5117668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_5117668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117668 prefixEnd_5117668 := by exact prefixLift 5117668
  have htrace : WordTrace (prefixWord ++ tailWord_5117668) baseStart_5117668 baseEnd_5117668 := by
    simpa [prefixWord, tailWord_5117668, baseEnd_5117668] using wordTrace_append hprefix tailTrace_5117668
  have hstable : (prefixWord ++ tailWord_5117668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117668).length < 2 ^ (prefixWord ++ tailWord_5117668).sum := by decide
  have hdescent : baseEnd_5117668 < baseStart_5117668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117722 : List Nat := [3, 1, 1, 3, 2, 2, 3, 3, 5]
def baseStart_5117722 : Nat := 118140960795 + 5117722 * 2 ^ 59
def prefixEnd_5117722 : Nat := 4983230072969 + 3 ^ 40 * 5117722 * 2
def baseEnd_5117722 : Nat := 291983471343236791426559

theorem tailTrace_5117722 : CollatzResearch.WordTrace tailWord_5117722 prefixEnd_5117722 291983471343236791426559 := by
  unfold tailWord_5117722
  simp only [CollatzResearch.WordTrace]
  refine ⟨46664663991343676544260855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124439103976916470784695613 46664663991343676544260855)
  ·
    refine ⟨69996995987015514816391283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46664663991343676544260855 69996995987015514816391283)
    ·
      refine ⟨104995493980523272224586925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69996995987015514816391283 104995493980523272224586925)
      ·
        refine ⟨39373310242696227084220097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104995493980523272224586925 39373310242696227084220097)
        ·
          refine ⟨29529982682022170313165073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39373310242696227084220097 29529982682022170313165073)
          ·
            refine ⟨22147487011516627734873805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29529982682022170313165073 22147487011516627734873805)
            ·
              refine ⟨8305307629318735400577677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22147487011516627734873805 8305307629318735400577677)
              ·
                refine ⟨3114490360994525775216629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8305307629318735400577677 3114490360994525775216629)
                ·
                  refine ⟨291983471343236791426559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3114490360994525775216629 291983471343236791426559)
                  ·
                    rfl

theorem cell23_5117722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_5117722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117722 prefixEnd_5117722 := by exact prefixLift 5117722
  have htrace : WordTrace (prefixWord ++ tailWord_5117722) baseStart_5117722 baseEnd_5117722 := by
    simpa [prefixWord, tailWord_5117722, baseEnd_5117722] using wordTrace_append hprefix tailTrace_5117722
  have hstable : (prefixWord ++ tailWord_5117722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117722).length < 2 ^ (prefixWord ++ tailWord_5117722).sum := by decide
  have hdescent : baseEnd_5117722 < baseStart_5117722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117745 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 5]
def baseStart_5117745 : Nat := 118140960795 + 5117745 * 2 ^ 59
def prefixEnd_5117745 : Nat := 4983230072969 + 3 ^ 40 * 5117745 * 2
def baseEnd_5117745 : Nat := 2627863052144184532851425

theorem tailTrace_5117745 : CollatzResearch.WordTrace tailWord_5117745 prefixEnd_5117745 2627863052144184532851425 := by
  unfold tailWord_5117745
  simp only [CollatzResearch.WordTrace]
  refine ⟨186659494844291381105130689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124439663229527587403420459 186659494844291381105130689)
  ·
    refine ⟨139994621133218535828848017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186659494844291381105130689 139994621133218535828848017)
    ·
      refine ⟨104995965849913901871636013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139994621133218535828848017 104995965849913901871636013)
      ·
        refine ⟨39373487193717713201863505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104995965849913901871636013 39373487193717713201863505)
        ·
          refine ⟨29530115395288284901397629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39373487193717713201863505 29530115395288284901397629)
          ·
            refine ⟨11073793273233106838024111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29530115395288284901397629 11073793273233106838024111)
            ·
              refine ⟨16610689909849660257036167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11073793273233106838024111 16610689909849660257036167)
              ·
                refine ⟨24916034864774490385554251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16610689909849660257036167 24916034864774490385554251)
                ·
                  refine ⟨37374052297161735578331377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24916034864774490385554251 37374052297161735578331377)
                  ·
                    refine ⟨28030539222871301683748533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37374052297161735578331377 28030539222871301683748533)
                    ·
                      refine ⟨2627863052144184532851425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28030539222871301683748533 2627863052144184532851425)
                      ·
                        rfl

theorem cell23_5117745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_5117745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117745 prefixEnd_5117745 := by exact prefixLift 5117745
  have htrace : WordTrace (prefixWord ++ tailWord_5117745) baseStart_5117745 baseEnd_5117745 := by
    simpa [prefixWord, tailWord_5117745, baseEnd_5117745] using wordTrace_append hprefix tailTrace_5117745
  have hstable : (prefixWord ++ tailWord_5117745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117745).length < 2 ^ (prefixWord ++ tailWord_5117745).sum := by decide
  have hdescent : baseEnd_5117745 < baseStart_5117745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117750 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_5117750 : Nat := 118140960795 + 5117750 * 2 ^ 59
def prefixEnd_5117750 : Nat := 4983230072969 + 3 ^ 40 * 5117750 * 2
def baseEnd_5117750 : Nat := 2627865619547457013288903

theorem tailTrace_5117750 : CollatzResearch.WordTrace tailWord_5117750 prefixEnd_5117750 2627865619547457013288903 := by
  unfold tailWord_5117750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11666229825579579184941419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124439784806182177972708469 11666229825579579184941419)
  ·
    refine ⟨17499344738369368777412129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11666229825579579184941419 17499344738369368777412129)
    ·
      refine ⟨13124508553777026583059097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17499344738369368777412129 13124508553777026583059097)
      ·
        refine ⟨9843381415332769937294323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13124508553777026583059097 9843381415332769937294323)
        ·
          refine ⟨14765072122999154905941485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9843381415332769937294323 14765072122999154905941485)
          ·
            refine ⟨5536902046124683089728057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14765072122999154905941485 5536902046124683089728057)
            ·
              refine ⟨4152676534593512317296043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5536902046124683089728057 4152676534593512317296043)
              ·
                refine ⟨6229014801890268475944065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4152676534593512317296043 6229014801890268475944065)
                ·
                  refine ⟨4671761101417701356958049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6229014801890268475944065 4671761101417701356958049)
                  ·
                    refine ⟨3503820826063276017718537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4671761101417701356958049 3503820826063276017718537)
                    ·
                      refine ⟨2627865619547457013288903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3503820826063276017718537 2627865619547457013288903)
                      ·
                        rfl

theorem cell23_5117750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_5117750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117750 prefixEnd_5117750 := by exact prefixLift 5117750
  have htrace : WordTrace (prefixWord ++ tailWord_5117750) baseStart_5117750 baseEnd_5117750 := by
    simpa [prefixWord, tailWord_5117750, baseEnd_5117750] using wordTrace_append hprefix tailTrace_5117750
  have hstable : (prefixWord ++ tailWord_5117750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117750).length < 2 ^ (prefixWord ++ tailWord_5117750).sum := by decide
  have hdescent : baseEnd_5117750 < baseStart_5117750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117765 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 5, 4]
def baseStart_5117765 : Nat := 118140960795 + 5117765 * 2 ^ 59
def prefixEnd_5117765 : Nat := 4983230072969 + 3 ^ 40 * 5117765 * 2
def baseEnd_5117765 : Nat := 875957773919091484867111

theorem tailTrace_5117765 : CollatzResearch.WordTrace tailWord_5117765 prefixEnd_5117765 875957773919091484867111 := by
  unfold tailWord_5117765
  simp only [CollatzResearch.WordTrace]
  refine ⟨186660224304218924520858749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124440149536145949680572499 186660224304218924520858749)
  ·
    refine ⟨69997584114082096695322031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186660224304218924520858749 69997584114082096695322031)
    ·
      refine ⟨104996376171123145042983047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69997584114082096695322031 104996376171123145042983047)
      ·
        refine ⟨157494564256684717564474571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104996376171123145042983047 157494564256684717564474571)
        ·
          refine ⟨236241846385027076346711857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157494564256684717564474571 236241846385027076346711857)
          ·
            refine ⟨177181384788770307260033893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236241846385027076346711857 177181384788770307260033893)
            ·
              refine ⟨33221509647894432611256355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177181384788770307260033893 33221509647894432611256355)
              ·
                refine ⟨49832264471841648916884533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33221509647894432611256355 49832264471841648916884533)
                ·
                  refine ⟨4671774794235154585957925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49832264471841648916884533 4671774794235154585957925)
                  ·
                    refine ⟨875957773919091484867111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4671774794235154585957925 875957773919091484867111)
                    ·
                      rfl

theorem cell23_5117765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_5117765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117765 prefixEnd_5117765 := by exact prefixLift 5117765
  have htrace : WordTrace (prefixWord ++ tailWord_5117765) baseStart_5117765 baseEnd_5117765 := by
    simpa [prefixWord, tailWord_5117765, baseEnd_5117765] using wordTrace_append hprefix tailTrace_5117765
  have hstable : (prefixWord ++ tailWord_5117765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117765).length < 2 ^ (prefixWord ++ tailWord_5117765).sum := by decide
  have hdescent : baseEnd_5117765 < baseStart_5117765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117792 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 3]
def baseStart_5117792 : Nat := 118140960795 + 5117792 * 2 ^ 59
def prefixEnd_5117792 : Nat := 4983230072969 + 3 ^ 40 * 5117792 * 2
def baseEnd_5117792 : Nat := 2627887185734945848963709

theorem tailTrace_5117792 : CollatzResearch.WordTrace tailWord_5117792 prefixEnd_5117792 2627887185734945848963709 := by
  unfold tailWord_5117792
  simp only [CollatzResearch.WordTrace]
  refine ⟨93330604537560554066045815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124440806050080738754727753 93330604537560554066045815)
  ·
    refine ⟨139995906806340831099068723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93330604537560554066045815 139995906806340831099068723)
    ·
      refine ⟨209993860209511246648603085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139995906806340831099068723 209993860209511246648603085)
      ·
        refine ⟨78747697578566717493226157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209993860209511246648603085 78747697578566717493226157)
        ·
          refine ⟨29530386591962519059959809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78747697578566717493226157 29530386591962519059959809)
          ·
            refine ⟨22147789943971889294969857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29530386591962519059959809 22147789943971889294969857)
            ·
              refine ⟨16610842457978916971227393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22147789943971889294969857 16610842457978916971227393)
              ·
                refine ⟨12458131843484187728420545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16610842457978916971227393 12458131843484187728420545)
                ·
                  refine ⟨9343598882613140796315409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12458131843484187728420545 9343598882613140796315409)
                  ·
                    refine ⟨7007699161959855597236557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9343598882613140796315409 7007699161959855597236557)
                    ·
                      refine ⟨2627887185734945848963709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7007699161959855597236557 2627887185734945848963709)
                      ·
                        rfl

theorem cell23_5117792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_5117792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117792 prefixEnd_5117792 := by exact prefixLift 5117792
  have htrace : WordTrace (prefixWord ++ tailWord_5117792) baseStart_5117792 baseEnd_5117792 := by
    simpa [prefixWord, tailWord_5117792, baseEnd_5117792] using wordTrace_append hprefix tailTrace_5117792
  have hstable : (prefixWord ++ tailWord_5117792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117792).length < 2 ^ (prefixWord ++ tailWord_5117792).sum := by decide
  have hdescent : baseEnd_5117792 < baseStart_5117792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117799 : List Nat := [1, 1, 5, 1, 2, 1, 3, 4, 1, 4]
def baseStart_5117799 : Nat := 118140960795 + 5117799 * 2 ^ 59
def prefixEnd_5117799 : Nat := 4983230072969 + 3 ^ 40 * 5117799 * 2
def baseEnd_5117799 : Nat := 875963593366509107192059

theorem tailTrace_5117799 : CollatzResearch.WordTrace tailWord_5117799 prefixEnd_5117799 875963593366509107192059 := by
  unfold tailWord_5117799
  simp only [CollatzResearch.WordTrace]
  refine ⟨186661464386095748327596451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124440976257397165551730967 186661464386095748327596451)
  ·
    refine ⟨279992196579143622491394677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186661464386095748327596451 279992196579143622491394677)
    ·
      refine ⟨26249268429294714608568251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 279992196579143622491394677 26249268429294714608568251)
      ·
        refine ⟨39373902643942071912852377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26249268429294714608568251 39373902643942071912852377)
        ·
          refine ⟨29530426982956553934639283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39373902643942071912852377 29530426982956553934639283)
          ·
            refine ⟨44295640474434830901958925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29530426982956553934639283 44295640474434830901958925)
            ·
              refine ⟨16610865177913061588234597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44295640474434830901958925 16610865177913061588234597)
              ·
                refine ⟨3114537220858699047793987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16610865177913061588234597 3114537220858699047793987)
                ·
                  refine ⟨4671805831288048571690981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114537220858699047793987 4671805831288048571690981)
                  ·
                    refine ⟨875963593366509107192059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4671805831288048571690981 875963593366509107192059)
                    ·
                      rfl

theorem cell23_5117799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_5117799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117799 prefixEnd_5117799 := by exact prefixLift 5117799
  have htrace : WordTrace (prefixWord ++ tailWord_5117799) baseStart_5117799 baseEnd_5117799 := by
    simpa [prefixWord, tailWord_5117799, baseEnd_5117799] using wordTrace_append hprefix tailTrace_5117799
  have hstable : (prefixWord ++ tailWord_5117799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117799).length < 2 ^ (prefixWord ++ tailWord_5117799).sum := by decide
  have hdescent : baseEnd_5117799 < baseStart_5117799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117846 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_5117846 : Nat := 118140960795 + 5117846 * 2 ^ 59
def prefixEnd_5117846 : Nat := 4983230072969 + 3 ^ 40 * 5117846 * 2
def baseEnd_5117846 : Nat := 291990545965587626409829

theorem tailTrace_5117846 : CollatzResearch.WordTrace tailWord_5117846 prefixEnd_5117846 291990545965587626409829 := by
  unfold tailWord_5117846
  simp only [CollatzResearch.WordTrace]
  refine ⟨11666448663557842209659837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124442119077950316903038261 11666448663557842209659837)
  ·
    refine ⟨4374918248834190828622439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11666448663557842209659837 4374918248834190828622439)
    ·
      refine ⟨6562377373251286242933659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4374918248834190828622439 6562377373251286242933659)
      ·
        refine ⟨9843566059876929364400489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6562377373251286242933659 9843566059876929364400489)
        ·
          refine ⟨7382674544907697023300367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9843566059876929364400489 7382674544907697023300367)
          ·
            refine ⟨11074011817361545534950551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7382674544907697023300367 11074011817361545534950551)
            ·
              refine ⟨16611017726042318302425827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11074011817361545534950551 16611017726042318302425827)
              ·
                refine ⟨24916526589063477453638741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16611017726042318302425827 24916526589063477453638741)
                ·
                  refine ⟨291990545965587626409829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24916526589063477453638741 291990545965587626409829)
                  ·
                    rfl

theorem cell23_5117846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_5117846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117846 prefixEnd_5117846 := by exact prefixLift 5117846
  have htrace : WordTrace (prefixWord ++ tailWord_5117846) baseStart_5117846 baseEnd_5117846 := by
    simpa [prefixWord, tailWord_5117846, baseEnd_5117846] using wordTrace_append hprefix tailTrace_5117846
  have hstable : (prefixWord ++ tailWord_5117846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117846).length < 2 ^ (prefixWord ++ tailWord_5117846).sum := by decide
  have hdescent : baseEnd_5117846 < baseStart_5117846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117865 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 2, 6, 3]
def baseStart_5117865 : Nat := 118140960795 + 5117865 * 2 ^ 59
def prefixEnd_5117865 : Nat := 4983230072969 + 3 ^ 40 * 5117865 * 2
def baseEnd_5117865 : Nat := 2627924669822724063350873

theorem tailTrace_5117865 : CollatzResearch.WordTrace tailWord_5117865 prefixEnd_5117865 2627924669822724063350873 := by
  unfold tailWord_5117865
  simp only [CollatzResearch.WordTrace]
  refine ⟨186663871603856641599499049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124442581069237761066332699 186663871603856641599499049)
  ·
    refine ⟨139997903702892481199624287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186663871603856641599499049 139997903702892481199624287)
    ·
      refine ⟨209996855554338721799436431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139997903702892481199624287 209996855554338721799436431)
      ·
        refine ⟨314995283331508082699154647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209996855554338721799436431 314995283331508082699154647)
        ·
          refine ⟨472492924997262124048731971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314995283331508082699154647 472492924997262124048731971)
          ·
            refine ⟨708739387495893186073097957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472492924997262124048731971 708739387495893186073097957)
            ·
              refine ⟨132888635155479972388705867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 708739387495893186073097957 132888635155479972388705867)
              ·
                refine ⟨199332952733219958583058801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132888635155479972388705867 199332952733219958583058801)
                ·
                  refine ⟨149499714549914968937294101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199332952733219958583058801 149499714549914968937294101)
                  ·
                    refine ⟨7007799119527264168935661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 149499714549914968937294101 7007799119527264168935661)
                    ·
                      refine ⟨2627924669822724063350873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7007799119527264168935661 2627924669822724063350873)
                      ·
                        rfl

theorem cell23_5117865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6, 3].length) (baseStart_5117865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117865 prefixEnd_5117865 := by exact prefixLift 5117865
  have htrace : WordTrace (prefixWord ++ tailWord_5117865) baseStart_5117865 baseEnd_5117865 := by
    simpa [prefixWord, tailWord_5117865, baseEnd_5117865] using wordTrace_append hprefix tailTrace_5117865
  have hstable : (prefixWord ++ tailWord_5117865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117865).length < 2 ^ (prefixWord ++ tailWord_5117865).sum := by decide
  have hdescent : baseEnd_5117865 < baseStart_5117865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117875 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 6]
def baseStart_5117875 : Nat := 118140960795 + 5117875 * 2 ^ 59
def prefixEnd_5117875 : Nat := 4983230072969 + 3 ^ 40 * 5117875 * 2
def baseEnd_5117875 : Nat := 2627929804629269024225827

theorem tailTrace_5117875 : CollatzResearch.WordTrace tailWord_5117875 prefixEnd_5117875 2627929804629269024225827 := by
  unfold tailWord_5117875
  simp only [CollatzResearch.WordTrace]
  refine ⟨186664236333820413307363079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124442824222546942204908719 186664236333820413307363079)
  ·
    refine ⟨279996354500730619961044619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186664236333820413307363079 279996354500730619961044619)
    ·
      refine ⟨419994531751095929941566929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279996354500730619961044619 419994531751095929941566929)
      ·
        refine ⟨314995898813321947456175197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419994531751095929941566929 314995898813321947456175197)
        ·
          refine ⟨118123462054995730296065699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314995898813321947456175197 118123462054995730296065699)
          ·
            refine ⟨177185193082493595444098549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118123462054995730296065699 177185193082493595444098549)
            ·
              refine ⟨16611111851483774572884239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 177185193082493595444098549 16611111851483774572884239)
              ·
                refine ⟨24916667777225661859326359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16611111851483774572884239 24916667777225661859326359)
                ·
                  refine ⟨37375001665838492788989539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24916667777225661859326359 37375001665838492788989539)
                  ·
                    refine ⟨56062502498757739183484309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37375001665838492788989539 56062502498757739183484309)
                    ·
                      refine ⟨2627929804629269024225827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56062502498757739183484309 2627929804629269024225827)
                      ·
                        rfl

theorem cell23_5117875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_5117875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117875 prefixEnd_5117875 := by exact prefixLift 5117875
  have htrace : WordTrace (prefixWord ++ tailWord_5117875) baseStart_5117875 baseEnd_5117875 := by
    simpa [prefixWord, tailWord_5117875, baseEnd_5117875] using wordTrace_append hprefix tailTrace_5117875
  have hstable : (prefixWord ++ tailWord_5117875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117875).length < 2 ^ (prefixWord ++ tailWord_5117875).sum := by decide
  have hdescent : baseEnd_5117875 < baseStart_5117875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117913 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 3, 2, 2]
def baseStart_5117913 : Nat := 118140960795 + 5117913 * 2 ^ 59
def prefixEnd_5117913 : Nat := 4983230072969 + 3 ^ 40 * 5117913 * 2
def baseEnd_5117913 : Nat := 2627949316894139875550653

theorem tailTrace_5117913 : CollatzResearch.WordTrace tailWord_5117913 prefixEnd_5117913 2627949316894139875550653 := by
  unfold tailWord_5117913
  simp only [CollatzResearch.WordTrace]
  refine ⟨186665622307682745797246393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124443748205121830531497595 186665622307682745797246393)
  ·
    refine ⟨139999216730762059347934795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186665622307682745797246393 139999216730762059347934795)
    ·
      refine ⟨209998825096143089021902193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139999216730762059347934795 209998825096143089021902193)
      ·
        refine ⟨157499118822107316766426645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209998825096143089021902193 157499118822107316766426645)
        ·
          refine ⟨7382771194786280473426249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 157499118822107316766426645 7382771194786280473426249)
          ·
            refine ⟨5537078396089710355069687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7382771194786280473426249 5537078396089710355069687)
            ·
              refine ⟨8305617594134565532604531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5537078396089710355069687 8305617594134565532604531)
              ·
                refine ⟨12458426391201848298906797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8305617594134565532604531 12458426391201848298906797)
                ·
                  refine ⟨4671909896700693112090049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12458426391201848298906797 4671909896700693112090049)
                  ·
                    refine ⟨3503932422525519834067537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4671909896700693112090049 3503932422525519834067537)
                    ·
                      refine ⟨2627949316894139875550653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3503932422525519834067537 2627949316894139875550653)
                      ·
                        rfl

theorem cell23_5117913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 3, 2, 2].length) (baseStart_5117913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117913 prefixEnd_5117913 := by exact prefixLift 5117913
  have htrace : WordTrace (prefixWord ++ tailWord_5117913) baseStart_5117913 baseEnd_5117913 := by
    simpa [prefixWord, tailWord_5117913, baseEnd_5117913] using wordTrace_append hprefix tailTrace_5117913
  have hstable : (prefixWord ++ tailWord_5117913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117913).length < 2 ^ (prefixWord ++ tailWord_5117913).sum := by decide
  have hdescent : baseEnd_5117913 < baseStart_5117913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117958 : List Nat := [6, 2, 1, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_5117958 : Nat := 118140960795 + 5117958 * 2 ^ 59
def prefixEnd_5117958 : Nat := 4983230072969 + 3 ^ 40 * 5117958 * 2
def baseEnd_5117958 : Nat := 2627972423523592199487947

theorem tailTrace_5117958 : CollatzResearch.WordTrace tailWord_5117958 prefixEnd_5117958 2627972423523592199487947 := by
  unfold tailWord_5117958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5833351987266241202582329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 124444842395013145655089685 5833351987266241202582329)
  ·
    refine ⟨4375013990449680901936747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5833351987266241202582329 4375013990449680901936747)
    ·
      refine ⟨6562520985674521352905121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4375013990449680901936747 6562520985674521352905121)
      ·
        refine ⟨4921890739255891014678841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6562520985674521352905121 4921890739255891014678841)
        ·
          refine ⟨3691418054441918261009131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4921890739255891014678841 3691418054441918261009131)
          ·
            refine ⟨5537127081662877391513697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3691418054441918261009131 5537127081662877391513697)
            ·
              refine ⟨4152845311247158043635273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5537127081662877391513697 4152845311247158043635273)
              ·
                refine ⟨3114633983435368532726455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4152845311247158043635273 3114633983435368532726455)
                ·
                  refine ⟨4671950975153052799089683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114633983435368532726455 4671950975153052799089683)
                  ·
                    refine ⟨7007926462729579198634525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4671950975153052799089683 7007926462729579198634525)
                    ·
                      refine ⟨2627972423523592199487947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7007926462729579198634525 2627972423523592199487947)
                      ·
                        rfl

theorem cell23_5117958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_5117958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117958 prefixEnd_5117958 := by exact prefixLift 5117958
  have htrace : WordTrace (prefixWord ++ tailWord_5117958) baseStart_5117958 baseEnd_5117958 := by
    simpa [prefixWord, tailWord_5117958, baseEnd_5117958] using wordTrace_append hprefix tailTrace_5117958
  have hstable : (prefixWord ++ tailWord_5117958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117958).length < 2 ^ (prefixWord ++ tailWord_5117958).sum := by decide
  have hdescent : baseEnd_5117958 < baseStart_5117958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5117986 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_5117986 : Nat := 118140960795 + 5117986 * 2 ^ 59
def prefixEnd_5117986 : Nat := 4983230072969 + 3 ^ 40 * 5117986 * 2
def baseEnd_5117986 : Nat := 2627986800981918089937817

theorem tailTrace_5117986 : CollatzResearch.WordTrace tailWord_5117986 prefixEnd_5117986 2627986800981918089937817 := by
  unfold tailWord_5117986
  simp only [CollatzResearch.WordTrace]
  refine ⟨46667071209104569816163453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124445523224278852843102541 46667071209104569816163453)
  ·
    refine ⟨17500151703414213681061295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46667071209104569816163453 17500151703414213681061295)
    ·
      refine ⟨26250227555121320521591943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17500151703414213681061295 26250227555121320521591943)
      ·
        refine ⟨39375341332681980782387915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26250227555121320521591943 39375341332681980782387915)
        ·
          refine ⟨59063011999022971173581873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39375341332681980782387915 59063011999022971173581873)
          ·
            refine ⟨44297258999267228380186405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59063011999022971173581873 44297258999267228380186405)
            ·
              refine ⟨8305736062362605321284951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44297258999267228380186405 8305736062362605321284951)
              ·
                refine ⟨12458604093543907981927427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8305736062362605321284951 12458604093543907981927427)
                ·
                  refine ⟨18687906140315861972891141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12458604093543907981927427 18687906140315861972891141)
                  ·
                    refine ⟨3503982401309224119917089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18687906140315861972891141 3503982401309224119917089)
                    ·
                      refine ⟨2627986800981918089937817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3503982401309224119917089 2627986800981918089937817)
                      ·
                        rfl

theorem cell23_5117986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_5117986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5117986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5117986 prefixEnd_5117986 := by exact prefixLift 5117986
  have htrace : WordTrace (prefixWord ++ tailWord_5117986) baseStart_5117986 baseEnd_5117986 := by
    simpa [prefixWord, tailWord_5117986, baseEnd_5117986] using wordTrace_append hprefix tailTrace_5117986
  have hstable : (prefixWord ++ tailWord_5117986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5117986).length < 2 ^ (prefixWord ++ tailWord_5117986).sum := by decide
  have hdescent : baseEnd_5117986 < baseStart_5117986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5117986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118042 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_5118042 : Nat := 118140960795 + 5118042 * 2 ^ 59
def prefixEnd_5118042 : Nat := 4983230072969 + 3 ^ 40 * 5118042 * 2
def baseEnd_5118042 : Nat := 2628015555898569870837559

theorem tailTrace_5118042 : CollatzResearch.WordTrace tailWord_5118042 prefixEnd_5118042 2628015555898569870837559 := by
  unfold tailWord_5118042
  simp only [CollatzResearch.WordTrace]
  refine ⟨46667581831053850207173095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124446884882810267219128253 46667581831053850207173095)
  ·
    refine ⟨70001372746580775310759643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46667581831053850207173095 70001372746580775310759643)
    ·
      refine ⟨105002059119871162966139465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70001372746580775310759643 105002059119871162966139465)
      ·
        refine ⟨78751544339903372224604599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105002059119871162966139465 78751544339903372224604599)
        ·
          refine ⟨118127316509855058336906899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78751544339903372224604599 118127316509855058336906899)
          ·
            refine ⟨177190974764782587505360349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118127316509855058336906899 177190974764782587505360349)
            ·
              refine ⟨66446615536793470314510131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177190974764782587505360349 66446615536793470314510131)
              ·
                refine ⟨99669923305190205471765197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66446615536793470314510131 99669923305190205471765197)
                ·
                  refine ⟨37376221239446327051911949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99669923305190205471765197 37376221239446327051911949)
                  ·
                    refine ⟨14016082964792372644466981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37376221239446327051911949 14016082964792372644466981)
                    ·
                      refine ⟨2628015555898569870837559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14016082964792372644466981 2628015555898569870837559)
                      ·
                        rfl

theorem cell23_5118042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_5118042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118042 prefixEnd_5118042 := by exact prefixLift 5118042
  have htrace : WordTrace (prefixWord ++ tailWord_5118042) baseStart_5118042 baseEnd_5118042 := by
    simpa [prefixWord, tailWord_5118042, baseEnd_5118042] using wordTrace_append hprefix tailTrace_5118042
  have hstable : (prefixWord ++ tailWord_5118042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118042).length < 2 ^ (prefixWord ++ tailWord_5118042).sum := by decide
  have hdescent : baseEnd_5118042 < baseStart_5118042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118133 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 6]
def baseStart_5118133 : Nat := 118140960795 + 5118133 * 2 ^ 59
def prefixEnd_5118133 : Nat := 4983230072969 + 3 ^ 40 * 5118133 * 2
def baseEnd_5118133 : Nat := 292006920293125446088849

theorem tailTrace_5118133 : CollatzResearch.WordTrace tailWord_5118133 prefixEnd_5118133 292006920293125446088849 := by
  unfold tailWord_5118133
  simp only [CollatzResearch.WordTrace]
  refine ⟨186673646366885723370255053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124449097577923815580170035 186673646366885723370255053)
  ·
    refine ⟨70002617387582146263845645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186673646366885723370255053 70002617387582146263845645)
    ·
      refine ⟨26250981520343304848942117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70002617387582146263845645 26250981520343304848942117)
      ·
        refine ⟨4922059035064369659176647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26250981520343304848942117 4922059035064369659176647)
        ·
          refine ⟨7383088552596554488764971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922059035064369659176647 7383088552596554488764971)
          ·
            refine ⟨11074632828894831733147457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7383088552596554488764971 11074632828894831733147457)
            ·
              refine ⟨8305974621671123799860593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11074632828894831733147457 8305974621671123799860593)
              ·
                refine ⟨6229480966253342849895445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8305974621671123799860593 6229480966253342849895445)
                ·
                  refine ⟨292006920293125446088849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6229480966253342849895445 292006920293125446088849)
                  ·
                    rfl

theorem cell23_5118133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_5118133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118133 prefixEnd_5118133 := by exact prefixLift 5118133
  have htrace : WordTrace (prefixWord ++ tailWord_5118133) baseStart_5118133 baseEnd_5118133 := by
    simpa [prefixWord, tailWord_5118133, baseEnd_5118133] using wordTrace_append hprefix tailTrace_5118133
  have hstable : (prefixWord ++ tailWord_5118133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118133).length < 2 ^ (prefixWord ++ tailWord_5118133).sum := by decide
  have hdescent : baseEnd_5118133 < baseStart_5118133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118136 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 2, 3, 2]
def baseStart_5118136 : Nat := 118140960795 + 5118136 * 2 ^ 59
def prefixEnd_5118136 : Nat := 4983230072969 + 3 ^ 40 * 5118136 * 2
def baseEnd_5118136 : Nat := 2628063823080092503062127

theorem tailTrace_5118136 : CollatzResearch.WordTrace tailWord_5118136 prefixEnd_5118136 2628063823080092503062127 := by
  unfold tailWord_5118136
  simp only [CollatzResearch.WordTrace]
  refine ⟨93336877892937427441307131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124449170523916569921742841 93336877892937427441307131)
  ·
    refine ⟨140005316839406141161960697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93336877892937427441307131 140005316839406141161960697)
    ·
      refine ⟨105003987629554605871470523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140005316839406141161960697 105003987629554605871470523)
      ·
        refine ⟨157505981444331908807205785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105003987629554605871470523 157505981444331908807205785)
        ·
          refine ⟨118129486083248931605404339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157505981444331908807205785 118129486083248931605404339)
          ·
            refine ⟨177194229124873397408106509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118129486083248931605404339 177194229124873397408106509)
            ·
              refine ⟨66447835921827524028039941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177194229124873397408106509 66447835921827524028039941)
              ·
                refine ⟨12458969235342660755257489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66447835921827524028039941 12458969235342660755257489)
                ·
                  refine ⟨9344226926506995566443117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12458969235342660755257489 9344226926506995566443117)
                  ·
                    refine ⟨3504085097440123337416169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9344226926506995566443117 3504085097440123337416169)
                    ·
                      refine ⟨2628063823080092503062127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504085097440123337416169 2628063823080092503062127)
                      ·
                        rfl

theorem cell23_5118136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 2, 3, 2].length) (baseStart_5118136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118136 prefixEnd_5118136 := by exact prefixLift 5118136
  have htrace : WordTrace (prefixWord ++ tailWord_5118136) baseStart_5118136 baseEnd_5118136 := by
    simpa [prefixWord, tailWord_5118136, baseEnd_5118136] using wordTrace_append hprefix tailTrace_5118136
  have hstable : (prefixWord ++ tailWord_5118136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118136).length < 2 ^ (prefixWord ++ tailWord_5118136).sum := by decide
  have hdescent : baseEnd_5118136 < baseStart_5118136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118149 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_5118149 : Nat := 118140960795 + 5118149 * 2 ^ 59
def prefixEnd_5118149 : Nat := 4983230072969 + 3 ^ 40 * 5118149 * 2
def baseEnd_5118149 : Nat := 2628070498328600952199567

theorem tailTrace_5118149 : CollatzResearch.WordTrace tailWord_5118149 prefixEnd_5118149 2628070498328600952199567 := by
  unfold tailWord_5118149
  simp only [CollatzResearch.WordTrace]
  refine ⟨186674229934827758102837501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124449486623218505401891667 186674229934827758102837501)
  ·
    refine ⟨70002836225560409288564063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186674229934827758102837501 70002836225560409288564063)
    ·
      refine ⟨105004254338340613932846095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70002836225560409288564063 105004254338340613932846095)
      ·
        refine ⟨157506381507510920899269143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105004254338340613932846095 157506381507510920899269143)
        ·
          refine ⟨236259572261266381348903715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157506381507510920899269143 236259572261266381348903715)
          ·
            refine ⟨354389358391899572023355573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236259572261266381348903715 354389358391899572023355573)
            ·
              refine ⟨33224002349240584877189585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 354389358391899572023355573 33224002349240584877189585)
              ·
                refine ⟨24918001761930438657892189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33224002349240584877189585 24918001761930438657892189)
                ·
                  refine ⟨9344250660723914496709571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24918001761930438657892189 9344250660723914496709571)
                  ·
                    refine ⟨14016375991085871745064357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9344250660723914496709571 14016375991085871745064357)
                    ·
                      refine ⟨2628070498328600952199567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14016375991085871745064357 2628070498328600952199567)
                      ·
                        rfl

theorem cell23_5118149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_5118149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118149 prefixEnd_5118149 := by exact prefixLift 5118149
  have htrace : WordTrace (prefixWord ++ tailWord_5118149) baseStart_5118149 baseEnd_5118149 := by
    simpa [prefixWord, tailWord_5118149, baseEnd_5118149] using wordTrace_append hprefix tailTrace_5118149
  have hstable : (prefixWord ++ tailWord_5118149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118149).length < 2 ^ (prefixWord ++ tailWord_5118149).sum := by decide
  have hdescent : baseEnd_5118149 < baseStart_5118149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118159 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 1, 6]
def baseStart_5118159 : Nat := 118140960795 + 5118159 * 2 ^ 59
def prefixEnd_5118159 : Nat := 4983230072969 + 3 ^ 40 * 5118159 * 2
def baseEnd_5118159 : Nat := 876025211045048637691507

theorem tailTrace_5118159 : CollatzResearch.WordTrace tailWord_5118159 prefixEnd_5118159 876025211045048637691507 := by
  unfold tailWord_5118159
  simp only [CollatzResearch.WordTrace]
  refine ⟨186674594664791529810701531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124449729776527686540467687 186674594664791529810701531)
  ·
    refine ⟨280011891997187294716052297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186674594664791529810701531 280011891997187294716052297)
    ·
      refine ⟨210008918997890471037039223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280011891997187294716052297 210008918997890471037039223)
      ·
        refine ⟨315013378496835706555558835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210008918997890471037039223 315013378496835706555558835)
        ·
          refine ⟨472520067745253559833338253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315013378496835706555558835 472520067745253559833338253)
          ·
            refine ⟨177195025404470084937501845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 472520067745253559833338253 177195025404470084937501845)
            ·
              refine ⟨8306016815834535231445399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177195025404470084937501845 8306016815834535231445399)
              ·
                refine ⟨12459025223751802847168099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8306016815834535231445399 12459025223751802847168099)
                ·
                  refine ⟨18688537835627704270752149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12459025223751802847168099 18688537835627704270752149)
                  ·
                    refine ⟨876025211045048637691507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18688537835627704270752149 876025211045048637691507)
                    ·
                      rfl

theorem cell23_5118159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 6].length) (baseStart_5118159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118159 prefixEnd_5118159 := by exact prefixLift 5118159
  have htrace : WordTrace (prefixWord ++ tailWord_5118159) baseStart_5118159 baseEnd_5118159 := by
    simpa [prefixWord, tailWord_5118159, baseEnd_5118159] using wordTrace_append hprefix tailTrace_5118159
  have hstable : (prefixWord ++ tailWord_5118159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118159).length < 2 ^ (prefixWord ++ tailWord_5118159).sum := by decide
  have hdescent : baseEnd_5118159 < baseStart_5118159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118183 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_5118183 : Nat := 118140960795 + 5118183 * 2 ^ 59
def prefixEnd_5118183 : Nat := 4983230072969 + 3 ^ 40 * 5118183 * 2
def baseEnd_5118183 : Nat := 2628087956670853819174411

theorem tailTrace_5118183 : CollatzResearch.WordTrace tailWord_5118183 prefixEnd_5118183 2628087956670853819174411 := by
  unfold tailWord_5118183
  simp only [CollatzResearch.WordTrace]
  refine ⟨186675470016704581909575203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124450313344469721273050135 186675470016704581909575203)
  ·
    refine ⟨280013205025056872864362805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186675470016704581909575203 280013205025056872864362805)
    ·
      refine ⟨26251237971099081831034013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 280013205025056872864362805 26251237971099081831034013)
      ·
        refine ⟨9844214239162155686637755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26251237971099081831034013 9844214239162155686637755)
        ·
          refine ⟨14766321358743233529956633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9844214239162155686637755 14766321358743233529956633)
          ·
            refine ⟨11074741019057425147467475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14766321358743233529956633 11074741019057425147467475)
            ·
              refine ⟨16612111528586137721201213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11074741019057425147467475 16612111528586137721201213)
              ·
                refine ⟨6229541823219801645450455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16612111528586137721201213 6229541823219801645450455)
                ·
                  refine ⟨9344312734829702468175683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6229541823219801645450455 9344312734829702468175683)
                  ·
                    refine ⟨14016469102244553702263525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9344312734829702468175683 14016469102244553702263525)
                    ·
                      refine ⟨2628087956670853819174411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14016469102244553702263525 2628087956670853819174411)
                      ·
                        rfl

theorem cell23_5118183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_5118183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118183 prefixEnd_5118183 := by exact prefixLift 5118183
  have htrace : WordTrace (prefixWord ++ tailWord_5118183) baseStart_5118183 baseEnd_5118183 := by
    simpa [prefixWord, tailWord_5118183, baseEnd_5118183] using wordTrace_append hprefix tailTrace_5118183
  have hstable : (prefixWord ++ tailWord_5118183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118183).length < 2 ^ (prefixWord ++ tailWord_5118183).sum := by decide
  have hdescent : baseEnd_5118183 < baseStart_5118183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118229 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_5118229 : Nat := 118140960795 + 5118229 * 2 ^ 59
def prefixEnd_5118229 : Nat := 4983230072969 + 3 ^ 40 * 5118229 * 2
def baseEnd_5118229 : Nat := 2628111576780960639199199

theorem tailTrace_5118229 : CollatzResearch.WordTrace tailWord_5118229 prefixEnd_5118229 2628111576780960639199199 := by
  unfold tailWord_5118229
  simp only [CollatzResearch.WordTrace]
  refine ⟨186677147774537931765749741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124451431849691954510499827 186677147774537931765749741)
  ·
    refine ⟨70003930415451724412156153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186677147774537931765749741 70003930415451724412156153)
    ·
      refine ⟨52502947811588793309117115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70003930415451724412156153 52502947811588793309117115)
      ·
        refine ⟨78754421717383189963675673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52502947811588793309117115 78754421717383189963675673)
        ·
          refine ⟨59065816288037392472756755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78754421717383189963675673 59065816288037392472756755)
          ·
            refine ⟨88598724432056088709135133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59065816288037392472756755 88598724432056088709135133)
            ·
              refine ⟨33224521662021033265925675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88598724432056088709135133 33224521662021033265925675)
              ·
                refine ⟨49836782493031549898888513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33224521662021033265925675 49836782493031549898888513)
                ·
                  refine ⟨37377586869773662424166385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49836782493031549898888513 37377586869773662424166385)
                  ·
                    refine ⟨28033190152330246818124789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37377586869773662424166385 28033190152330246818124789)
                    ·
                      refine ⟨2628111576780960639199199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28033190152330246818124789 2628111576780960639199199)
                      ·
                        rfl

theorem cell23_5118229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_5118229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118229 prefixEnd_5118229 := by exact prefixLift 5118229
  have htrace : WordTrace (prefixWord ++ tailWord_5118229) baseStart_5118229 baseEnd_5118229 := by
    simpa [prefixWord, tailWord_5118229, baseEnd_5118229] using wordTrace_append hprefix tailTrace_5118229
  have hstable : (prefixWord ++ tailWord_5118229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118229).length < 2 ^ (prefixWord ++ tailWord_5118229).sum := by decide
  have hdescent : baseEnd_5118229 < baseStart_5118229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118234 : List Nat := [3, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2]
def baseStart_5118234 : Nat := 118140960795 + 5118234 * 2 ^ 59
def prefixEnd_5118234 : Nat := 4983230072969 + 3 ^ 40 * 5118234 * 2
def baseEnd_5118234 : Nat := 2628114144184233119636677

theorem tailTrace_5118234 : CollatzResearch.WordTrace tailWord_5118234 prefixEnd_5118234 2628114144184233119636677 := by
  unfold tailWord_5118234
  simp only [CollatzResearch.WordTrace]
  refine ⟨46669332534879954404920439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124451553426346545079787837 46669332534879954404920439)
  ·
    refine ⟨70003998802319931607380659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46669332534879954404920439 70003998802319931607380659)
    ·
      refine ⟨105005998203479897411070989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70003998802319931607380659 105005998203479897411070989)
      ·
        refine ⟨39377249326304961529151621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105005998203479897411070989 39377249326304961529151621)
        ·
          refine ⟨7383234248682180286715929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39377249326304961529151621 7383234248682180286715929)
          ·
            refine ⟨5537425686511635215036947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7383234248682180286715929 5537425686511635215036947)
            ·
              refine ⟨8306138529767452822555421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5537425686511635215036947 8306138529767452822555421)
              ·
                refine ⟨3114801948662794808458283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8306138529767452822555421 3114801948662794808458283)
                ·
                  refine ⟨4672202922994192212687425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114801948662794808458283 4672202922994192212687425)
                  ·
                    refine ⟨3504152192245644159515569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4672202922994192212687425 3504152192245644159515569)
                    ·
                      refine ⟨2628114144184233119636677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504152192245644159515569 2628114144184233119636677)
                      ·
                        rfl

theorem cell23_5118234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_5118234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118234 prefixEnd_5118234 := by exact prefixLift 5118234
  have htrace : WordTrace (prefixWord ++ tailWord_5118234) baseStart_5118234 baseEnd_5118234 := by
    simpa [prefixWord, tailWord_5118234, baseEnd_5118234] using wordTrace_append hprefix tailTrace_5118234
  have hstable : (prefixWord ++ tailWord_5118234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118234).length < 2 ^ (prefixWord ++ tailWord_5118234).sum := by decide
  have hdescent : baseEnd_5118234 < baseStart_5118234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118243 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 1, 3, 2]
def baseStart_5118243 : Nat := 118140960795 + 5118243 * 2 ^ 59
def prefixEnd_5118243 : Nat := 4983230072969 + 3 ^ 40 * 5118243 * 2
def baseEnd_5118243 : Nat := 2628118765510123584424135

theorem tailTrace_5118243 : CollatzResearch.WordTrace tailWord_5118243 prefixEnd_5118243 2628118765510123584424135 := by
  unfold tailWord_5118243
  simp only [CollatzResearch.WordTrace]
  refine ⟨186677658396487212156759383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124451772264324808104506255 186677658396487212156759383)
  ·
    refine ⟨280016487594730818235139075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186677658396487212156759383 280016487594730818235139075)
    ·
      refine ⟨420024731392096227352708613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280016487594730818235139075 420024731392096227352708613)
      ·
        refine ⟨78754637136018042628632865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 420024731392096227352708613 78754637136018042628632865)
        ·
          refine ⟨59065977852013531971474649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78754637136018042628632865 59065977852013531971474649)
          ·
            refine ⟨44299483389010148978605987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59065977852013531971474649 44299483389010148978605987)
            ·
              refine ⟨66449225083515223467908981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44299483389010148978605987 66449225083515223467908981)
              ·
                refine ⟨6229614851579552200116467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66449225083515223467908981 6229614851579552200116467)
                ·
                  refine ⟨9344422277369328300174701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6229614851579552200116467 9344422277369328300174701)
                  ·
                    refine ⟨3504158354013498112565513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9344422277369328300174701 3504158354013498112565513)
                    ·
                      refine ⟨2628118765510123584424135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504158354013498112565513 2628118765510123584424135)
                      ·
                        rfl

theorem cell23_5118243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_5118243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118243 prefixEnd_5118243 := by exact prefixLift 5118243
  have htrace : WordTrace (prefixWord ++ tailWord_5118243) baseStart_5118243 baseEnd_5118243 := by
    simpa [prefixWord, tailWord_5118243, baseEnd_5118243] using wordTrace_append hprefix tailTrace_5118243
  have hstable : (prefixWord ++ tailWord_5118243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118243).length < 2 ^ (prefixWord ++ tailWord_5118243).sum := by decide
  have hdescent : baseEnd_5118243 < baseStart_5118243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118256 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 5, 4, 2]
def baseStart_5118256 : Nat := 118140960795 + 5118256 * 2 ^ 59
def prefixEnd_5118256 : Nat := 4983230072969 + 3 ^ 40 * 5118256 * 2
def baseEnd_5118256 : Nat := 2628125440758632033561575

theorem tailTrace_5118256 : CollatzResearch.WordTrace tailWord_5118256 prefixEnd_5118256 2628125440758632033561575 := by
  unfold tailWord_5118256
  simp only [CollatzResearch.WordTrace]
  refine ⟨93339066272720057688491311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124452088363626743584655081 93339066272720057688491311)
  ·
    refine ⟨140008599409080086532736967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93339066272720057688491311 140008599409080086532736967)
    ·
      refine ⟨210012899113620129799105451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140008599409080086532736967 210012899113620129799105451)
      ·
        refine ⟨315019348670430194698658177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210012899113620129799105451 315019348670430194698658177)
        ·
          refine ⟨236264511502822646023993633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315019348670430194698658177 236264511502822646023993633)
          ·
            refine ⟨177198383627116984517995225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236264511502822646023993633 177198383627116984517995225)
            ·
              refine ⟨132898787720337738388496419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177198383627116984517995225 132898787720337738388496419)
              ·
                refine ⟨199348181580506607582744629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132898787720337738388496419 199348181580506607582744629)
                ·
                  refine ⟨18688892023172494460882309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 199348181580506607582744629 18688892023172494460882309)
                  ·
                    refine ⟨3504167254344842711415433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18688892023172494460882309 3504167254344842711415433)
                    ·
                      refine ⟨2628125440758632033561575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504167254344842711415433 2628125440758632033561575)
                      ·
                        rfl

theorem cell23_5118256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 5, 4, 2].length) (baseStart_5118256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118256 prefixEnd_5118256 := by exact prefixLift 5118256
  have htrace : WordTrace (prefixWord ++ tailWord_5118256) baseStart_5118256 baseEnd_5118256 := by
    simpa [prefixWord, tailWord_5118256, baseEnd_5118256] using wordTrace_append hprefix tailTrace_5118256
  have hstable : (prefixWord ++ tailWord_5118256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118256).length < 2 ^ (prefixWord ++ tailWord_5118256).sum := by decide
  have hdescent : baseEnd_5118256 < baseStart_5118256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118259 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 5]
def baseStart_5118259 : Nat := 118140960795 + 5118259 * 2 ^ 59
def prefixEnd_5118259 : Nat := 4983230072969 + 3 ^ 40 * 5118259 * 2
def baseEnd_5118259 : Nat := 2628126981200595521824061

theorem tailTrace_5118259 : CollatzResearch.WordTrace tailWord_5118259 prefixEnd_5118259 2628126981200595521824061 := by
  unfold tailWord_5118259
  simp only [CollatzResearch.WordTrace]
  refine ⟨186678241964429246889341831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124452161309619497926227887 186678241964429246889341831)
  ·
    refine ⟨280017362946643870334012747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186678241964429246889341831 280017362946643870334012747)
    ·
      refine ⟨420026044419965805501019121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280017362946643870334012747 420026044419965805501019121)
      ·
        refine ⟨315019533314974354125764341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420026044419965805501019121 315019533314974354125764341)
        ·
          refine ⟨29533081248278845699290407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 315019533314974354125764341 29533081248278845699290407)
          ·
            refine ⟨44299621872418268548935611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29533081248278845699290407 44299621872418268548935611)
            ·
              refine ⟨66449432808627402823403417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44299621872418268548935611 66449432808627402823403417)
              ·
                refine ⟨49837074606470552117552563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66449432808627402823403417 49837074606470552117552563)
                ·
                  refine ⟨74755611909705828176328845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49837074606470552117552563 74755611909705828176328845)
                  ·
                    refine ⟨28033354466139685566123317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74755611909705828176328845 28033354466139685566123317)
                    ·
                      refine ⟨2628126981200595521824061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28033354466139685566123317 2628126981200595521824061)
                      ·
                        rfl

theorem cell23_5118259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_5118259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118259 prefixEnd_5118259 := by exact prefixLift 5118259
  have htrace : WordTrace (prefixWord ++ tailWord_5118259) baseStart_5118259 baseEnd_5118259 := by
    simpa [prefixWord, tailWord_5118259, baseEnd_5118259] using wordTrace_append hprefix tailTrace_5118259
  have hstable : (prefixWord ++ tailWord_5118259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118259).length < 2 ^ (prefixWord ++ tailWord_5118259).sum := by decide
  have hdescent : baseEnd_5118259 < baseStart_5118259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118279 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 9]
def baseStart_5118279 : Nat := 118140960795 + 5118279 * 2 ^ 59
def prefixEnd_5118279 : Nat := 4983230072969 + 3 ^ 40 * 5118279 * 2
def baseEnd_5118279 : Nat := 292015250090409493730441

theorem tailTrace_5118279 : CollatzResearch.WordTrace tailWord_5118279 prefixEnd_5118279 292015250090409493730441 := by
  unfold tailWord_5118279
  simp only [CollatzResearch.WordTrace]
  refine ⟨186678971424356790305069891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124452647616237860203379927 186678971424356790305069891)
  ·
    refine ⟨280018457136535185457604837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186678971424356790305069891 280018457136535185457604837)
    ·
      refine ⟨52503460713100347273300907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280018457136535185457604837 52503460713100347273300907)
      ·
        refine ⟨78755191069650520909951361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52503460713100347273300907 78755191069650520909951361)
        ·
          refine ⟨59066393302237890682463521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78755191069650520909951361 59066393302237890682463521)
          ·
            refine ⟨44299794976678418011847641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59066393302237890682463521 44299794976678418011847641)
            ·
              refine ⟨33224846232508813508885731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44299794976678418011847641 33224846232508813508885731)
              ·
                refine ⟨49837269348763220263328597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33224846232508813508885731 49837269348763220263328597)
                ·
                  refine ⟨292015250090409493730441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49837269348763220263328597 292015250090409493730441)
                  ·
                    rfl

theorem cell23_5118279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 9].length) (baseStart_5118279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118279 prefixEnd_5118279 := by exact prefixLift 5118279
  have htrace : WordTrace (prefixWord ++ tailWord_5118279) baseStart_5118279 baseEnd_5118279 := by
    simpa [prefixWord, tailWord_5118279, baseEnd_5118279] using wordTrace_append hprefix tailTrace_5118279
  have hstable : (prefixWord ++ tailWord_5118279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118279).length < 2 ^ (prefixWord ++ tailWord_5118279).sum := by decide
  have hdescent : baseEnd_5118279 < baseStart_5118279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118302 : List Nat := [4, 4, 2, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_5118302 : Nat := 118140960795 + 5118302 * 2 ^ 59
def prefixEnd_5118302 : Nat := 4983230072969 + 3 ^ 40 * 5118302 * 2
def baseEnd_5118302 : Nat := 2628149060868738853586365

theorem tailTrace_5118302 : CollatzResearch.WordTrace tailWord_5118302 prefixEnd_5118302 2628149060868738853586365 := by
  unfold tailWord_5118302
  simp only [CollatzResearch.WordTrace]
  refine ⟨23334976287909183154144645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124453206868848976822104773 23334976287909183154144645)
  ·
    refine ⟨4375308053982971841402121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23334976287909183154144645 4375308053982971841402121)
    ·
      refine ⟨3281481040487228881051591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4375308053982971841402121 3281481040487228881051591)
      ·
        refine ⟨4922221560730843321577387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3281481040487228881051591 4922221560730843321577387)
        ·
          refine ⟨7383332341096264982366081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922221560730843321577387 7383332341096264982366081)
          ·
            refine ⟨5537499255822198736774561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7383332341096264982366081 5537499255822198736774561)
            ·
              refine ⟨4153124441866649052580921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5537499255822198736774561 4153124441866649052580921)
              ·
                refine ⟨3114843331399986789435691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4153124441866649052580921 3114843331399986789435691)
                ·
                  refine ⟨4672264997099980184153537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114843331399986789435691 4672264997099980184153537)
                  ·
                    refine ⟨3504198747824985138115153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4672264997099980184153537 3504198747824985138115153)
                    ·
                      refine ⟨2628149060868738853586365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504198747824985138115153 2628149060868738853586365)
                      ·
                        rfl

theorem cell23_5118302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_5118302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118302 prefixEnd_5118302 := by exact prefixLift 5118302
  have htrace : WordTrace (prefixWord ++ tailWord_5118302) baseStart_5118302 baseEnd_5118302 := by
    simpa [prefixWord, tailWord_5118302, baseEnd_5118302] using wordTrace_append hprefix tailTrace_5118302
  have hstable : (prefixWord ++ tailWord_5118302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118302).length < 2 ^ (prefixWord ++ tailWord_5118302).sum := by decide
  have hdescent : baseEnd_5118302 < baseStart_5118302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118319 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 7]
def baseStart_5118319 : Nat := 118140960795 + 5118319 * 2 ^ 59
def prefixEnd_5118319 : Nat := 4983230072969 + 3 ^ 40 * 5118319 * 2
def baseEnd_5118319 : Nat := 2628157790039865287073785

theorem tailTrace_5118319 : CollatzResearch.WordTrace tailWord_5118319 prefixEnd_5118319 2628157790039865287073785 := by
  unfold tailWord_5118319
  simp only [CollatzResearch.WordTrace]
  refine ⟨186680430344211877136526011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124453620229474584757684007 186680430344211877136526011)
  ·
    refine ⟨280020645516317815704789017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186680430344211877136526011 280020645516317815704789017)
    ·
      refine ⟨210015484137238361778591763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280020645516317815704789017 210015484137238361778591763)
      ·
        refine ⟨315023226205857542667887645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210015484137238361778591763 315023226205857542667887645)
        ·
          refine ⟨118133709827196578500457867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315023226205857542667887645 118133709827196578500457867)
          ·
            refine ⟨177200564740794867750686801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118133709827196578500457867 177200564740794867750686801)
            ·
              refine ⟨132900423555596150813015101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177200564740794867750686801 132900423555596150813015101)
              ·
                refine ⟨49837658833348556554880663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132900423555596150813015101 49837658833348556554880663)
                ·
                  refine ⟨74756488250022834832320995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49837658833348556554880663 74756488250022834832320995)
                  ·
                    refine ⟨112134732375034252248481493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74756488250022834832320995 112134732375034252248481493)
                    ·
                      refine ⟨2628157790039865287073785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112134732375034252248481493 2628157790039865287073785)
                      ·
                        rfl

theorem cell23_5118319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_5118319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118319 prefixEnd_5118319 := by exact prefixLift 5118319
  have htrace : WordTrace (prefixWord ++ tailWord_5118319) baseStart_5118319 baseEnd_5118319 := by
    simpa [prefixWord, tailWord_5118319, baseEnd_5118319] using wordTrace_append hprefix tailTrace_5118319
  have hstable : (prefixWord ++ tailWord_5118319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118319).length < 2 ^ (prefixWord ++ tailWord_5118319).sum := by decide
  have hdescent : baseEnd_5118319 < baseStart_5118319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118373 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 3, 4]
def baseStart_5118373 : Nat := 118140960795 + 5118373 * 2 ^ 59
def prefixEnd_5118373 : Nat := 4983230072969 + 3 ^ 40 * 5118373 * 2
def baseEnd_5118373 : Nat := 876061839331736025266179

theorem tailTrace_5118373 : CollatzResearch.WordTrace tailWord_5118373 prefixEnd_5118373 876061839331736025266179 := by
  unfold tailWord_5118373
  simp only [CollatzResearch.WordTrace]
  refine ⟨186682399886016244358991773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124454933257344162905994515 186682399886016244358991773)
  ·
    refine ⟨70005899957256091634621915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186682399886016244358991773 70005899957256091634621915)
    ·
      refine ⟨105008849935884137451932873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70005899957256091634621915 105008849935884137451932873)
      ·
        refine ⟨78756637451913103088949655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105008849935884137451932873 78756637451913103088949655)
        ·
          refine ⟨118134956177869654633424483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78756637451913103088949655 118134956177869654633424483)
          ·
            refine ⟨177202434266804481950136725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118134956177869654633424483 177202434266804481950136725)
            ·
              refine ⟨8306364106256460091412659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177202434266804481950136725 8306364106256460091412659)
              ·
                refine ⟨12459546159384690137118989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8306364106256460091412659 12459546159384690137118989)
                ·
                  refine ⟨4672329809769258801419621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12459546159384690137118989 4672329809769258801419621)
                  ·
                    refine ⟨876061839331736025266179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4672329809769258801419621 876061839331736025266179)
                    ·
                      rfl

theorem cell23_5118373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_5118373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118373 prefixEnd_5118373 := by exact prefixLift 5118373
  have htrace : WordTrace (prefixWord ++ tailWord_5118373) baseStart_5118373 baseEnd_5118373 := by
    simpa [prefixWord, tailWord_5118373, baseEnd_5118373] using wordTrace_append hprefix tailTrace_5118373
  have hstable : (prefixWord ++ tailWord_5118373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118373).length < 2 ^ (prefixWord ++ tailWord_5118373).sum := by decide
  have hdescent : baseEnd_5118373 < baseStart_5118373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118407 : List Nat := [1, 1, 4, 1, 1, 6, 1, 3, 1, 4]
def baseStart_5118407 : Nat := 118140960795 + 5118407 * 2 ^ 59
def prefixEnd_5118407 : Nat := 4983230072969 + 3 ^ 40 * 5118407 * 2
def baseEnd_5118407 : Nat := 876067658779153647591127

theorem tailTrace_5118407 : CollatzResearch.WordTrace tailWord_5118407 prefixEnd_5118407 876067658779153647591127 := by
  unfold tailWord_5118407
  simp only [CollatzResearch.WordTrace]
  refine ⟨186683639967893068165729475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124455759978595378777152983 186683639967893068165729475)
  ·
    refine ⟨280025459951839602248594213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186683639967893068165729475 280025459951839602248594213)
    ·
      refine ⟨52504773740969925421611415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280025459951839602248594213 52504773740969925421611415)
      ·
        refine ⟨78757160611454888132417123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52504773740969925421611415 78757160611454888132417123)
        ·
          refine ⟨118135740917182332198625685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78757160611454888132417123 118135740917182332198625685)
          ·
            refine ⟨5537612855492921821810579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118135740917182332198625685 5537612855492921821810579)
            ·
              refine ⟨8306419283239382732715869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5537612855492921821810579 8306419283239382732715869)
              ·
                refine ⟨3114907231214768524768451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8306419283239382732715869 3114907231214768524768451)
                ·
                  refine ⟨4672360846822152787152677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3114907231214768524768451 4672360846822152787152677)
                  ·
                    refine ⟨876067658779153647591127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4672360846822152787152677 876067658779153647591127)
                    ·
                      rfl

theorem cell23_5118407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_5118407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118407 prefixEnd_5118407 := by exact prefixLift 5118407
  have htrace : WordTrace (prefixWord ++ tailWord_5118407) baseStart_5118407 baseEnd_5118407 := by
    simpa [prefixWord, tailWord_5118407, baseEnd_5118407] using wordTrace_append hprefix tailTrace_5118407
  have hstable : (prefixWord ++ tailWord_5118407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118407).length < 2 ^ (prefixWord ++ tailWord_5118407).sum := by decide
  have hdescent : baseEnd_5118407 < baseStart_5118407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118436 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_5118436 : Nat := 118140960795 + 5118436 * 2 ^ 59
def prefixEnd_5118436 : Nat := 4983230072969 + 3 ^ 40 * 5118436 * 2
def baseEnd_5118436 : Nat := 2628217867276441329310747

theorem tailTrace_5118436 : CollatzResearch.WordTrace tailWord_5118436 prefixEnd_5118436 2628217867276441329310747 := by
  unfold tailWord_5118436
  simp only [CollatzResearch.WordTrace]
  refine ⟨93342348842394003059267581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124456465123192004079023441 93342348842394003059267581)
  ·
    refine ⟨35003380815897751147225343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93342348842394003059267581 35003380815897751147225343)
    ·
      refine ⟨52505071223846626720838015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35003380815897751147225343 52505071223846626720838015)
      ·
        refine ⟨78757606835769940081257023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52505071223846626720838015 78757606835769940081257023)
        ·
          refine ⟨118136410253654910121885535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78757606835769940081257023 118136410253654910121885535)
          ·
            refine ⟨177204615380482365182828303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118136410253654910121885535 177204615380482365182828303)
            ·
              refine ⟨265806923070723547774242455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177204615380482365182828303 265806923070723547774242455)
              ·
                refine ⟨398710384606085321661363683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265806923070723547774242455 398710384606085321661363683)
                ·
                  refine ⟨598065576909127982492045525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398710384606085321661363683 598065576909127982492045525)
                  ·
                    refine ⟨14017161958807687089657317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 598065576909127982492045525 14017161958807687089657317)
                    ·
                      refine ⟨2628217867276441329310747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14017161958807687089657317 2628217867276441329310747)
                      ·
                        rfl

theorem cell23_5118436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_5118436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118436 prefixEnd_5118436 := by exact prefixLift 5118436
  have htrace : WordTrace (prefixWord ++ tailWord_5118436) baseStart_5118436 baseEnd_5118436 := by
    simpa [prefixWord, tailWord_5118436, baseEnd_5118436] using wordTrace_append hprefix tailTrace_5118436
  have hstable : (prefixWord ++ tailWord_5118436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118436).length < 2 ^ (prefixWord ++ tailWord_5118436).sum := by decide
  have hdescent : baseEnd_5118436 < baseStart_5118436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118437 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 6]
def baseStart_5118437 : Nat := 118140960795 + 5118437 * 2 ^ 59
def prefixEnd_5118437 : Nat := 4983230072969 + 3 ^ 40 * 5118437 * 2
def baseEnd_5118437 : Nat := 292024264528566202822027

theorem tailTrace_5118437 : CollatzResearch.WordTrace tailWord_5118437 prefixEnd_5118437 292024264528566202822027 := by
  unfold tailWord_5118437
  simp only [CollatzResearch.WordTrace]
  refine ⟨186684734157784383289321565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124456489438522922192881043 186684734157784383289321565)
  ·
    refine ⟨70006775309169143733495587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186684734157784383289321565 70006775309169143733495587)
    ·
      refine ⟨105010162963753715600243381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70006775309169143733495587 105010162963753715600243381)
      ·
        refine ⟨9844702777851910837522817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105010162963753715600243381 9844702777851910837522817)
        ·
          refine ⟨7383527083388933128142113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9844702777851910837522817 7383527083388933128142113)
          ·
            refine ⟨5537645312541699846106585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7383527083388933128142113 5537645312541699846106585)
            ·
              refine ⟨4153233984406274884579939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5537645312541699846106585 4153233984406274884579939)
              ·
                refine ⟨6229850976609412326869909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4153233984406274884579939 6229850976609412326869909)
                ·
                  refine ⟨292024264528566202822027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6229850976609412326869909 292024264528566202822027)
                  ·
                    rfl

theorem cell23_5118437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_5118437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118437 prefixEnd_5118437 := by exact prefixLift 5118437
  have htrace : WordTrace (prefixWord ++ tailWord_5118437) baseStart_5118437 baseEnd_5118437 := by
    simpa [prefixWord, tailWord_5118437, baseEnd_5118437] using wordTrace_append hprefix tailTrace_5118437
  have hstable : (prefixWord ++ tailWord_5118437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118437).length < 2 ^ (prefixWord ++ tailWord_5118437).sum := by decide
  have hdescent : baseEnd_5118437 < baseStart_5118437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118450 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_5118450 : Nat := 118140960795 + 5118450 * 2 ^ 59
def prefixEnd_5118450 : Nat := 4983230072969 + 3 ^ 40 * 5118450 * 2
def baseEnd_5118450 : Nat := 876075018668534758178561

theorem tailTrace_5118450 : CollatzResearch.WordTrace tailWord_5118450 prefixEnd_5118450 876075018668534758178561 := by
  unfold tailWord_5118450
  simp only [CollatzResearch.WordTrace]
  refine ⟨46671302076684321627386201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124456805537824857673029869 46671302076684321627386201)
  ·
    refine ⟨35003476557513241220539651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46671302076684321627386201 35003476557513241220539651)
    ·
      refine ⟨52505214836269861830809477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35003476557513241220539651 52505214836269861830809477)
      ·
        refine ⟨9844727781800599093276777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52505214836269861830809477 9844727781800599093276777)
        ·
          refine ⟨7383545836350449319957583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9844727781800599093276777 7383545836350449319957583)
          ·
            refine ⟨11075318754525673979936375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7383545836350449319957583 11075318754525673979936375)
            ·
              refine ⟨16612978131788510969904563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11075318754525673979936375 16612978131788510969904563)
              ·
                refine ⟨24919467197682766454856845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16612978131788510969904563 24919467197682766454856845)
                ·
                  refine ⟨9344800199131037420571317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24919467197682766454856845 9344800199131037420571317)
                  ·
                    refine ⟨876075018668534758178561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9344800199131037420571317 876075018668534758178561)
                    ·
                      rfl

theorem cell23_5118450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_5118450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118450 prefixEnd_5118450 := by exact prefixLift 5118450
  have htrace : WordTrace (prefixWord ++ tailWord_5118450) baseStart_5118450 baseEnd_5118450 := by
    simpa [prefixWord, tailWord_5118450, baseEnd_5118450] using wordTrace_append hprefix tailTrace_5118450
  have hstable : (prefixWord ++ tailWord_5118450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118450).length < 2 ^ (prefixWord ++ tailWord_5118450).sum := by decide
  have hdescent : baseEnd_5118450 < baseStart_5118450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118476 : List Nat := [2, 2, 1, 2, 4, 12]
def baseStart_5118476 : Nat := 118140960795 + 5118476 * 2 ^ 59
def prefixEnd_5118476 : Nat := 4983230072969 + 3 ^ 40 * 5118476 * 2
def baseEnd_5118476 : Nat := 10815795911533420464241

theorem tailTrace_5118476 : CollatzResearch.WordTrace tailWord_5118476 prefixEnd_5118476 10815795911533420464241 := by
  unfold tailWord_5118476
  simp only [CollatzResearch.WordTrace]
  refine ⟨93343078302321546474995641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124457437736428728633327521 93343078302321546474995641)
  ·
    refine ⟨70007308726741159856246731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93343078302321546474995641 70007308726741159856246731)
    ·
      refine ⟨105010963090111739784370097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70007308726741159856246731 105010963090111739784370097)
      ·
        refine ⟨78758222317583804838277573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105010963090111739784370097 78758222317583804838277573)
        ·
          refine ⟨14767166684546963407177045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78758222317583804838277573 14767166684546963407177045)
          ·
            refine ⟨10815795911533420464241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14767166684546963407177045 10815795911533420464241)
            ·
              rfl

theorem cell23_5118476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 12].length) (baseStart_5118476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118476 prefixEnd_5118476 := by exact prefixLift 5118476
  have htrace : WordTrace (prefixWord ++ tailWord_5118476) baseStart_5118476 baseEnd_5118476 := by
    simpa [prefixWord, tailWord_5118476, baseEnd_5118476] using wordTrace_append hprefix tailTrace_5118476
  have hstable : (prefixWord ++ tailWord_5118476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118476).length < 2 ^ (prefixWord ++ tailWord_5118476).sum := by decide
  have hdescent : baseEnd_5118476 < baseStart_5118476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118493 : List Nat := [1, 4, 2, 2, 1, 2, 3, 8]
def baseStart_5118493 : Nat := 118140960795 + 5118493 * 2 ^ 59
def prefixEnd_5118493 : Nat := 4983230072969 + 3 ^ 40 * 5118493 * 2
def baseEnd_5118493 : Nat := 97342486506435096529555

theorem tailTrace_5118493 : CollatzResearch.WordTrace tailWord_5118493 prefixEnd_5118493 97342486506435096529555 := by
  unfold tailWord_5118493
  simp only [CollatzResearch.WordTrace]
  refine ⟨186686776645581504853360133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124457851097054336568906755 186686776645581504853360133)
  ·
    refine ⟨35003770621046532160005025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186686776645581504853360133 35003770621046532160005025)
    ·
      refine ⟨26252827965784899120003769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35003770621046532160005025 26252827965784899120003769)
      ·
        refine ⟨19689620974338674340002827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26252827965784899120003769 19689620974338674340002827)
        ·
          refine ⟨29534431461508011510004241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19689620974338674340002827 29534431461508011510004241)
          ·
            refine ⟨22150823596131008632503181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29534431461508011510004241 22150823596131008632503181)
            ·
              refine ⟨8306558848549128237188693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22150823596131008632503181 8306558848549128237188693)
              ·
                refine ⟨97342486506435096529555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8306558848549128237188693 97342486506435096529555)
                ·
                  rfl

theorem cell23_5118493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 8].length) (baseStart_5118493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118493 prefixEnd_5118493 := by exact prefixLift 5118493
  have htrace : WordTrace (prefixWord ++ tailWord_5118493) baseStart_5118493 baseEnd_5118493 := by
    simpa [prefixWord, tailWord_5118493, baseEnd_5118493] using wordTrace_append hprefix tailTrace_5118493
  have hstable : (prefixWord ++ tailWord_5118493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118493).length < 2 ^ (prefixWord ++ tailWord_5118493).sum := by decide
  have hdescent : baseEnd_5118493 < baseStart_5118493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118504 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_5118504 : Nat := 118140960795 + 5118504 * 2 ^ 59
def prefixEnd_5118504 : Nat := 4983230072969 + 3 ^ 40 * 5118504 * 2
def baseEnd_5118504 : Nat := 2628252783960947063260435

theorem tailTrace_5118504 : CollatzResearch.WordTrace tailWord_5118504 prefixEnd_5118504 2628252783960947063260435 := by
  unfold tailWord_5118504
  simp only [CollatzResearch.WordTrace]
  refine ⟨93343588924270826866005283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124458118565694435821340377 93343588924270826866005283)
  ·
    refine ⟨140015383386406240299007925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93343588924270826866005283 140015383386406240299007925)
    ·
      refine ⟨13126442192475585028031993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140015383386406240299007925 13126442192475585028031993)
      ·
        refine ⟨9844831644356688771023995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13126442192475585028031993 9844831644356688771023995)
        ·
          refine ⟨14767247466535033156535993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9844831644356688771023995 14767247466535033156535993)
          ·
            refine ⟨11075435599901274867401995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14767247466535033156535993 11075435599901274867401995)
            ·
              refine ⟨16613153399851912301102993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11075435599901274867401995 16613153399851912301102993)
              ·
                refine ⟨12459865049888934225827245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16613153399851912301102993 12459865049888934225827245)
                ·
                  refine ⟨4672449393708350334685217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12459865049888934225827245 4672449393708350334685217)
                  ·
                    refine ⟨3504337045281262751013913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4672449393708350334685217 3504337045281262751013913)
                    ·
                      refine ⟨2628252783960947063260435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504337045281262751013913 2628252783960947063260435)
                      ·
                        rfl

theorem cell23_5118504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_5118504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118504 prefixEnd_5118504 := by exact prefixLift 5118504
  have htrace : WordTrace (prefixWord ++ tailWord_5118504) baseStart_5118504 baseEnd_5118504 := by
    simpa [prefixWord, tailWord_5118504, baseEnd_5118504] using wordTrace_append hprefix tailTrace_5118504
  have hstable : (prefixWord ++ tailWord_5118504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118504).length < 2 ^ (prefixWord ++ tailWord_5118504).sum := by decide
  have hdescent : baseEnd_5118504 < baseStart_5118504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118520 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 4, 1, 3]
def baseStart_5118520 : Nat := 118140960795 + 5118520 * 2 ^ 59
def prefixEnd_5118520 : Nat := 4983230072969 + 3 ^ 40 * 5118520 * 2
def baseEnd_5118520 : Nat := 2628260999651419000660361

theorem tailTrace_5118520 : CollatzResearch.WordTrace tailWord_5118520 prefixEnd_5118520 2628260999651419000660361 := by
  unfold tailWord_5118520
  simp only [CollatzResearch.WordTrace]
  refine ⟨93343880708241844232296507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124458507610989125643062009 93343880708241844232296507)
  ·
    refine ⟨140015821062362766348444761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93343880708241844232296507 140015821062362766348444761)
    ·
      refine ⟨105011865796772074761333571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140015821062362766348444761 105011865796772074761333571)
      ·
        refine ⟨157517798695158112142000357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105011865796772074761333571 157517798695158112142000357)
        ·
          refine ⟨29534587255342146026625067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157517798695158112142000357 29534587255342146026625067)
          ·
            refine ⟨44301880883013219039937601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29534587255342146026625067 44301880883013219039937601)
            ·
              refine ⟨33226410662259914279953201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44301880883013219039937601 33226410662259914279953201)
              ·
                refine ⟨24919807996694935709964901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33226410662259914279953201 24919807996694935709964901)
                ·
                  refine ⟨4672463999380300445618419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24919807996694935709964901 4672463999380300445618419)
                  ·
                    refine ⟨7008695999070450668427629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4672463999380300445618419 7008695999070450668427629)
                    ·
                      refine ⟨2628260999651419000660361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7008695999070450668427629 2628260999651419000660361)
                      ·
                        rfl

theorem cell23_5118520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_5118520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118520 prefixEnd_5118520 := by exact prefixLift 5118520
  have htrace : WordTrace (prefixWord ++ tailWord_5118520) baseStart_5118520 baseEnd_5118520 := by
    simpa [prefixWord, tailWord_5118520, baseEnd_5118520] using wordTrace_append hprefix tailTrace_5118520
  have hstable : (prefixWord ++ tailWord_5118520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118520).length < 2 ^ (prefixWord ++ tailWord_5118520).sum := by decide
  have hdescent : baseEnd_5118520 < baseStart_5118520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118524 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 1, 2, 3]
def baseStart_5118524 : Nat := 118140960795 + 5118524 * 2 ^ 59
def prefixEnd_5118524 : Nat := 4983230072969 + 3 ^ 40 * 5118524 * 2
def baseEnd_5118524 : Nat := 2628263053574036985010343

theorem tailTrace_5118524 : CollatzResearch.WordTrace tailWord_5118524 prefixEnd_5118524 2628263053574036985010343 := by
  unfold tailWord_5118524
  simp only [CollatzResearch.WordTrace]
  refine ⟨93343953654234598573869313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124458604872312798098492417 93343953654234598573869313)
  ·
    refine ⟨70007965240675948930401985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93343953654234598573869313 70007965240675948930401985)
    ·
      refine ⟨52505973930506961697801489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70007965240675948930401985 52505973930506961697801489)
      ·
        refine ⟨39379480447880221273351117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52505973930506961697801489 39379480447880221273351117)
        ·
          refine ⟨14767305167955082977506669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39379480447880221273351117 14767305167955082977506669)
          ·
            refine ⟨5537739437983156116565001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14767305167955082977506669 5537739437983156116565001)
            ·
              refine ⟨4153304578487367087423751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5537739437983156116565001 4153304578487367087423751)
              ·
                refine ⟨6229956867731050631135627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4153304578487367087423751 6229956867731050631135627)
                ·
                  refine ⟨9344935301596575946703441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6229956867731050631135627 9344935301596575946703441)
                  ·
                    refine ⟨7008701476197431960027581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9344935301596575946703441 7008701476197431960027581)
                    ·
                      refine ⟨2628263053574036985010343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7008701476197431960027581 2628263053574036985010343)
                      ·
                        rfl

theorem cell23_5118524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_5118524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118524 prefixEnd_5118524 := by exact prefixLift 5118524
  have htrace : WordTrace (prefixWord ++ tailWord_5118524) baseStart_5118524 baseEnd_5118524 := by
    simpa [prefixWord, tailWord_5118524, baseEnd_5118524] using wordTrace_append hprefix tailTrace_5118524
  have hstable : (prefixWord ++ tailWord_5118524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118524).length < 2 ^ (prefixWord ++ tailWord_5118524).sum := by decide
  have hdescent : baseEnd_5118524 < baseStart_5118524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118558 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_5118558 : Nat := 118140960795 + 5118558 * 2 ^ 59
def prefixEnd_5118558 : Nat := 4983230072969 + 3 ^ 40 * 5118558 * 2
def baseEnd_5118558 : Nat := 2628280511916289851985187

theorem tailTrace_5118558 : CollatzResearch.WordTrace tailWord_5118558 prefixEnd_5118558 2628280511916289851985187 := by
  unfold tailWord_5118558
  simp only [CollatzResearch.WordTrace]
  refine ⟨23336143423793252619309541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124459431593564013969650885 23336143423793252619309541)
  ·
    refine ⟨4375526891961234866120539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23336143423793252619309541 4375526891961234866120539)
    ·
      refine ⟨6563290337941852299180809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4375526891961234866120539 6563290337941852299180809)
      ·
        refine ⟨4922467753456389224385607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6563290337941852299180809 4922467753456389224385607)
        ·
          refine ⟨7383701630184583836578411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922467753456389224385607 7383701630184583836578411)
          ·
            refine ⟨11075552445276875754867617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7383701630184583836578411 11075552445276875754867617)
            ·
              refine ⟨8306664333957656816150713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11075552445276875754867617 8306664333957656816150713)
              ·
                refine ⟨6229998250468242612113035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8306664333957656816150713 6229998250468242612113035)
                ·
                  refine ⟨9344997375702363918169553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6229998250468242612113035 9344997375702363918169553)
                  ·
                    refine ⟨7008748031776772938627165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9344997375702363918169553 7008748031776772938627165)
                    ·
                      refine ⟨2628280511916289851985187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7008748031776772938627165 2628280511916289851985187)
                      ·
                        rfl

theorem cell23_5118558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_5118558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118558 prefixEnd_5118558 := by exact prefixLift 5118558
  have htrace : WordTrace (prefixWord ++ tailWord_5118558) baseStart_5118558 baseEnd_5118558 := by
    simpa [prefixWord, tailWord_5118558, baseEnd_5118558] using wordTrace_append hprefix tailTrace_5118558
  have hstable : (prefixWord ++ tailWord_5118558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118558).length < 2 ^ (prefixWord ++ tailWord_5118558).sum := by decide
  have hdescent : baseEnd_5118558 < baseStart_5118558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118563 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 5]
def baseStart_5118563 : Nat := 118140960795 + 5118563 * 2 ^ 59
def prefixEnd_5118563 : Nat := 4983230072969 + 3 ^ 40 * 5118563 * 2
def baseEnd_5118563 : Nat := 2628283079319562332422663

theorem tailTrace_5118563 : CollatzResearch.WordTrace tailWord_5118563 prefixEnd_5118563 2628283079319562332422663 := by
  unfold tailWord_5118563
  simp only [CollatzResearch.WordTrace]
  refine ⟨186689329755327906808408343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124459553170218604538938895 186689329755327906808408343)
  ·
    refine ⟨280033994632991860212612515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186689329755327906808408343 280033994632991860212612515)
    ·
      refine ⟨420050991949487790318918773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 280033994632991860212612515 420050991949487790318918773)
      ·
        refine ⟨39379780495264480342398635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 420050991949487790318918773 39379780495264480342398635)
        ·
          refine ⟨59069670742896720513597953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39379780495264480342398635 59069670742896720513597953)
          ·
            refine ⟨44302253057172540385198465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59069670742896720513597953 44302253057172540385198465)
            ·
              refine ⟨33226689792879405288898849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44302253057172540385198465 33226689792879405288898849)
              ·
                refine ⟨24920017344659553966674137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33226689792879405288898849 24920017344659553966674137)
                ·
                  refine ⟨18690013008494665475005603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24920017344659553966674137 18690013008494665475005603)
                  ·
                    refine ⟨28035019512741998212508405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18690013008494665475005603 28035019512741998212508405)
                    ·
                      refine ⟨2628283079319562332422663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28035019512741998212508405 2628283079319562332422663)
                      ·
                        rfl

theorem cell23_5118563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_5118563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118563 prefixEnd_5118563 := by exact prefixLift 5118563
  have htrace : WordTrace (prefixWord ++ tailWord_5118563) baseStart_5118563 baseEnd_5118563 := by
    simpa [prefixWord, tailWord_5118563, baseEnd_5118563] using wordTrace_append hprefix tailTrace_5118563
  have hstable : (prefixWord ++ tailWord_5118563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118563).length < 2 ^ (prefixWord ++ tailWord_5118563).sum := by decide
  have hdescent : baseEnd_5118563 < baseStart_5118563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118593 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_5118593 : Nat := 118140960795 + 5118593 * 2 ^ 59
def prefixEnd_5118593 : Nat := 4983230072969 + 3 ^ 40 * 5118593 * 2
def baseEnd_5118593 : Nat := 2628298483739197215047525

theorem tailTrace_5118593 : CollatzResearch.WordTrace tailWord_5118593 prefixEnd_5118593 2628298483739197215047525 := by
  unfold tailWord_5118593
  simp only [CollatzResearch.WordTrace]
  refine ⟨186690423945219221932000433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124460282630146147954666955 186690423945219221932000433)
  ·
    refine ⟨140017817958914416449000325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186690423945219221932000433 140017817958914416449000325)
    ·
      refine ⟨26253340867296453084187561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140017817958914416449000325 26253340867296453084187561)
      ·
        refine ⟨19690005650472339813140671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26253340867296453084187561 19690005650472339813140671)
        ·
          refine ⟨29535008475708509719711007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19690005650472339813140671 29535008475708509719711007)
          ·
            refine ⟨44302512713562764579566511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29535008475708509719711007 44302512713562764579566511)
            ·
              refine ⟨66453769070344146869349767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44302512713562764579566511 66453769070344146869349767)
              ·
                refine ⟨99680653605516220304024651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66453769070344146869349767 99680653605516220304024651)
                ·
                  refine ⟨149520980408274330456036977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99680653605516220304024651 149520980408274330456036977)
                  ·
                    refine ⟨112140735306205747842027733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 149520980408274330456036977 112140735306205747842027733)
                    ·
                      refine ⟨2628298483739197215047525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112140735306205747842027733 2628298483739197215047525)
                      ·
                        rfl

theorem cell23_5118593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_5118593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118593 prefixEnd_5118593 := by exact prefixLift 5118593
  have htrace : WordTrace (prefixWord ++ tailWord_5118593) baseStart_5118593 baseEnd_5118593 := by
    simpa [prefixWord, tailWord_5118593, baseEnd_5118593] using wordTrace_append hprefix tailTrace_5118593
  have hstable : (prefixWord ++ tailWord_5118593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118593).length < 2 ^ (prefixWord ++ tailWord_5118593).sum := by decide
  have hdescent : baseEnd_5118593 < baseStart_5118593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118650 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_5118650 : Nat := 118140960795 + 5118650 * 2 ^ 59
def prefixEnd_5118650 : Nat := 4983230072969 + 3 ^ 40 * 5118650 * 2
def baseEnd_5118650 : Nat := 2628327752136503492034763

theorem tailTrace_5118650 : CollatzResearch.WordTrace tailWord_5118650 prefixEnd_5118650 2628327752136503492034763 := by
  unfold tailWord_5118650
  simp only [CollatzResearch.WordTrace]
  refine ⟨46673125726503180166706351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124461668604008480444550269 46673125726503180166706351)
  ·
    refine ⟨70009688589754770250059527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46673125726503180166706351 70009688589754770250059527)
    ·
      refine ⟨105014532884632155375089291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70009688589754770250059527 105014532884632155375089291)
      ·
        refine ⟨157521799326948233062633937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105014532884632155375089291 157521799326948233062633937)
        ·
          refine ⟨118141349495211174796975453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157521799326948233062633937 118141349495211174796975453)
          ·
            refine ⟨44303006060704190548865795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118141349495211174796975453 44303006060704190548865795)
            ·
              refine ⟨66454509091056285823298693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44303006060704190548865795 66454509091056285823298693)
              ·
                refine ⟨12460220454573053591868505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66454509091056285823298693 12460220454573053591868505)
                ·
                  refine ⟨9345165340929790193901379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12460220454573053591868505 9345165340929790193901379)
                  ·
                    refine ⟨14017748011394685290852069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9345165340929790193901379 14017748011394685290852069)
                    ·
                      refine ⟨2628327752136503492034763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14017748011394685290852069 2628327752136503492034763)
                      ·
                        rfl

theorem cell23_5118650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_5118650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118650 prefixEnd_5118650 := by exact prefixLift 5118650
  have htrace : WordTrace (prefixWord ++ tailWord_5118650) baseStart_5118650 baseEnd_5118650 := by
    simpa [prefixWord, tailWord_5118650, baseEnd_5118650] using wordTrace_append hprefix tailTrace_5118650
  have hstable : (prefixWord ++ tailWord_5118650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118650).length < 2 ^ (prefixWord ++ tailWord_5118650).sum := by decide
  have hdescent : baseEnd_5118650 < baseStart_5118650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118663 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_5118663 : Nat := 118140960795 + 5118663 * 2 ^ 59
def prefixEnd_5118663 : Nat := 4983230072969 + 3 ^ 40 * 5118663 * 2
def baseEnd_5118663 : Nat := 2628334427385011941172203

theorem tailTrace_5118663 : CollatzResearch.WordTrace tailWord_5118663 prefixEnd_5118663 2628334427385011941172203 := by
  unfold tailWord_5118663
  simp only [CollatzResearch.WordTrace]
  refine ⟨186692977054965623887048643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124461984703310415924699095 186692977054965623887048643)
  ·
    refine ⟨280039465582448435830572965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186692977054965623887048643 280039465582448435830572965)
    ·
      refine ⟨52507399796709081718232431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280039465582448435830572965 52507399796709081718232431)
      ·
        refine ⟨78761099695063622577348647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52507399796709081718232431 78761099695063622577348647)
        ·
          refine ⟨118141649542595433866022971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78761099695063622577348647 118141649542595433866022971)
          ·
            refine ⟨177212474313893150799034457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118141649542595433866022971 177212474313893150799034457)
            ·
              refine ⟨132909355735419863099275843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177212474313893150799034457 132909355735419863099275843)
              ·
                refine ⟨199364033603129794648913765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132909355735419863099275843 199364033603129794648913765)
                ·
                  refine ⟨37380756300586836496671331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199364033603129794648913765 37380756300586836496671331)
                  ·
                    refine ⟨56071134450880254745006997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37380756300586836496671331 56071134450880254745006997)
                    ·
                      refine ⟨2628334427385011941172203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56071134450880254745006997 2628334427385011941172203)
                      ·
                        rfl

theorem cell23_5118663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_5118663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118663 prefixEnd_5118663 := by exact prefixLift 5118663
  have htrace : WordTrace (prefixWord ++ tailWord_5118663) baseStart_5118663 baseEnd_5118663 := by
    simpa [prefixWord, tailWord_5118663, baseEnd_5118663] using wordTrace_append hprefix tailTrace_5118663
  have hstable : (prefixWord ++ tailWord_5118663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118663).length < 2 ^ (prefixWord ++ tailWord_5118663).sum := by decide
  have hdescent : baseEnd_5118663 < baseStart_5118663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118684 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_5118684 : Nat := 118140960795 + 5118684 * 2 ^ 59
def prefixEnd_5118684 : Nat := 4983230072969 + 3 ^ 40 * 5118684 * 2
def baseEnd_5118684 : Nat := 2628345210478756359009607

theorem tailTrace_5118684 : CollatzResearch.WordTrace tailWord_5118684 prefixEnd_5118684 2628345210478756359009607 := by
  unfold tailWord_5118684
  simp only [CollatzResearch.WordTrace]
  refine ⟨93346871493944772236781553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124462495325259696315708737 93346871493944772236781553)
  ·
    refine ⟨70010153620458579177586165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93346871493944772236781553 70010153620458579177586165)
    ·
      refine ⟨6563451901917991797898703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70010153620458579177586165 6563451901917991797898703)
      ·
        refine ⟨9845177852876987696848055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6563451901917991797898703 9845177852876987696848055)
        ·
          refine ⟨14767766779315481545272083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9845177852876987696848055 14767766779315481545272083)
          ·
            refine ⟨22151650168973222317908125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14767766779315481545272083 22151650168973222317908125)
            ·
              refine ⟨8306868813364958369215547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22151650168973222317908125 8306868813364958369215547)
              ·
                refine ⟨12460303220047437553823321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8306868813364958369215547 12460303220047437553823321)
                ·
                  refine ⟨9345227415035578165367491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12460303220047437553823321 9345227415035578165367491)
                  ·
                    refine ⟨14017841122553367248051237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9345227415035578165367491 14017841122553367248051237)
                    ·
                      refine ⟨2628345210478756359009607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14017841122553367248051237 2628345210478756359009607)
                      ·
                        rfl

theorem cell23_5118684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_5118684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118684 prefixEnd_5118684 := by exact prefixLift 5118684
  have htrace : WordTrace (prefixWord ++ tailWord_5118684) baseStart_5118684 baseEnd_5118684 := by
    simpa [prefixWord, tailWord_5118684, baseEnd_5118684] using wordTrace_append hprefix tailTrace_5118684
  have hstable : (prefixWord ++ tailWord_5118684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118684).length < 2 ^ (prefixWord ++ tailWord_5118684).sum := by decide
  have hdescent : baseEnd_5118684 < baseStart_5118684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118687 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 3]
def baseStart_5118687 : Nat := 118140960795 + 5118687 * 2 ^ 59
def prefixEnd_5118687 : Nat := 4983230072969 + 3 ^ 40 * 5118687 * 2
def baseEnd_5118687 : Nat := 2628346750920719847272093

theorem tailTrace_5118687 : CollatzResearch.WordTrace tailWord_5118687 prefixEnd_5118687 2628346750920719847272093 := by
  unfold tailWord_5118687
  simp only [CollatzResearch.WordTrace]
  refine ⟨186693852406878675985922315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124462568271252450657281543 186693852406878675985922315)
  ·
    refine ⟨280040778610318013978883473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186693852406878675985922315 280040778610318013978883473)
    ·
      refine ⟨210030583957738510484162605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280040778610318013978883473 210030583957738510484162605)
      ·
        refine ⟨78761468984151941431560977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210030583957738510484162605 78761468984151941431560977)
        ·
          refine ⟨59071101738113956073670733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78761468984151941431560977 59071101738113956073670733)
          ·
            refine ⟨22151663151792733527626525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59071101738113956073670733 22151663151792733527626525)
            ·
              refine ⟨8306873681922275072859947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22151663151792733527626525 8306873681922275072859947)
              ·
                refine ⟨12460310522883412609289921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8306873681922275072859947 12460310522883412609289921)
                ·
                  refine ⟨9345232892162559456967441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12460310522883412609289921 9345232892162559456967441)
                  ·
                    refine ⟨7008924669121919592725581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9345232892162559456967441 7008924669121919592725581)
                    ·
                      refine ⟨2628346750920719847272093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7008924669121919592725581 2628346750920719847272093)
                      ·
                        rfl

theorem cell23_5118687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_5118687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118687 prefixEnd_5118687 := by exact prefixLift 5118687
  have htrace : WordTrace (prefixWord ++ tailWord_5118687) baseStart_5118687 baseEnd_5118687 := by
    simpa [prefixWord, tailWord_5118687, baseEnd_5118687] using wordTrace_append hprefix tailTrace_5118687
  have hstable : (prefixWord ++ tailWord_5118687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118687).length < 2 ^ (prefixWord ++ tailWord_5118687).sum := by decide
  have hdescent : baseEnd_5118687 < baseStart_5118687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118710 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_5118710 : Nat := 118140960795 + 5118710 * 2 ^ 59
def prefixEnd_5118710 : Nat := 4983230072969 + 3 ^ 40 * 5118710 * 2
def baseEnd_5118710 : Nat := 2628358560975773257284487

theorem tailTrace_5118710 : CollatzResearch.WordTrace tailWord_5118710 prefixEnd_5118710 2628358560975773257284487 := by
  unfold tailWord_5118710
  simp only [CollatzResearch.WordTrace]
  refine ⟨11668418205362209432125599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124463127523863567276006389 11668418205362209432125599)
  ·
    refine ⟨17502627308043314148188399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11668418205362209432125599 17502627308043314148188399)
    ·
      refine ⟨26253940962064971222282599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17502627308043314148188399 26253940962064971222282599)
      ·
        refine ⟨39380911443097456833423899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26253940962064971222282599 39380911443097456833423899)
        ·
          refine ⟨59071367164646185250135849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39380911443097456833423899 59071367164646185250135849)
          ·
            refine ⟨44303525373484638937601887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59071367164646185250135849 44303525373484638937601887)
            ·
              refine ⟨66455288060226958406402831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44303525373484638937601887 66455288060226958406402831)
              ·
                refine ⟨99682932090340437609604247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66455288060226958406402831 99682932090340437609604247)
                ·
                  refine ⟨149524398135510656414406371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99682932090340437609604247 149524398135510656414406371)
                  ·
                    refine ⟨224286597203265984621609557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 149524398135510656414406371 224286597203265984621609557)
                    ·
                      refine ⟨2628358560975773257284487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 224286597203265984621609557 2628358560975773257284487)
                      ·
                        rfl

theorem cell23_5118710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_5118710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118710 prefixEnd_5118710 := by exact prefixLift 5118710
  have htrace : WordTrace (prefixWord ++ tailWord_5118710) baseStart_5118710 baseEnd_5118710 := by
    simpa [prefixWord, tailWord_5118710, baseEnd_5118710] using wordTrace_append hprefix tailTrace_5118710
  have hstable : (prefixWord ++ tailWord_5118710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118710).length < 2 ^ (prefixWord ++ tailWord_5118710).sum := by decide
  have hdescent : baseEnd_5118710 < baseStart_5118710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118751 : List Nat := [1, 1, 2, 4, 2, 2, 3, 3, 1, 1, 3]
def baseStart_5118751 : Nat := 118140960795 + 5118751 * 2 ^ 59
def prefixEnd_5118751 : Nat := 4983230072969 + 3 ^ 40 * 5118751 * 2
def baseEnd_5118751 : Nat := 2628379613682607596871799

theorem tailTrace_5118751 : CollatzResearch.WordTrace tailWord_5118751 prefixEnd_5118751 2628379613682607596871799 := by
  unfold tailWord_5118751
  simp only [CollatzResearch.WordTrace]
  refine ⟨186696186678646814916252107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124464124452431209944168071 186696186678646814916252107)
  ·
    refine ⟨280044280017970222374378161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186696186678646814916252107 280044280017970222374378161)
    ·
      refine ⟨210033210013477666780783621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280044280017970222374378161 210033210013477666780783621)
      ·
        refine ⟨39381226877527062521396929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210033210013477666780783621 39381226877527062521396929)
        ·
          refine ⟨29535920158145296891047697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39381226877527062521396929 29535920158145296891047697)
          ·
            refine ⟨22151940118608972668285773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29535920158145296891047697 22151940118608972668285773)
            ·
              refine ⟨8306977544478364750607165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22151940118608972668285773 8306977544478364750607165)
              ·
                refine ⟨3115116579179386781477687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8306977544478364750607165 3115116579179386781477687)
                ·
                  refine ⟨4672674868769080172216531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115116579179386781477687 4672674868769080172216531)
                  ·
                    refine ⟨7009012303153620258324797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4672674868769080172216531 7009012303153620258324797)
                    ·
                      refine ⟨2628379613682607596871799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7009012303153620258324797 2628379613682607596871799)
                      ·
                        rfl

theorem cell23_5118751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_5118751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118751 prefixEnd_5118751 := by exact prefixLift 5118751
  have htrace : WordTrace (prefixWord ++ tailWord_5118751) baseStart_5118751 baseEnd_5118751 := by
    simpa [prefixWord, tailWord_5118751, baseEnd_5118751] using wordTrace_append hprefix tailTrace_5118751
  have hstable : (prefixWord ++ tailWord_5118751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118751).length < 2 ^ (prefixWord ++ tailWord_5118751).sum := by decide
  have hdescent : baseEnd_5118751 < baseStart_5118751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118757 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 4]
def baseStart_5118757 : Nat := 118140960795 + 5118757 * 2 ^ 59
def prefixEnd_5118757 : Nat := 4983230072969 + 3 ^ 40 * 5118757 * 2
def baseEnd_5118757 : Nat := 2628382694566534573396771

theorem tailTrace_5118757 : CollatzResearch.WordTrace tailWord_5118757 prefixEnd_5118757 2628382694566534573396771 := by
  unfold tailWord_5118757
  simp only [CollatzResearch.WordTrace]
  refine ⟨186696405516625077940970525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124464270344416718627313683 186696405516625077940970525)
  ·
    refine ⟨70011152068734404227863947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186696405516625077940970525 70011152068734404227863947)
    ·
      refine ⟨105016728103101606341795921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70011152068734404227863947 105016728103101606341795921)
      ·
        refine ⟨78762546077326204756346941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105016728103101606341795921 78762546077326204756346941)
        ·
          refine ⟨29535954778997326783630103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78762546077326204756346941 29535954778997326783630103)
          ·
            refine ⟨44303932168495990175445155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29535954778997326783630103 44303932168495990175445155)
            ·
              refine ⟨66455898252743985263167733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44303932168495990175445155 66455898252743985263167733)
              ·
                refine ⟨6230240461194748618421975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66455898252743985263167733 6230240461194748618421975)
                ·
                  refine ⟨9345360691792122927632963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6230240461194748618421975 9345360691792122927632963)
                  ·
                    refine ⟨14018041037688184391449445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9345360691792122927632963 14018041037688184391449445)
                    ·
                      refine ⟨2628382694566534573396771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14018041037688184391449445 2628382694566534573396771)
                      ·
                        rfl

theorem cell23_5118757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_5118757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118757 prefixEnd_5118757 := by exact prefixLift 5118757
  have htrace : WordTrace (prefixWord ++ tailWord_5118757) baseStart_5118757 baseEnd_5118757 := by
    simpa [prefixWord, tailWord_5118757, baseEnd_5118757] using wordTrace_append hprefix tailTrace_5118757
  have hstable : (prefixWord ++ tailWord_5118757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118757).length < 2 ^ (prefixWord ++ tailWord_5118757).sum := by decide
  have hdescent : baseEnd_5118757 < baseStart_5118757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118770 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_5118770 : Nat := 118140960795 + 5118770 * 2 ^ 59
def prefixEnd_5118770 : Nat := 4983230072969 + 3 ^ 40 * 5118770 * 2
def baseEnd_5118770 : Nat := 2628389369815043022534211

theorem tailTrace_5118770 : CollatzResearch.WordTrace tailWord_5118770 prefixEnd_5118770 2628389369815043022534211 := by
  unfold tailWord_5118770
  simp only [CollatzResearch.WordTrace]
  refine ⟨46674219916394495290298441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124464586443718654107462509 46674219916394495290298441)
  ·
    refine ⟨35005664937295871467723831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46674219916394495290298441 35005664937295871467723831)
    ·
      refine ⟨52508497405943807201585747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35005664937295871467723831 52508497405943807201585747)
      ·
        refine ⟨78762746108915710802378621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52508497405943807201585747 78762746108915710802378621)
        ·
          refine ⟨29536029790843391550891983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78762746108915710802378621 29536029790843391550891983)
          ·
            refine ⟨44304044686265087326337975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29536029790843391550891983 44304044686265087326337975)
            ·
              refine ⟨66456067029397630989506963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44304044686265087326337975 66456067029397630989506963)
              ·
                refine ⟨99684100544096446484260445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66456067029397630989506963 99684100544096446484260445)
                ·
                  refine ⟨37381537704036167431597667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99684100544096446484260445 37381537704036167431597667)
                  ·
                    refine ⟨56072306556054251147396501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37381537704036167431597667 56072306556054251147396501)
                    ·
                      refine ⟨2628389369815043022534211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56072306556054251147396501 2628389369815043022534211)
                      ·
                        rfl

theorem cell23_5118770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_5118770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118770 prefixEnd_5118770 := by exact prefixLift 5118770
  have htrace : WordTrace (prefixWord ++ tailWord_5118770) baseStart_5118770 baseEnd_5118770 := by
    simpa [prefixWord, tailWord_5118770, baseEnd_5118770] using wordTrace_append hprefix tailTrace_5118770
  have hstable : (prefixWord ++ tailWord_5118770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118770).length < 2 ^ (prefixWord ++ tailWord_5118770).sum := by decide
  have hdescent : baseEnd_5118770 < baseStart_5118770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118788 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_5118788 : Nat := 118140960795 + 5118788 * 2 ^ 59
def prefixEnd_5118788 : Nat := 4983230072969 + 3 ^ 40 * 5118788 * 2
def baseEnd_5118788 : Nat := 876132870822274650703043

theorem tailTrace_5118788 : CollatzResearch.WordTrace tailWord_5118788 prefixEnd_5118788 876132870822274650703043 := by
  unfold tailWord_5118788
  simp only [CollatzResearch.WordTrace]
  refine ⟨93348768089756385117674509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124465024119675180156899345 93348768089756385117674509)
  ·
    refine ⟨35005788033658644419127941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93348768089756385117674509 35005788033658644419127941)
    ·
      refine ⟨6563585256310995828586489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35005788033658644419127941 6563585256310995828586489)
      ·
        refine ⟨4922688942233246871439867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6563585256310995828586489 4922688942233246871439867)
        ·
          refine ⟨7384033413349870307159801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4922688942233246871439867 7384033413349870307159801)
          ·
            refine ⟨5538025060012402730369851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7384033413349870307159801 5538025060012402730369851)
            ·
              refine ⟨8307037590018604095554777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538025060012402730369851 8307037590018604095554777)
              ·
                refine ⟨6230278192513953071666083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8307037590018604095554777 6230278192513953071666083)
                ·
                  refine ⟨9345417288770929607499125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6230278192513953071666083 9345417288770929607499125)
                  ·
                    refine ⟨876132870822274650703043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9345417288770929607499125 876132870822274650703043)
                    ·
                      rfl

theorem cell23_5118788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_5118788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118788 prefixEnd_5118788 := by exact prefixLift 5118788
  have htrace : WordTrace (prefixWord ++ tailWord_5118788) baseStart_5118788 baseEnd_5118788 := by
    simpa [prefixWord, tailWord_5118788, baseEnd_5118788] using wordTrace_append hprefix tailTrace_5118788
  have hstable : (prefixWord ++ tailWord_5118788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118788).length < 2 ^ (prefixWord ++ tailWord_5118788).sum := by decide
  have hdescent : baseEnd_5118788 < baseStart_5118788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118804 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_5118804 : Nat := 118140960795 + 5118804 * 2 ^ 59
def prefixEnd_5118804 : Nat := 4983230072969 + 3 ^ 40 * 5118804 * 2
def baseEnd_5118804 : Nat := 2628406828157295889509055

theorem tailTrace_5118804 : CollatzResearch.WordTrace tailWord_5118804 prefixEnd_5118804 2628406828157295889509055 := by
  unfold tailWord_5118804
  simp only [CollatzResearch.WordTrace]
  refine ⟨93349059873727402483965733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124465413164969869978620977 93349059873727402483965733)
  ·
    refine ⟨17502948726323887965743575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93349059873727402483965733 17502948726323887965743575)
    ·
      refine ⟨26254423089485831948615363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17502948726323887965743575 26254423089485831948615363)
      ·
        refine ⟨39381634634228747922923045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26254423089485831948615363 39381634634228747922923045)
        ·
          refine ⟨7384056493917890235548071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39381634634228747922923045 7384056493917890235548071)
          ·
            refine ⟨11076084740876835353322107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7384056493917890235548071 11076084740876835353322107)
            ·
              refine ⟨16614127111315253029983161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11076084740876835353322107 16614127111315253029983161)
              ·
                refine ⟨12460595333486439772487371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16614127111315253029983161 12460595333486439772487371)
                ·
                  refine ⟨18690893000229659658731057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12460595333486439772487371 18690893000229659658731057)
                  ·
                    refine ⟨14018169750172244744048293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18690893000229659658731057 14018169750172244744048293)
                    ·
                      refine ⟨2628406828157295889509055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14018169750172244744048293 2628406828157295889509055)
                      ·
                        rfl

theorem cell23_5118804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_5118804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118804 prefixEnd_5118804 := by exact prefixLift 5118804
  have htrace : WordTrace (prefixWord ++ tailWord_5118804) baseStart_5118804 baseEnd_5118804 := by
    simpa [prefixWord, tailWord_5118804, baseEnd_5118804] using wordTrace_append hprefix tailTrace_5118804
  have hstable : (prefixWord ++ tailWord_5118804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118804).length < 2 ^ (prefixWord ++ tailWord_5118804).sum := by decide
  have hdescent : baseEnd_5118804 < baseStart_5118804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118807 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 3]
def baseStart_5118807 : Nat := 118140960795 + 5118807 * 2 ^ 59
def prefixEnd_5118807 : Nat := 4983230072969 + 3 ^ 40 * 5118807 * 2
def baseEnd_5118807 : Nat := 2628408368599259377771541

theorem tailTrace_5118807 : CollatzResearch.WordTrace tailWord_5118807 prefixEnd_5118807 2628408368599259377771541 := by
  unfold tailWord_5118807
  simp only [CollatzResearch.WordTrace]
  refine ⟨186698229166443936480290675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124465486110962624320193783 186698229166443936480290675)
  ·
    refine ⟨280047343749665904720436013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186698229166443936480290675 280047343749665904720436013)
    ·
      refine ⟨105017753906124714270163505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280047343749665904720436013 105017753906124714270163505)
      ·
        refine ⟨78763315429593535702622629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105017753906124714270163505 78763315429593535702622629)
        ·
          refine ⟨14768121643048787944241743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78763315429593535702622629 14768121643048787944241743)
          ·
            refine ⟨22152182464573181916362615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14768121643048787944241743 22152182464573181916362615)
            ·
              refine ⟨33228273696859772874543923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22152182464573181916362615 33228273696859772874543923)
              ·
                refine ⟨49842410545289659311815885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33228273696859772874543923 49842410545289659311815885)
                ·
                  refine ⟨18690903954483622241930957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49842410545289659311815885 18690903954483622241930957)
                  ·
                    refine ⟨7009088982931358340724109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18690903954483622241930957 7009088982931358340724109)
                    ·
                      refine ⟨2628408368599259377771541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7009088982931358340724109 2628408368599259377771541)
                      ·
                        rfl

theorem cell23_5118807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_5118807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118807 prefixEnd_5118807 := by exact prefixLift 5118807
  have htrace : WordTrace (prefixWord ++ tailWord_5118807) baseStart_5118807 baseEnd_5118807 := by
    simpa [prefixWord, tailWord_5118807, baseEnd_5118807] using wordTrace_append hprefix tailTrace_5118807
  have hstable : (prefixWord ++ tailWord_5118807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118807).length < 2 ^ (prefixWord ++ tailWord_5118807).sum := by decide
  have hdescent : baseEnd_5118807 < baseStart_5118807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118834 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 3, 3, 2]
def baseStart_5118834 : Nat := 118140960795 + 5118834 * 2 ^ 59
def prefixEnd_5118834 : Nat := 4983230072969 + 3 ^ 40 * 5118834 * 2
def baseEnd_5118834 : Nat := 2628422232576930772133917

theorem tailTrace_5118834 : CollatzResearch.WordTrace tailWord_5118834 prefixEnd_5118834 2628422232576930772133917 := by
  unfold tailWord_5118834
  simp only [CollatzResearch.WordTrace]
  refine ⟨46674803484336530022880889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124466142624897413394349037 46674803484336530022880889)
  ·
    refine ⟨35006102613252397517160667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46674803484336530022880889 35006102613252397517160667)
    ·
      refine ⟨52509153919878596275741001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35006102613252397517160667 52509153919878596275741001)
      ·
        refine ⟨39381865439908947206805751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52509153919878596275741001 39381865439908947206805751)
        ·
          refine ⟨59072798159863420810208627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39381865439908947206805751 59072798159863420810208627)
          ·
            refine ⟨88609197239795131215312941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59072798159863420810208627 88609197239795131215312941)
            ·
              refine ⟨33228448964923174205742353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88609197239795131215312941 33228448964923174205742353)
              ·
                refine ⟨24921336723692380654306765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33228448964923174205742353 24921336723692380654306765)
                ·
                  refine ⟨9345501271384642745365037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24921336723692380654306765 9345501271384642745365037)
                  ·
                    refine ⟨3504562976769241029511889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9345501271384642745365037 3504562976769241029511889)
                    ·
                      refine ⟨2628422232576930772133917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504562976769241029511889 2628422232576930772133917)
                      ·
                        rfl

theorem cell23_5118834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_5118834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118834 prefixEnd_5118834 := by exact prefixLift 5118834
  have htrace : WordTrace (prefixWord ++ tailWord_5118834) baseStart_5118834 baseEnd_5118834 := by
    simpa [prefixWord, tailWord_5118834, baseEnd_5118834] using wordTrace_append hprefix tailTrace_5118834
  have hstable : (prefixWord ++ tailWord_5118834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118834).length < 2 ^ (prefixWord ++ tailWord_5118834).sum := by decide
  have hdescent : baseEnd_5118834 < baseStart_5118834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118877 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_5118877 : Nat := 118140960795 + 5118877 * 2 ^ 59
def prefixEnd_5118877 : Nat := 4983230072969 + 3 ^ 40 * 5118877 * 2
def baseEnd_5118877 : Nat := 2628444312245074103896219

theorem tailTrace_5118877 : CollatzResearch.WordTrace tailWord_5118877 prefixEnd_5118877 2628444312245074103896219 := by
  unfold tailWord_5118877
  simp only [CollatzResearch.WordTrace]
  refine ⟨186700782276190338435338885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124467188184126892290225923 186700782276190338435338885)
  ·
    refine ⟨35006396676785688456626041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186700782276190338435338885 35006396676785688456626041)
    ·
      refine ⟨26254797507589266342469531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35006396676785688456626041 26254797507589266342469531)
      ·
        refine ⟨39382196261383899513704297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26254797507589266342469531 39382196261383899513704297)
        ·
          refine ⟨29536647196037924635278223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39382196261383899513704297 29536647196037924635278223)
          ·
            refine ⟨44304970794056886952917335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29536647196037924635278223 44304970794056886952917335)
            ·
              refine ⟨66457456191085330429376003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44304970794056886952917335 66457456191085330429376003)
              ·
                refine ⟨99686184286627995644064005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66457456191085330429376003 99686184286627995644064005)
                ·
                  refine ⟨18691159553742749183262001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99686184286627995644064005 18691159553742749183262001)
                  ·
                    refine ⟨14018369665307061887446501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18691159553742749183262001 14018369665307061887446501)
                    ·
                      refine ⟨2628444312245074103896219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14018369665307061887446501 2628444312245074103896219)
                      ·
                        rfl

theorem cell23_5118877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_5118877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118877 prefixEnd_5118877 := by exact prefixLift 5118877
  have htrace : WordTrace (prefixWord ++ tailWord_5118877) baseStart_5118877 baseEnd_5118877 := by
    simpa [prefixWord, tailWord_5118877, baseEnd_5118877] using wordTrace_append hprefix tailTrace_5118877
  have hstable : (prefixWord ++ tailWord_5118877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118877).length < 2 ^ (prefixWord ++ tailWord_5118877).sum := by decide
  have hdescent : baseEnd_5118877 < baseStart_5118877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118949 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 2, 2, 2]
def baseStart_5118949 : Nat := 118140960795 + 5118949 * 2 ^ 59
def prefixEnd_5118949 : Nat := 4983230072969 + 3 ^ 40 * 5118949 * 2
def baseEnd_5118949 : Nat := 2628481282852197822195889

theorem tailTrace_5118949 : CollatzResearch.WordTrace tailWord_5118949 prefixEnd_5118949 2628481282852197822195889 := by
  unfold tailWord_5118949
  simp only [CollatzResearch.WordTrace]
  refine ⟨186703408331929494731959901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124468938887952996487973267 186703408331929494731959901)
  ·
    refine ⟨70013778124473560524484963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186703408331929494731959901 70013778124473560524484963)
    ·
      refine ⟨105020667186710340786727445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70013778124473560524484963 105020667186710340786727445)
      ·
        refine ⟨4922843774377047224377849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105020667186710340786727445 4922843774377047224377849)
        ·
          refine ⟨3692132830782785418283387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4922843774377047224377849 3692132830782785418283387)
          ·
            refine ⟨5538199246174178127425081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692132830782785418283387 5538199246174178127425081)
            ·
              refine ⟨4153649434630633595568811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5538199246174178127425081 4153649434630633595568811)
              ·
                refine ⟨6230474151945950393353217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4153649434630633595568811 6230474151945950393353217)
                ·
                  refine ⟨4672855613959462795014913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6230474151945950393353217 4672855613959462795014913)
                  ·
                    refine ⟨3504641710469597096261185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4672855613959462795014913 3504641710469597096261185)
                    ·
                      refine ⟨2628481282852197822195889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504641710469597096261185 2628481282852197822195889)
                      ·
                        rfl

theorem cell23_5118949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_5118949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118949 prefixEnd_5118949 := by exact prefixLift 5118949
  have htrace : WordTrace (prefixWord ++ tailWord_5118949) baseStart_5118949 baseEnd_5118949 := by
    simpa [prefixWord, tailWord_5118949, baseEnd_5118949] using wordTrace_append hprefix tailTrace_5118949
  have hstable : (prefixWord ++ tailWord_5118949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118949).length < 2 ^ (prefixWord ++ tailWord_5118949).sum := by decide
  have hdescent : baseEnd_5118949 < baseStart_5118949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5118981 : List Nat := [1, 3, 1, 1, 2, 3, 2, 5, 1, 4]
def baseStart_5118981 : Nat := 118140960795 + 5118981 * 2 ^ 59
def prefixEnd_5118981 : Nat := 4983230072969 + 3 ^ 40 * 5118981 * 2
def baseEnd_5118981 : Nat := 876165904744380565665247

theorem tailTrace_5118981 : CollatzResearch.WordTrace tailWord_5118981 prefixEnd_5118981 876165904744380565665247 := by
  unfold tailWord_5118981
  simp only [CollatzResearch.WordTrace]
  refine ⟨186704575467813564197124797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124469716978542376131416531 186704575467813564197124797)
  ·
    refine ⟨70014215800430086573921799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186704575467813564197124797 70014215800430086573921799)
    ·
      refine ⟨105021323700645129860882699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70014215800430086573921799 105021323700645129860882699)
      ·
        refine ⟨157531985550967694791324049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105021323700645129860882699 157531985550967694791324049)
        ·
          refine ⟨118148989163225771093493037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157531985550967694791324049 118148989163225771093493037)
          ·
            refine ⟨44305870936209664160059889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118148989163225771093493037 44305870936209664160059889)
            ·
              refine ⟨33229403202157248120044917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44305870936209664160059889 33229403202157248120044917)
              ·
                refine ⟨3115256550202242011254211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33229403202157248120044917 3115256550202242011254211)
                ·
                  refine ⟨4672884825303363016881317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115256550202242011254211 4672884825303363016881317)
                  ·
                    refine ⟨876165904744380565665247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4672884825303363016881317 876165904744380565665247)
                    ·
                      rfl

theorem cell23_5118981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_5118981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5118981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5118981 prefixEnd_5118981 := by exact prefixLift 5118981
  have htrace : WordTrace (prefixWord ++ tailWord_5118981) baseStart_5118981 baseEnd_5118981 := by
    simpa [prefixWord, tailWord_5118981, baseEnd_5118981] using wordTrace_append hprefix tailTrace_5118981
  have hstable : (prefixWord ++ tailWord_5118981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5118981).length < 2 ^ (prefixWord ++ tailWord_5118981).sum := by decide
  have hdescent : baseEnd_5118981 < baseStart_5118981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5118981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119024 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 1, 5]
def baseStart_5119024 : Nat := 118140960795 + 5119024 * 2 ^ 59
def prefixEnd_5119024 : Nat := 4983230072969 + 3 ^ 40 * 5119024 * 2
def baseEnd_5119024 : Nat := 876173264633761676252681

theorem tailTrace_5119024 : CollatzResearch.WordTrace tailWord_5119024 prefixEnd_5119024 876173264633761676252681 := by
  unfold tailWord_5119024
  simp only [CollatzResearch.WordTrace]
  refine ⟨93353071903328891270470063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124470762537771855027293417 93353071903328891270470063)
  ·
    refine ⟨140029607854993336905705095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93353071903328891270470063 140029607854993336905705095)
    ·
      refine ⟨210044411782490005358557643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140029607854993336905705095 210044411782490005358557643)
      ·
        refine ⟨315066617673735008037836465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210044411782490005358557643 315066617673735008037836465)
        ·
          refine ⟨236299963255301256028377349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315066617673735008037836465 236299963255301256028377349)
          ·
            refine ⟨44306243110368985505320753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 236299963255301256028377349 44306243110368985505320753)
            ·
              refine ⟨33229682332776739128990565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44306243110368985505320753 33229682332776739128990565)
              ·
                refine ⟨6230565437395638586685731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33229682332776739128990565 6230565437395638586685731)
                ·
                  refine ⟨9345848156093457880028597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6230565437395638586685731 9345848156093457880028597)
                  ·
                    refine ⟨876173264633761676252681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9345848156093457880028597 876173264633761676252681)
                    ·
                      rfl

theorem cell23_5119024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 5].length) (baseStart_5119024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119024 prefixEnd_5119024 := by exact prefixLift 5119024
  have htrace : WordTrace (prefixWord ++ tailWord_5119024) baseStart_5119024 baseEnd_5119024 := by
    simpa [prefixWord, tailWord_5119024, baseEnd_5119024] using wordTrace_append hprefix tailTrace_5119024
  have hstable : (prefixWord ++ tailWord_5119024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119024).length < 2 ^ (prefixWord ++ tailWord_5119024).sum := by decide
  have hdescent : baseEnd_5119024 < baseStart_5119024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119064 : List Nat := [2, 1, 2, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_5119064 : Nat := 118140960795 + 5119064 * 2 ^ 59
def prefixEnd_5119064 : Nat := 4983230072969 + 3 ^ 40 * 5119064 * 2
def baseEnd_5119064 : Nat := 2628540333127464872257859

theorem tailTrace_5119064 : CollatzResearch.WordTrace tailWord_5119064 prefixEnd_5119064 2628540333127464872257859 := by
  unfold tailWord_5119064
  simp only [CollatzResearch.WordTrace]
  refine ⟨93353801363256434686198123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124471735151008579581597497 93353801363256434686198123)
  ·
    refine ⟨140030702044884652029297185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93353801363256434686198123 140030702044884652029297185)
    ·
      refine ⟨105023026533663489021972889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140030702044884652029297185 105023026533663489021972889)
      ·
        refine ⟨78767269900247616766479667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105023026533663489021972889 78767269900247616766479667)
        ·
          refine ⟨118150904850371425149719501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78767269900247616766479667 118150904850371425149719501)
          ·
            refine ⟨44306589318889284431144813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118150904850371425149719501 44306589318889284431144813)
            ·
              refine ⟨16614970994583481661679305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44306589318889284431144813 16614970994583481661679305)
              ·
                refine ⟨12461228245937611246259479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16614970994583481661679305 12461228245937611246259479)
                ·
                  refine ⟨18691842368906416869389219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12461228245937611246259479 18691842368906416869389219)
                  ·
                    refine ⟨28037763553359625304083829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18691842368906416869389219 28037763553359625304083829)
                    ·
                      refine ⟨2628540333127464872257859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28037763553359625304083829 2628540333127464872257859)
                      ·
                        rfl

theorem cell23_5119064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_5119064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119064 prefixEnd_5119064 := by exact prefixLift 5119064
  have htrace : WordTrace (prefixWord ++ tailWord_5119064) baseStart_5119064 baseEnd_5119064 := by
    simpa [prefixWord, tailWord_5119064, baseEnd_5119064] using wordTrace_append hprefix tailTrace_5119064
  have hstable : (prefixWord ++ tailWord_5119064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119064).length < 2 ^ (prefixWord ++ tailWord_5119064).sum := by decide
  have hdescent : baseEnd_5119064 < baseStart_5119064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119081 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 1, 2, 3]
def baseStart_5119081 : Nat := 118140960795 + 5119081 * 2 ^ 59
def prefixEnd_5119081 : Nat := 4983230072969 + 3 ^ 40 * 5119081 * 2
def baseEnd_5119081 : Nat := 2628549062298591305745281

theorem tailTrace_5119081 : CollatzResearch.WordTrace tailWord_5119081 prefixEnd_5119081 2628549062298591305745281 := by
  unfold tailWord_5119081
  simp only [CollatzResearch.WordTrace]
  refine ⟨186708222767451281275765097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124472148511634187517176731 186708222767451281275765097)
  ·
    refine ⟨140031167075588460956823823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186708222767451281275765097 140031167075588460956823823)
    ·
      refine ⟨210046750613382691435235735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140031167075588460956823823 210046750613382691435235735)
      ·
        refine ⟨315070125920074037152853603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210046750613382691435235735 315070125920074037152853603)
        ·
          refine ⟨472605188880111055729280405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315070125920074037152853603 472605188880111055729280405)
          ·
            refine ⟨22153368228755205737310019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 472605188880111055729280405 22153368228755205737310019)
            ·
              refine ⟨33230052343132808605965029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22153368228755205737310019 33230052343132808605965029)
              ·
                refine ⟨6230634814337401613618443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33230052343132808605965029 6230634814337401613618443)
                ·
                  refine ⟨9345952221506102420427665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6230634814337401613618443 9345952221506102420427665)
                  ·
                    refine ⟨7009464166129576815320749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9345952221506102420427665 7009464166129576815320749)
                    ·
                      refine ⟨2628549062298591305745281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7009464166129576815320749 2628549062298591305745281)
                      ·
                        rfl

theorem cell23_5119081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 2, 3].length) (baseStart_5119081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119081 prefixEnd_5119081 := by exact prefixLift 5119081
  have htrace : WordTrace (prefixWord ++ tailWord_5119081) baseStart_5119081 baseEnd_5119081 := by
    simpa [prefixWord, tailWord_5119081, baseEnd_5119081] using wordTrace_append hprefix tailTrace_5119081
  have hstable : (prefixWord ++ tailWord_5119081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119081).length < 2 ^ (prefixWord ++ tailWord_5119081).sum := by decide
  have hdescent : baseEnd_5119081 < baseStart_5119081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119112 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 3, 2, 2]
def baseStart_5119112 : Nat := 118140960795 + 5119112 * 2 ^ 59
def prefixEnd_5119112 : Nat := 4983230072969 + 3 ^ 40 * 5119112 * 2
def baseEnd_5119112 : Nat := 2628564980198880684457639

theorem tailTrace_5119112 : CollatzResearch.WordTrace tailWord_5119112 prefixEnd_5119112 2628564980198880684457639 := by
  unfold tailWord_5119112
  simp only [CollatzResearch.WordTrace]
  refine ⟨93354676715169486785071795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124472902286892649046762393 93354676715169486785071795)
  ·
    refine ⟨140032015072754230177607693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93354676715169486785071795 140032015072754230177607693)
    ·
      refine ⟨52512005652282836316602885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140032015072754230177607693 52512005652282836316602885)
      ·
        refine ⟨9846001059803031809363041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52512005652282836316602885 9846001059803031809363041)
        ·
          refine ⟨7384500794852273857022281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9846001059803031809363041 7384500794852273857022281)
          ·
            refine ⟨5538375596139205392766711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7384500794852273857022281 5538375596139205392766711)
            ·
              refine ⟨8307563394208808089150067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538375596139205392766711 8307563394208808089150067)
              ·
                refine ⟨12461345091313212133725101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8307563394208808089150067 12461345091313212133725101)
                ·
                  refine ⟨4673004409242454550146913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12461345091313212133725101 4673004409242454550146913)
                  ·
                    refine ⟨3504753306931840912610185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4673004409242454550146913 3504753306931840912610185)
                    ·
                      refine ⟨2628564980198880684457639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504753306931840912610185 2628564980198880684457639)
                      ·
                        rfl

theorem cell23_5119112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_5119112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119112 prefixEnd_5119112 := by exact prefixLift 5119112
  have htrace : WordTrace (prefixWord ++ tailWord_5119112) baseStart_5119112 baseEnd_5119112 := by
    simpa [prefixWord, tailWord_5119112, baseEnd_5119112] using wordTrace_append hprefix tailTrace_5119112
  have hstable : (prefixWord ++ tailWord_5119112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119112).length < 2 ^ (prefixWord ++ tailWord_5119112).sum := by decide
  have hdescent : baseEnd_5119112 < baseStart_5119112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119114 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_5119114 : Nat := 118140960795 + 5119114 * 2 ^ 59
def prefixEnd_5119114 : Nat := 4983230072969 + 3 ^ 40 * 5119114 * 2
def baseEnd_5119114 : Nat := 876188669053396558877543

theorem tailTrace_5119114 : CollatzResearch.WordTrace tailWord_5119114 prefixEnd_5119114 876188669053396558877543 := by
  unfold tailWord_5119114
  simp only [CollatzResearch.WordTrace]
  refine ⟨46677356594082931977929099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124472950917554485274477597 46677356594082931977929099)
  ·
    refine ⟨70016034891124397966893649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46677356594082931977929099 70016034891124397966893649)
    ·
      refine ⟨52512026168343298475170237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70016034891124397966893649 52512026168343298475170237)
      ·
        refine ⟨19692009813128736928188839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52512026168343298475170237 19692009813128736928188839)
        ·
          refine ⟨29538014719693105392283259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19692009813128736928188839 29538014719693105392283259)
          ·
            refine ⟨44307022079539658088424889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29538014719693105392283259 44307022079539658088424889)
            ·
              refine ⟨33230266559654743566318667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44307022079539658088424889 33230266559654743566318667)
              ·
                refine ⟨49845399839482115349478001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33230266559654743566318667 49845399839482115349478001)
                ·
                  refine ⟨37384049879611586512108501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49845399839482115349478001 37384049879611586512108501)
                  ·
                    refine ⟨876188669053396558877543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37384049879611586512108501 876188669053396558877543)
                    ·
                      rfl

theorem cell23_5119114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_5119114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119114 prefixEnd_5119114 := by exact prefixLift 5119114
  have htrace : WordTrace (prefixWord ++ tailWord_5119114) baseStart_5119114 baseEnd_5119114 := by
    simpa [prefixWord, tailWord_5119114, baseEnd_5119114] using wordTrace_append hprefix tailTrace_5119114
  have hstable : (prefixWord ++ tailWord_5119114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119114).length < 2 ^ (prefixWord ++ tailWord_5119114).sum := by decide
  have hdescent : baseEnd_5119114 < baseStart_5119114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119151 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 3, 4, 2]
def baseStart_5119151 : Nat := 118140960795 + 5119151 * 2 ^ 59
def prefixEnd_5119151 : Nat := 4983230072969 + 3 ^ 40 * 5119151 * 2
def baseEnd_5119151 : Nat := 2628585005944406031869959

theorem tailTrace_5119151 : CollatzResearch.WordTrace tailWord_5119151 prefixEnd_5119151 2628585005944406031869959 := by
  unfold tailWord_5119151
  simp only [CollatzResearch.WordTrace]
  refine ⟨186710775877197683230813307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124473850584798455487208871 186710775877197683230813307)
  ·
    refine ⟨280066163815796524846219961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186710775877197683230813307 280066163815796524846219961)
    ·
      refine ⟨210049622861847393634664971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280066163815796524846219961 210049622861847393634664971)
      ·
        refine ⟨315074434292771090451997457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210049622861847393634664971 315074434292771090451997457)
        ·
          refine ⟨236305825719578317838998093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315074434292771090451997457 236305825719578317838998093)
          ·
            refine ⟨88614684644841869189624285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236305825719578317838998093 88614684644841869189624285)
            ·
              refine ⟨33230506741815700946109107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88614684644841869189624285 33230506741815700946109107)
              ·
                refine ⟨49845760112723551419163661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33230506741815700946109107 49845760112723551419163661)
                ·
                  refine ⟨18692160042271331782186373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49845760112723551419163661 18692160042271331782186373)
                  ·
                    refine ⟨3504780007925874709159945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18692160042271331782186373 3504780007925874709159945)
                    ·
                      refine ⟨2628585005944406031869959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504780007925874709159945 2628585005944406031869959)
                      ·
                        rfl

theorem cell23_5119151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 4, 2].length) (baseStart_5119151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119151 prefixEnd_5119151 := by exact prefixLift 5119151
  have htrace : WordTrace (prefixWord ++ tailWord_5119151) baseStart_5119151 baseEnd_5119151 := by
    simpa [prefixWord, tailWord_5119151, baseEnd_5119151] using wordTrace_append hprefix tailTrace_5119151
  have hstable : (prefixWord ++ tailWord_5119151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119151).length < 2 ^ (prefixWord ++ tailWord_5119151).sum := by decide
  have hdescent : baseEnd_5119151 < baseStart_5119151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119208 : List Nat := [2, 1, 4, 1, 2, 1, 4, 3, 5]
def baseStart_5119208 : Nat := 118140960795 + 5119208 * 2 ^ 59
def prefixEnd_5119208 : Nat := 4983230072969 + 3 ^ 40 * 5119208 * 2
def baseEnd_5119208 : Nat := 292068252704634700984133

theorem tailTrace_5119208 : CollatzResearch.WordTrace tailWord_5119208 prefixEnd_5119208 292068252704634700984133 := by
  unfold tailWord_5119208
  simp only [CollatzResearch.WordTrace]
  refine ⟨93356427418995590982819139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124475236558660787977092185 93356427418995590982819139)
  ·
    refine ⟨140034641128493386474228709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93356427418995590982819139 140034641128493386474228709)
    ·
      refine ⟨26256495211592509963917883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140034641128493386474228709 26256495211592509963917883)
      ·
        refine ⟨39384742817388764945876825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26256495211592509963917883 39384742817388764945876825)
        ·
          refine ⟨29538557113041573709407619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39384742817388764945876825 29538557113041573709407619)
          ·
            refine ⟨44307835669562360564111429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29538557113041573709407619 44307835669562360564111429)
            ·
              refine ⟨8307719188042942605770893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44307835669562360564111429 8307719188042942605770893)
              ·
                refine ⟨3115394695516103477164085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8307719188042942605770893 3115394695516103477164085)
                ·
                  refine ⟨292068252704634700984133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3115394695516103477164085 292068252704634700984133)
                  ·
                    rfl

theorem cell23_5119208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 5].length) (baseStart_5119208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119208 prefixEnd_5119208 := by exact prefixLift 5119208
  have htrace : WordTrace (prefixWord ++ tailWord_5119208) baseStart_5119208 baseEnd_5119208 := by
    simpa [prefixWord, tailWord_5119208, baseEnd_5119208] using wordTrace_append hprefix tailTrace_5119208
  have hstable : (prefixWord ++ tailWord_5119208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119208).length < 2 ^ (prefixWord ++ tailWord_5119208).sum := by decide
  have hdescent : baseEnd_5119208 < baseStart_5119208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119281 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 8]
def baseStart_5119281 : Nat := 118140960795 + 5119281 * 2 ^ 59
def prefixEnd_5119281 : Nat := 4983230072969 + 3 ^ 40 * 5119281 * 2
def baseEnd_5119281 : Nat := 292072417603276724804929

theorem tailTrace_5119281 : CollatzResearch.WordTrace tailWord_5119281 prefixEnd_5119281 292072417603276724804929 := by
  unfold tailWord_5119281
  simp only [CollatzResearch.WordTrace]
  refine ⟨186715517366726715433045697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124477011577817810288697131 186715517366726715433045697)
  ·
    refine ⟨140036638025045036574784273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186715517366726715433045697 140036638025045036574784273)
    ·
      refine ⟨105027478518783777431088205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140036638025045036574784273 105027478518783777431088205)
      ·
        refine ⟨39385304444543916536658077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105027478518783777431088205 39385304444543916536658077)
        ·
          refine ⟨14769489166703968701246779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39385304444543916536658077 14769489166703968701246779)
          ·
            refine ⟨22154233750055953051870169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14769489166703968701246779 22154233750055953051870169)
            ·
              refine ⟨16615675312541964788902627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22154233750055953051870169 16615675312541964788902627)
              ·
                refine ⟨24923512968812947183353941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16615675312541964788902627 24923512968812947183353941)
                ·
                  refine ⟨292072417603276724804929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24923512968812947183353941 292072417603276724804929)
                  ·
                    rfl

theorem cell23_5119281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 8].length) (baseStart_5119281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119281 prefixEnd_5119281 := by exact prefixLift 5119281
  have htrace : WordTrace (prefixWord ++ tailWord_5119281) baseStart_5119281 baseEnd_5119281 := by
    simpa [prefixWord, tailWord_5119281, baseEnd_5119281] using wordTrace_append hprefix tailTrace_5119281
  have hstable : (prefixWord ++ tailWord_5119281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119281).length < 2 ^ (prefixWord ++ tailWord_5119281).sum := by decide
  have hdescent : baseEnd_5119281 < baseStart_5119281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119285 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 3, 4]
def baseStart_5119285 : Nat := 118140960795 + 5119285 * 2 ^ 59
def prefixEnd_5119285 : Nat := 4983230072969 + 3 ^ 40 * 5119285 * 2
def baseEnd_5119285 : Nat := 876217937450702835864781

theorem tailTrace_5119285 : CollatzResearch.WordTrace tailWord_5119285 prefixEnd_5119285 876217937450702835864781 := by
  unfold tailWord_5119285
  simp only [CollatzResearch.WordTrace]
  refine ⟨186715663258712224116191309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124477108839141482744127539 186715663258712224116191309)
  ·
    refine ⟨70018373722017084043571741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186715663258712224116191309 70018373722017084043571741)
    ·
      refine ⟨26256890145756406516339403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70018373722017084043571741 26256890145756406516339403)
      ·
        refine ⟨39385335218634609774509105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26256890145756406516339403 39385335218634609774509105)
        ·
          refine ⟨29539001413975957330881829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39385335218634609774509105 29539001413975957330881829)
          ·
            refine ⟨5538562765120491999540343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29539001413975957330881829 5538562765120491999540343)
            ·
              refine ⟨8307844147680737999310515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538562765120491999540343 8307844147680737999310515)
              ·
                refine ⟨12461766221521106998965773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8307844147680737999310515 12461766221521106998965773)
                ·
                  refine ⟨4673162333070415124612165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12461766221521106998965773 4673162333070415124612165)
                  ·
                    refine ⟨876217937450702835864781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4673162333070415124612165 876217937450702835864781)
                    ·
                      rfl

theorem cell23_5119285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_5119285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119285 prefixEnd_5119285 := by exact prefixLift 5119285
  have htrace : WordTrace (prefixWord ++ tailWord_5119285) baseStart_5119285 baseEnd_5119285 := by
    simpa [prefixWord, tailWord_5119285, baseEnd_5119285] using wordTrace_append hprefix tailTrace_5119285
  have hstable : (prefixWord ++ tailWord_5119285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119285).length < 2 ^ (prefixWord ++ tailWord_5119285).sum := by decide
  have hdescent : baseEnd_5119285 < baseStart_5119285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119336 : List Nat := [2, 1, 4, 2, 4, 1, 2, 2, 1, 4]
def baseStart_5119336 : Nat := 118140960795 + 5119336 * 2 ^ 59
def prefixEnd_5119336 : Nat := 4983230072969 + 3 ^ 40 * 5119336 * 2
def baseEnd_5119336 : Nat := 876226666621829269352203

theorem tailTrace_5119336 : CollatzResearch.WordTrace tailWord_5119336 prefixEnd_5119336 876226666621829269352203 := by
  unfold tailWord_5119336
  simp only [CollatzResearch.WordTrace]
  refine ⟨93358761690763729913148931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124478348921018306550865241 93358761690763729913148931)
  ·
    refine ⟨140038142536145594869723397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93358761690763729913148931 140038142536145594869723397)
    ·
      refine ⟨26257151725527299038073137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140038142536145594869723397 26257151725527299038073137)
      ·
        refine ⟨19692863794145474278554853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26257151725527299038073137 19692863794145474278554853)
        ·
          refine ⟨3692411961402276427229035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19692863794145474278554853 3692411961402276427229035)
          ·
            refine ⟨5538617942103414640843553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692411961402276427229035 5538617942103414640843553)
            ·
              refine ⟨4153963456577560980632665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5538617942103414640843553 4153963456577560980632665)
              ·
                refine ⟨3115472592433170735474499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4153963456577560980632665 3115472592433170735474499)
                ·
                  refine ⟨4673208888649756103211749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115472592433170735474499 4673208888649756103211749)
                  ·
                    refine ⟨876226666621829269352203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4673208888649756103211749 876226666621829269352203)
                    ·
                      rfl

theorem cell23_5119336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_5119336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119336 prefixEnd_5119336 := by exact prefixLift 5119336
  have htrace : WordTrace (prefixWord ++ tailWord_5119336) baseStart_5119336 baseEnd_5119336 := by
    simpa [prefixWord, tailWord_5119336, baseEnd_5119336] using wordTrace_append hprefix tailTrace_5119336
  have hstable : (prefixWord ++ tailWord_5119336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119336).length < 2 ^ (prefixWord ++ tailWord_5119336).sum := by decide
  have hdescent : baseEnd_5119336 < baseStart_5119336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119351 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_5119351 : Nat := 118140960795 + 5119351 * 2 ^ 59
def prefixEnd_5119351 : Nat := 4983230072969 + 3 ^ 40 * 5119351 * 2
def baseEnd_5119351 : Nat := 2628687702075305249369039

theorem tailTrace_5119351 : CollatzResearch.WordTrace tailWord_5119351 prefixEnd_5119351 2628687702075305249369039 := by
  unfold tailWord_5119351
  simp only [CollatzResearch.WordTrace]
  refine ⟨186718070476473117388093907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124478713650982078258729271 186718070476473117388093907)
  ·
    refine ⟨280077105714709676082140861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186718070476473117388093907 280077105714709676082140861)
    ·
      refine ⟨105028914643016128530802823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 280077105714709676082140861 105028914643016128530802823)
      ·
        refine ⟨157543371964524192796204235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105028914643016128530802823 157543371964524192796204235)
        ·
          refine ⟨236315057946786289194306353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157543371964524192796204235 236315057946786289194306353)
          ·
            refine ⟨177236293460089716895729765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236315057946786289194306353 177236293460089716895729765)
            ·
              refine ⟨33231805023766821917949331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 177236293460089716895729765 33231805023766821917949331)
              ·
                refine ⟨49847707535650232876923997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33231805023766821917949331 49847707535650232876923997)
                ·
                  refine ⟨18692890325868837328846499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49847707535650232876923997 18692890325868837328846499)
                  ·
                    refine ⟨28039335488803255993269749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18692890325868837328846499 28039335488803255993269749)
                    ·
                      refine ⟨2628687702075305249369039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28039335488803255993269749 2628687702075305249369039)
                      ·
                        rfl

theorem cell23_5119351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_5119351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119351 prefixEnd_5119351 := by exact prefixLift 5119351
  have htrace : WordTrace (prefixWord ++ tailWord_5119351) baseStart_5119351 baseEnd_5119351 := by
    simpa [prefixWord, tailWord_5119351, baseEnd_5119351] using wordTrace_append hprefix tailTrace_5119351
  have hstable : (prefixWord ++ tailWord_5119351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119351).length < 2 ^ (prefixWord ++ tailWord_5119351).sum := by decide
  have hdescent : baseEnd_5119351 < baseStart_5119351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119365 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 5, 2, 2]
def baseStart_5119365 : Nat := 118140960795 + 5119365 * 2 ^ 59
def prefixEnd_5119365 : Nat := 4983230072969 + 3 ^ 40 * 5119365 * 2
def baseEnd_5119365 : Nat := 2628694890804468194593975

theorem tailTrace_5119365 : CollatzResearch.WordTrace tailWord_5119365 prefixEnd_5119365 2628694890804468194593975 := by
  unfold tailWord_5119365
  simp only [CollatzResearch.WordTrace]
  refine ⟨186718581098422397779103549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124479054065614931852735699 186718581098422397779103549)
  ·
    refine ⟨70019467911908399167163831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186718581098422397779103549 70019467911908399167163831)
    ·
      refine ⟨105029201867862598750745747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70019467911908399167163831 105029201867862598750745747)
      ·
        refine ⟨157543802801793898126118621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105029201867862598750745747 157543802801793898126118621)
        ·
          refine ⟨59078926050672711797294483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157543802801793898126118621 59078926050672711797294483)
          ·
            refine ⟨88618389076009067695941725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59078926050672711797294483 88618389076009067695941725)
            ·
              refine ⟨33231895903503400385978147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88618389076009067695941725 33231895903503400385978147)
              ·
                refine ⟨49847843855255100578967221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33231895903503400385978147 49847843855255100578967221)
                ·
                  refine ⟨4673235361430165679278177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49847843855255100578967221 4673235361430165679278177)
                  ·
                    refine ⟨3504926521072624259458633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4673235361430165679278177 3504926521072624259458633)
                    ·
                      refine ⟨2628694890804468194593975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504926521072624259458633 2628694890804468194593975)
                      ·
                        rfl

theorem cell23_5119365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 2, 2].length) (baseStart_5119365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119365 prefixEnd_5119365 := by exact prefixLift 5119365
  have htrace : WordTrace (prefixWord ++ tailWord_5119365) baseStart_5119365 baseEnd_5119365 := by
    simpa [prefixWord, tailWord_5119365, baseEnd_5119365] using wordTrace_append hprefix tailTrace_5119365
  have hstable : (prefixWord ++ tailWord_5119365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119365).length < 2 ^ (prefixWord ++ tailWord_5119365).sum := by decide
  have hdescent : baseEnd_5119365 < baseStart_5119365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119369 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 2, 3, 2]
def baseStart_5119369 : Nat := 118140960795 + 5119369 * 2 ^ 59
def prefixEnd_5119369 : Nat := 4983230072969 + 3 ^ 40 * 5119369 * 2
def baseEnd_5119369 : Nat := 2628696944727086178943957

theorem tailTrace_5119369 : CollatzResearch.WordTrace tailWord_5119369 prefixEnd_5119369 2628696944727086178943957 := by
  unfold tailWord_5119369
  simp only [CollatzResearch.WordTrace]
  refine ⟨186718726990407906462249161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124479151326938604308166107 186718726990407906462249161)
  ·
    refine ⟨140039045242805929846686871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186718726990407906462249161 140039045242805929846686871)
    ·
      refine ⟨210058567864208894770030307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140039045242805929846686871 210058567864208894770030307)
      ·
        refine ⟨315087851796313342155045461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210058567864208894770030307 315087851796313342155045461)
        ·
          refine ⟨3692435763238046978379439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 315087851796313342155045461 3692435763238046978379439)
          ·
            refine ⟨5538653644857070467569159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3692435763238046978379439 5538653644857070467569159)
            ·
              refine ⟨8307980467285605701353739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5538653644857070467569159 8307980467285605701353739)
              ·
                refine ⟨12461970700928408552030609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8307980467285605701353739 12461970700928408552030609)
                ·
                  refine ⟨9346478025696306414022957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12461970700928408552030609 9346478025696306414022957)
                  ·
                    refine ⟨3504929259636114905258609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9346478025696306414022957 3504929259636114905258609)
                    ·
                      refine ⟨2628696944727086178943957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504929259636114905258609 2628696944727086178943957)
                      ·
                        rfl

theorem cell23_5119369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 2, 3, 2].length) (baseStart_5119369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119369 prefixEnd_5119369 := by exact prefixLift 5119369
  have htrace : WordTrace (prefixWord ++ tailWord_5119369) baseStart_5119369 baseEnd_5119369 := by
    simpa [prefixWord, tailWord_5119369, baseEnd_5119369] using wordTrace_append hprefix tailTrace_5119369
  have hstable : (prefixWord ++ tailWord_5119369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119369).length < 2 ^ (prefixWord ++ tailWord_5119369).sum := by decide
  have hdescent : baseEnd_5119369 < baseStart_5119369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119385 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 1, 2, 3]
def baseStart_5119385 : Nat := 118140960795 + 5119385 * 2 ^ 59
def prefixEnd_5119385 : Nat := 4983230072969 + 3 ^ 40 * 5119385 * 2
def baseEnd_5119385 : Nat := 2628705160417558116343883

theorem tailTrace_5119385 : CollatzResearch.WordTrace tailWord_5119385 prefixEnd_5119385 2628705160417558116343883 := by
  unfold tailWord_5119385
  simp only [CollatzResearch.WordTrace]
  refine ⟨186719310558349941194831609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124479540372233294129887739 186719310558349941194831609)
  ·
    refine ⟨140039482918762455896123707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186719310558349941194831609 140039482918762455896123707)
    ·
      refine ⟨210059224378143683844185561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140039482918762455896123707 210059224378143683844185561)
      ·
        refine ⟨157544418283607762883139171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210059224378143683844185561 157544418283607762883139171)
        ·
          refine ⟨236316627425411644324708757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157544418283607762883139171 236316627425411644324708757)
          ·
            refine ⟨11077341910566170827720723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 236316627425411644324708757 11077341910566170827720723)
            ·
              refine ⟨16616012865849256241581085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11077341910566170827720723 16616012865849256241581085)
              ·
                refine ⟨6231004824693471090592907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16616012865849256241581085 6231004824693471090592907)
                ·
                  refine ⟨9346507237040206635889361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6231004824693471090592907 9346507237040206635889361)
                  ·
                    refine ⟨7009880427780154976917021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9346507237040206635889361 7009880427780154976917021)
                    ·
                      refine ⟨2628705160417558116343883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7009880427780154976917021 2628705160417558116343883)
                      ·
                        rfl

theorem cell23_5119385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_5119385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119385 prefixEnd_5119385 := by exact prefixLift 5119385
  have htrace : WordTrace (prefixWord ++ tailWord_5119385) baseStart_5119385 baseEnd_5119385 := by
    simpa [prefixWord, tailWord_5119385, baseEnd_5119385] using wordTrace_append hprefix tailTrace_5119385
  have hstable : (prefixWord ++ tailWord_5119385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119385).length < 2 ^ (prefixWord ++ tailWord_5119385).sum := by decide
  have hdescent : baseEnd_5119385 < baseStart_5119385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5119399 : List Nat := [1, 1, 6, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_5119399 : Nat := 118140960795 + 5119399 * 2 ^ 59
def prefixEnd_5119399 : Nat := 4983230072969 + 3 ^ 40 * 5119399 * 2
def baseEnd_5119399 : Nat := 2628712349146721061568819

theorem tailTrace_5119399 : CollatzResearch.WordTrace tailWord_5119399 prefixEnd_5119399 2628712349146721061568819 := by
  unfold tailWord_5119399
  simp only [CollatzResearch.WordTrace]
  refine ⟨186719821180299221585841251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124479880786866147723894167 186719821180299221585841251)
  ·
    refine ⟨280079731770448832378761877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186719821180299221585841251 280079731770448832378761877)
    ·
      refine ⟨13128737426739789017754463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 280079731770448832378761877 13128737426739789017754463)
      ·
        refine ⟨19693106140109683526631695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13128737426739789017754463 19693106140109683526631695)
        ·
          refine ⟨29539659210164525289947543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19693106140109683526631695 29539659210164525289947543)
          ·
            refine ⟨44309488815246787934921315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29539659210164525289947543 44309488815246787934921315)
            ·
              refine ⟨66464233222870181902381973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44309488815246787934921315 66464233222870181902381973)
              ·
                refine ⟨3115510932322039776674155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66464233222870181902381973 3115510932322039776674155)
                ·
                  refine ⟨4673266398483059665011233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3115510932322039776674155 4673266398483059665011233)
                  ·
                    refine ⟨3504949798862294748758425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4673266398483059665011233 3504949798862294748758425)
                    ·
                      refine ⟨2628712349146721061568819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3504949798862294748758425 2628712349146721061568819)
                      ·
                        rfl

theorem cell23_5119399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_5119399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5119399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5119399 prefixEnd_5119399 := by exact prefixLift 5119399
  have htrace : WordTrace (prefixWord ++ tailWord_5119399) baseStart_5119399 baseEnd_5119399 := by
    simpa [prefixWord, tailWord_5119399, baseEnd_5119399] using wordTrace_append hprefix tailTrace_5119399
  have hstable : (prefixWord ++ tailWord_5119399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5119399).length < 2 ^ (prefixWord ++ tailWord_5119399).sum := by decide
  have hdescent : baseEnd_5119399 < baseStart_5119399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5119399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
